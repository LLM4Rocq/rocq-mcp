"""Module M. verification template, Print Assumptions parsing, axiom whitelist."""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum, auto

# ---------------------------------------------------------------------------
# Definition categories and problem structure
# ---------------------------------------------------------------------------


class DefCategory(Enum):
    """Classification of Rocq vernacular commands for template placement."""

    PREAMBLE = auto()  # Require, Import, Open Scope
    SHARED_DEF = auto()  # Inductive, Record, Definition, Fixpoint, etc.
    THEOREM = auto()  # Theorem, Lemma, Proposition, etc.
    NOTATION = auto()  # Notation, Infix
    OTHER = auto()  # Section, Variable, etc.


@dataclass
class DefinitionInfo:
    """A single extracted definition from the problem statement."""

    name: str | None
    detail: str  # Rocq keyword from toc: "Inductive", "Definition", etc.
    category: DefCategory
    source_text: str
    start_line: int  # 0-based
    end_line: int  # 0-based


@dataclass
class ProblemStructure:
    """Parsed structure of a Rocq problem statement."""

    preamble_source: str  # Imports/Open Scope before definitions
    definitions: list[DefinitionInfo]  # Shared defs (Inductive, Record, etc.)
    theorem_source: str  # The theorem statement
    theorem_name: str | None
    has_shared_defs: bool  # True if any Inductive/Record/Def present
    full_source: str  # Original complete source


# Detail strings from coq-lsp toc that should be shared outside Module M
_SHARED_DEF_DETAILS: set[str] = {
    "Inductive",
    "CoInductive",
    "Variant",
    "Record",
    "Structure",
    "Class",
    "Definition",
    "Fixpoint",
    "CoFixpoint",
    "Function",
    "Canonical",
    "Coercion",
    "Instance",
}

_THEOREM_DETAILS: set[str] = {
    "Theorem",
    "Lemma",
    "Proposition",
    "Corollary",
    "Example",
    "Fact",
    "Remark",
}

_NOTATION_DETAILS: set[str] = {
    "Notation",
    "Infix",
}


def classify_toc_detail(detail: str) -> DefCategory:
    """Classify a coq-lsp toc detail string into a DefCategory."""
    if detail in _SHARED_DEF_DETAILS:
        return DefCategory.SHARED_DEF
    if detail in _THEOREM_DETAILS:
        return DefCategory.THEOREM
    if detail in _NOTATION_DETAILS:
        return DefCategory.NOTATION
    return DefCategory.OTHER


# Regex alternation of definition keywords (longest first for correct matching)
_DEF_KEYWORDS_RE_STR = "|".join(
    re.escape(k) for k in sorted(_SHARED_DEF_DETAILS, key=len, reverse=True)
)


def _neutralize_for_regex(text: str) -> str:
    """Replace comment and string interiors with spaces, preserving text length.

    Comment delimiters ``(* ... *)`` and their contents become spaces.
    String interiors (between ``"..."``) become spaces but the quote
    delimiters are preserved outside comments.  This lets regex patterns
    match on the neutralized text with spans that map 1:1 back to the
    original.
    """
    result = list(text)
    depth = 0
    in_str = False
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if in_str:
            if ch == '"':
                if i + 1 < n and text[i + 1] == '"':
                    # Escaped quote inside string — blank both
                    result[i] = " "
                    result[i + 1] = " "
                    i += 2
                    continue
                # Closing quote
                in_str = False
                if depth > 0:
                    result[i] = " "
            else:
                result[i] = " "
        elif depth > 0:
            if ch == '"':
                in_str = True
                result[i] = " "
            elif ch == "(" and i + 1 < n and text[i + 1] == "*":
                depth += 1
                result[i] = " "
                result[i + 1] = " "
                i += 2
                continue
            elif ch == "*" and i + 1 < n and text[i + 1] == ")":
                depth -= 1
                result[i] = " "
                result[i + 1] = " "
                i += 2
                continue
            else:
                result[i] = " "
        else:
            if ch == '"':
                in_str = True
            elif ch == "(" and i + 1 < n and text[i + 1] == "*":
                depth += 1
                result[i] = " "
                result[i + 1] = " "
                i += 2
                continue
        i += 1
    return "".join(result)


def _strip_shared_defs(proof: str, shared_names: set[str]) -> str:
    """Remove definition blocks from proof whose names match shared_names.

    For each name in shared_names, finds and removes the Rocq vernacular
    sentence that defines it (from the keyword to the sentence-terminating
    period).  This prevents type shadowing when the same definitions are
    placed outside Module M in the shared-defs template.

    The sentence terminator is a period followed by whitespace or end of
    string, matching Rocq's lexical convention.  Dots inside qualified
    names (e.g., ``Nat.add``) are not followed by whitespace and are
    correctly skipped.

    Comments and strings are neutralized (replaced with spaces) before
    regex matching so that definition keywords and dots inside them
    do not confuse the sentence boundary detection.  Match spans are
    mapped back to the original text, preserving comments in the output.
    """
    if not shared_names:
        return proof
    # Neutralize comments and strings for safe regex matching.
    # The neutralized text has the same length as the original,
    # so match spans map directly back.
    neutralized = _neutralize_for_regex(proof)
    # Collect all spans to remove (from ALL names).
    spans: list[tuple[int, int]] = []
    for name in sorted(shared_names):  # sorted for determinism
        if not name:
            continue
        # Match: optional leading whitespace + definition keyword + name
        # + everything up to the sentence-terminating period (. followed
        # by whitespace or end of string).  MULTILINE so ^ matches line
        # starts; DOTALL so .* crosses newlines.
        pattern = (
            rf"(?ms)^[ \t]*(?:{_DEF_KEYWORDS_RE_STR})\s+{re.escape(name)}\b"
            rf".*?\.(?=\s|$)[ \t]*\n?"
        )
        # Find ALL occurrences (not just first). Using only the first match
        # would allow an adversary to hide a decoy definition to protect
        # their real redefinition from stripping.
        for m in re.finditer(pattern, neutralized):
            spans.append((m.start(), m.end()))
    # Merge overlapping/contained spans to avoid corruption when a
    # definition body textually contains another definition pattern.
    spans.sort()
    merged: list[tuple[int, int]] = []
    for start, end in spans:
        if merged and start <= merged[-1][1]:
            # Overlapping or contained — extend the previous span.
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    # Apply in reverse order so removals don't shift earlier offsets.
    result = proof
    for start, end in reversed(merged):
        result = result[:start] + result[end:]
    return result


# ---------------------------------------------------------------------------
# Forbidden command check
# ---------------------------------------------------------------------------

_FORBIDDEN_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (
        re.compile(r"\bRedirect\b"),
        "Forbidden command 'Redirect' (writes Rocq output to arbitrary files)",
    ),
    (
        re.compile(r'\bExtraction\s+"'),
        "Forbidden command 'Extraction \"...\"' (extracts code to files)",
    ),
    (
        re.compile(r"\bDrop\b"),
        "Forbidden command 'Drop' (escapes to OCaml toplevel)",
    ),
    (
        re.compile(r"\bSeparate\s+Extraction\b"),
        "Forbidden command 'Separate Extraction' (writes .ml/.mli files)",
    ),
    (
        re.compile(r"\bRecursive\s+Extraction\b"),
        "Forbidden command 'Recursive Extraction' (writes .ml files)",
    ),
    (
        re.compile(r"\bCd\b"),
        "Forbidden command 'Cd' (changes working directory)",
    ),
    (
        re.compile(r"\bLoad\b"),
        "Forbidden command 'Load' (loads and executes external .v files)",
    ),
    (
        re.compile(r"\bExtraction\s+Library\b"),
        "Forbidden command 'Extraction Library' (writes .ml files)",
    ),
    (
        re.compile(r"\bDeclare\s+ML\s+Module\b"),
        "Forbidden command 'Declare ML Module' (loads arbitrary OCaml plugins)",
    ),
    (
        re.compile(r"\bUnset\s+Guard\s+Checking\b"),
        "Forbidden command 'Unset Guard Checking' (disables termination checker)",
    ),
    (
        re.compile(r"\bUnset\s+Positivity\s+Checking\b"),
        "Forbidden command 'Unset Positivity Checking' (disables positivity checker)",
    ),
    (
        re.compile(r"\bUnset\s+Universe\s+Checking\b"),
        "Forbidden command 'Unset Universe Checking' (disables universe checker)",
    ),
    (
        re.compile(r"\bbypass_check\b"),
        "Forbidden attribute 'bypass_check' (bypasses kernel safety checks)",
    ),
    (
        re.compile(r"\bEnd\s+M\b\s*\."),
        "Forbidden command 'End M.' (attempt to escape Module M sandbox)",
    ),
    (
        re.compile(r"\bReset\b"),
        "Forbidden command 'Reset' (resets global environment)",
    ),
    (
        re.compile(r"\bBack\b"),
        "Forbidden command 'Back' (undoes vernacular commands)",
    ),
    (
        re.compile(r"\bUndo\b"),
        "Forbidden command 'Undo' (undoes proof steps)",
    ),
    (
        re.compile(r"\bAdd\s+(Rec\s+)?LoadPath\b"),
        "Forbidden command 'Add LoadPath' (loads .vo from arbitrary directories)",
    ),
    (
        re.compile(r"\bAdd\s+ML\s+Path\b"),
        "Forbidden command 'Add ML Path' (extends OCaml plugin search path)",
    ),
    (
        re.compile(r'\bPrint\s+(?:Sorted\s+)?Universes\s+"'),
        "Forbidden: 'Print [Sorted] Universes \"...\"' writes files",
    ),
    (
        re.compile(r"\bExtraction\s+TestCompile\b"),
        "Forbidden: 'Extraction TestCompile' invokes external compiler",
    ),
    (
        re.compile(r"\bExtraction\s+Output\s+Directory\b"),
        "Forbidden: 'Extraction Output Directory' directs extraction writes to arbitrary paths",
    ),
]


def _rocq_scan(text: str):
    """Yield ``(index, char, in_comment, in_string)`` for each character.

    Single-pass scanner that tracks ``(* ... *)`` comment nesting (arbitrary
    depth) and ``"..."`` string literals (with ``""`` escape).  Rocq's lexer
    tracks string literals inside comments (so ``*)`` inside a quoted string
    within a comment does NOT close the comment), and this scanner matches
    that behavior.

    Two-character tokens (``(*``, ``*)``, ``""``) are yielded as one event at
    the position of their first character; the second character is skipped.
    """
    depth = 0
    in_str = False
    i = 0
    length = len(text)
    while i < length:
        ch = text[i]
        if in_str:
            if ch == '"':
                if i + 1 < length and text[i + 1] == '"':
                    yield i, ch, depth > 0, True
                    i += 2
                    continue
                in_str = False
            yield i, ch, depth > 0, True
        elif depth > 0:
            if ch == '"':
                in_str = True
                yield i, ch, True, True
            elif ch == "*" and i + 1 < length and text[i + 1] == ")":
                depth -= 1
                yield i, ch, True, False  # closing *) – still part of comment
                i += 2
                continue
            elif ch == "(" and i + 1 < length and text[i + 1] == "*":
                depth += 1
                yield i, ch, True, False
                i += 2
                continue
            else:
                yield i, ch, True, False
        else:
            if ch == '"':
                in_str = True
                yield i, ch, False, True
            elif ch == "(" and i + 1 < length and text[i + 1] == "*":
                depth += 1
                yield i, ch, True, False
                i += 2
                continue
            else:
                yield i, ch, False, False
        i += 1


def _strip_rocq_comments(text: str) -> str:
    """Remove ``(* ... *)`` comments from *text*, replacing each with a space.

    Uses :func:`_rocq_scan` to ensure comment/string tracking exactly matches
    Rocq's lexer (including string literals inside comments).
    """
    result: list[str] = []
    was_in_comment = False
    for _idx, ch, in_comment, _in_str in _rocq_scan(text):
        if not in_comment:
            if was_in_comment:
                result.append(" ")  # replace closing comment with space
            result.append(ch)
        elif not was_in_comment:
            result.append(" ")  # replace opening comment with space
        was_in_comment = in_comment
    return "".join(result)


def _strip_rocq_strings(text: str) -> str:
    """Replace the contents of string literals with spaces.

    Preserves string delimiters but blanks interior characters so that
    forbidden-command patterns do not match inside strings.
    """
    result: list[str] = []
    for _idx, ch, _in_comment, in_str in _rocq_scan(text):
        if in_str and ch != '"':
            result.append(" ")
        else:
            result.append(ch)
    return "".join(result)


def _check_forbidden_commands(source: str) -> str | None:
    """Check for dangerous Rocq commands in the source text.

    Uses :func:`_neutralize_for_regex` to blank comment and string
    interiors in a single pass, avoiding desync issues that can occur
    with separate strip-comments / strip-strings passes (e.g. ``""``
    escape sequences shifting quote boundaries between passes).

    Returns an error message string if a forbidden command is found,
    or None if the source is clean.
    """
    stripped = _neutralize_for_regex(source)
    for pattern, message in _FORBIDDEN_PATTERNS:
        if re.search(pattern, stripped):
            return message
    return None


# ---------------------------------------------------------------------------
# Module M. template
# ---------------------------------------------------------------------------

# Note: we use f-string construction (not str.format) to avoid any issues
# with Rocq braces { } in proof text.


def build_verification_source(
    proof: str,
    problem_name: str,
    problem_statement: str,
) -> str:
    """Build the Module M. verification source.

    The template:
    1. Wraps the entire proof (including imports) in Module M. ... End M.
    2. Places the cleaned problem statement (with its own imports) outside
    3. Applies M.theorem_name to prove the original statement
    4. Runs Print Assumptions to check for axioms/admits

    Imports (Require/From) work inside modules in Rocq, so there is no need
    to split the preamble from the body.  This follows the same approach as
    the proof_checker reference implementation.
    """
    forbidden = _check_forbidden_commands(proof)
    if forbidden:
        raise ValueError(forbidden)

    forbidden = _check_forbidden_commands(problem_statement)
    if forbidden:
        raise ValueError(forbidden)

    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", problem_name):
        raise ValueError(
            f"problem_name must be a valid Rocq identifier. Got: {problem_name!r}"
        )

    clean_statement = _clean_problem_statement(problem_statement)

    return (
        f"Module M.\n"
        f"{proof}\n"
        f"End M.\n\n"
        # Reset printing flags that Module M may have changed, to ensure
        # Print Assumptions output matches our parser's expected format.
        f"Unset Printing All.\n"
        f"Unset Printing Universes.\n"
        f"Set Printing Width 120.\n"
        f"Set Printing Depth 1000000.\n\n"
        f"{clean_statement}\n"
        f"Proof.\n"
        f"exact M.{problem_name} || apply M.{problem_name} || eapply M.{problem_name}.\n"
        f"all: first [ eassumption | assumption | reflexivity | congruence | auto | easy | simpl; auto ].\n"
        f"Qed.\n\n"
        f"Print Assumptions {problem_name}.\n"
    )


def _clean_problem_statement(problem_statement: str) -> str:
    """Strip trailing Admitted./Abort./admit./give_up. from the problem statement.

    Only strips at end of text (not in the middle). Handles optional
    whitespace before the dot.
    """
    result = re.sub(
        r"\s*(Admitted|Abort|admit|give_up)\s*\.\s*$",
        "",
        problem_statement,
    )
    result = re.sub(r"\s*Proof\s*(?:(?:using|with)\b.*)?\.\s*$", "", result)
    return result.strip()


# ---------------------------------------------------------------------------
# Shared-definitions verification template
# ---------------------------------------------------------------------------


def build_shared_defs_verification_source(
    proof: str,
    problem_name: str,
    structure: ProblemStructure,
) -> str:
    """Build verification source with shared definitions outside Module M.

    When the problem statement contains type definitions (Inductive, Record,
    Definition, etc.), placing them inside Module M causes type incompatibility
    across the module boundary.  This template places shared definitions
    *outside* Module M so the proof's types unify with the theorem's types.

    Template layout::

        <preamble: Require/Import/Open Scope>
        <shared definitions: Inductive, Record, Definition, etc.>
        Module M.
        <proof>
        End M.
        <theorem re-statement>
        Proof.
        exact M.<name> || apply M.<name> || eapply M.<name>.
        all: first [ assumption | reflexivity | congruence | auto | easy | simpl; auto ].
        Qed.
        Print Assumptions <name>.
    """
    forbidden = _check_forbidden_commands(proof)
    if forbidden:
        raise ValueError(forbidden)

    forbidden = _check_forbidden_commands(structure.full_source)
    if forbidden:
        raise ValueError(forbidden)

    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", problem_name):
        raise ValueError(
            f"problem_name must be a valid Rocq identifier. Got: {problem_name!r}"
        )

    clean_theorem = _clean_problem_statement(structure.theorem_source)

    # Collect shared definition source texts
    shared_defs_text = "\n".join(defn.source_text for defn in structure.definitions)

    # Collect names of shared definitions to strip from the proof.
    # Only SHARED_DEF items (Inductive, Record, Definition, etc.) cause
    # nominal type shadowing; Notations and OTHER are harmless if duplicated.
    shared_names = {
        defn.name
        for defn in structure.definitions
        if defn.name and defn.category == DefCategory.SHARED_DEF
    }

    # Strip the duplicate definitions from the proof so they don't
    # shadow the shared definitions placed outside Module M.
    stripped_proof = _strip_shared_defs(proof, shared_names)

    parts: list[str] = []

    # 1. Preamble (Require/Import/Open Scope)
    if structure.preamble_source.strip():
        parts.append(structure.preamble_source.strip())
        parts.append("")

    # 2. Shared definitions (Inductive, Record, Definition, etc.)
    if shared_defs_text.strip():
        parts.append(shared_defs_text.strip())
        parts.append("")

    # 3. Module M with the proof (definitions stripped)
    parts.append("Module M.")
    parts.append(stripped_proof)
    parts.append("End M.")
    parts.append("")

    # Reset printing flags that Module M may have changed, to ensure
    # Print Assumptions output matches our parser's expected format.
    parts.append("Unset Printing All.")
    parts.append("Unset Printing Universes.")
    parts.append("Set Printing Width 120.")
    parts.append("Set Printing Depth 1000000.")
    parts.append("")

    # 4. Theorem re-statement and apply
    parts.append(clean_theorem)
    parts.append("Proof.")
    parts.append(
        f"exact M.{problem_name} || apply M.{problem_name} || eapply M.{problem_name}."
    )
    parts.append(
        "all: first [ eassumption | assumption | reflexivity | congruence | auto | easy | simpl; auto ]."
    )
    parts.append("Qed.")
    parts.append("")

    # 5. Print Assumptions
    parts.append(f"Print Assumptions {problem_name}.")
    parts.append("")

    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Axiom whitelist
# ---------------------------------------------------------------------------

# Whitelist of known safe axioms by short name (last dot-separated component).
# Print Assumptions outputs axiom names in various forms:
#   - Unqualified: "classic"
#   - Fully qualified: "Coq.Logic.Classical_Prop.classic"
#   - Module-qualified (no stdlib prefix): "ClassicalDedekindReals.sig_forall_dec"
# We match on short name AND verify the qualified prefix is safe.

_KNOWN_SAFE_AXIOMS: set[str] = {
    # --- Classical logic ---
    "classic",  # forall P : Prop, P \/ ~ P
    # --- Extensionality ---
    "functional_extensionality_dep",  # (forall x, f x = g x) -> f = g
    "propositional_extensionality",  # (P <-> Q) -> P = Q
    "proof_irrelevance",  # forall (p1 p2 : P), p1 = p2
    "JMeq_eq",  # JMeq x y -> x = y
    "eq_rect_eq",  # UIP / Streicher's K
    # --- Choice and descriptions ---
    "constructive_indefinite_description",  # sig form of indefinite choice
    "constructive_definite_description",  # sig form of definite description
    "dependent_unique_choice",
    "unique_choice",
    "relational_choice",
    "epsilon",  # Hilbert epsilon
    "epsilon_spec",
    # --- Reals axiomatization (Coq.Reals.Raxioms) ---
    "R",
    "R0",
    "R1",
    "Rplus",
    "Rmult",
    "Ropp",
    "Rinv",
    "Rlt",
    "up",
    "R1_neq_R0",
    "Rplus_comm",
    "Rplus_assoc",
    "Rplus_opp_r",
    "Rplus_0_l",
    "Rmult_comm",
    "Rmult_assoc",
    "Rmult_1_l",
    "Rmult_plus_distr_l",
    "Rinv_l",
    "Rlt_asym",
    "Rlt_trans",
    "Rplus_lt_compat_l",
    "Rmult_lt_compat_l",
    "archimed",
    "completeness",
    "total_order_T",
    # --- Dedekind reals (ClassicalDedekindReals) ---
    "sig_forall_dec",
    "sig_not_dec",  # forall P : Prop, {~ ~ P} + {~ P}
    # --- Sets (Ensembles) ---
    "Extensionality_Ensembles",  # forall U (A B : Ensemble U), Same_set U A B -> A = B
    # --- Primitive 63-bit integers (PrimInt63 / Uint63Axioms) ---
    "int",  # Set (primitive type)
    "add",  # int -> int -> int
    "sub",  # int -> int -> int
    "mul",  # int -> int -> int
    "div",  # int -> int -> int
    "mod",  # int -> int -> int
    "eqb",  # int -> int -> bool (also float -> float -> bool)
    "ltb",  # int -> int -> bool (also float -> float -> bool)
    "leb",  # int -> int -> bool (also float -> float -> bool)
    "land",  # int -> int -> int
    "lor",  # int -> int -> int
    "lxor",  # int -> int -> int
    "lsl",  # int -> int -> int
    "lsr",  # int -> int -> int
    "asr",  # int -> int -> int
    "head0",  # int -> int
    "tail0",  # int -> int
    "compare",  # int -> int -> comparison (also string -> string -> comparison)
    "add_spec",  # forall x y, φ(x+y) = ((φx + φy) mod wB)%Z
    "sub_spec",  # forall x y, φ(x-y) = ((φx - φy) mod wB)%Z
    "mul_spec",  # forall x y, φ(x*y) = ((φx * φy) mod wB)%Z
    "div_spec",  # forall x y, φ(x/y) = (φx / φy)%Z
    "mod_spec",  # forall x y, φ(x mod y) = (φx mod φy)%Z
    "eqb_correct",  # forall i j, (i =? j) = true -> i = j
    "eqb_refl",  # forall x, (x =? x) = true
    "of_to_Z",  # forall x, of_Z (φ x) = x
    # --- Primitive floats (PrimFloat) ---
    "float",  # Set (primitive type)
    "sqrt",  # float -> float
    "abs",  # float -> float
    "classify",  # float -> float_class
    "normfr_mantissa",  # float -> int
    "frshiftexp",  # float -> float * int
    "ldshiftexp",  # float -> int -> float
    "next_up",  # float -> float
    "next_down",  # float -> float
    "opp",  # float -> float
    # --- Primitive arrays (PrimArray) ---
    "array",  # Type -> Type
    "get",  # forall A, array A -> int -> A
    "set",  # forall A, array A -> int -> A -> array A
    "make",  # forall A, int -> A -> array A
    "length",  # forall A, array A -> int (also string -> int)
    "copy",  # forall A, array A -> array A
    # --- Primitive strings (PrimString) ---
    "string",  # Set (primitive type)
    "cat",  # string -> string -> string
}

# Standard library module prefixes. Axioms qualified with these are safe.
_STDLIB_PREFIXES: tuple[str, ...] = ("Coq.", "Rocq.", "Stdlib.", "Corelib.")

# Known stdlib module names that Print Assumptions outputs WITHOUT the full
# Stdlib./Coq./Corelib. prefix. E.g., "ClassicalDedekindReals.sig_forall_dec"
# instead of "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec".
_STDLIB_MODULE_PREFIXES: tuple[str, ...] = (
    "ClassicalDedekindReals.",  # Dedekind reals axioms
    "FunctionalExtensionality.",  # functional extensionality
    "Eqdep.Eq_rect_eq.",  # eq_rect_eq / UIP (via JMeq)
    "Eq_rect_eq.",  # eq_rect_eq / UIP (via Eqdep directly)
    "Classical_Prop.",  # classic, proof_irrelevance
    "ClassicalEpsilon.",  # constructive_indefinite_description, epsilon
    "ClassicalUniqueChoice.",  # dependent_unique_choice, unique_choice
    "ClassicalDescription.",  # constructive_definite_description
    "RelationalChoice.",  # relational_choice
    "PropExtensionality.",  # propositional_extensionality
    "Raxioms.",  # R, Rplus, Rmult, etc.
    "Ensembles.",  # Extensionality_Ensembles
    # Primitive types and operations (kernel-level axioms)
    "PrimInt63.",  # int, add, sub, mul, div, mod, eqb, ltb, leb, ...
    "Uint63Axioms.",  # add_spec, sub_spec, ..., eqb_correct, eqb_refl, of_to_Z
    "PrimFloat.",  # float, add, sub, mul, div, sqrt, eqb, ltb, leb, ...
    "PrimArray.",  # array, get, set, make, length, copy
    "PrimString.",  # string, cat, length, compare
    "FloatOps.",  # float operation specs
    "FloatAxioms.",  # float axiom specs
)


# Protected module names — first component of each _STDLIB_MODULE_PREFIXES entry,
# top-level stdlib namespace prefixes (Coq, Rocq, Stdlib, Corelib), and commonly
# used stdlib module names whose functions appear in Check/Print Assumptions output.
# Proofs in Phase 3 (no Module M) must not define modules with these names,
# as that would allow spoofing axiom qualifications to bypass the whitelist.
_PROTECTED_MODULE_NAMES: set[str] = (
    {prefix.split(".")[0] for prefix in _STDLIB_MODULE_PREFIXES}
    | {prefix.rstrip(".") for prefix in _STDLIB_PREFIXES}
    | {
        # Common stdlib modules whose names appear in qualified references.
        # Shadowing these would let a proof redefine stdlib functions.
        "Nat",
        "Z",
        "N",
        "Q",
        "R",
        "List",
        "Bool",
        "String",
        "Datatypes",
        "BinNums",
        "BinInt",
        "BinNat",
        "BinPos",
        "PeanoNat",
        "ZArith",
        "Arith",
        "Logic",
        "Init",
        "Numbers",
        "Reals",
        "Sets",
        "Vectors",
        "Sorting",
        "Wellfounded",
    }
)


def _axiom_short_name(qualified_name: str) -> str:
    """Extract short name: 'Coq.Logic.Classical_Prop.classic' -> 'classic'."""
    return qualified_name.rsplit(".", 1)[-1]


# Axiom short names that are too generic to accept unqualified in Phase 3.
# These names commonly appear as user-defined functions, so unqualified
# appearances in Print Assumptions must have stdlib qualification to be
# trusted.  Unique stdlib names (classic, Rplus_comm, etc.) are safe
# unqualified because they are unlikely to be user-defined.
_AMBIGUOUS_AXIOM_NAMES: set[str] = {
    # Primitive types (very common names)
    "int",
    "float",
    "array",
    "string",
    # Arithmetic operations
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    # Comparison operations
    "eqb",
    "ltb",
    "leb",
    "compare",
    # Bit operations
    "land",
    "lor",
    "lxor",
    "lsl",
    "lsr",
    "asr",
    # Utility functions
    "head0",
    "tail0",
    # Math functions
    "sqrt",
    "abs",
    "classify",
    "opp",
    # Container operations
    "get",
    "set",
    "make",
    "length",
    "copy",
    "cat",
    # Reals — single-letter or generic names that could be user-defined
    "R",
    "R0",
    "R1",
    "completeness",
    # Other generic names
    "epsilon",
    "up",
}


def _is_standard_axiom(name: str, *, require_qualified: bool = False) -> bool:
    """Check if an axiom name refers to a known standard library axiom.

    For qualified names (containing dots): the prefix must be from a known
    stdlib module AND the short name must be in the whitelist.

    For unqualified names: accepted when *require_qualified* is False
    (Phase 1/2 where Module M gives user axioms an ``M.`` prefix).
    When *require_qualified* is True (Phase 3), only *ambiguous* short
    names (``add``, ``sub``, ``compare``, etc.) are rejected.  Unique
    stdlib names (``classic``, ``functional_extensionality_dep``) are
    accepted unqualified even in Phase 3.

    This prevents spoofing: a user-defined 'M.classic : False' has prefix 'M.'
    which is NOT a stdlib prefix, so it is rejected even though short name
    'classic' is in the whitelist.

    Print Assumptions outputs axiom names in various forms:
      - "classic" (unqualified)
      - "Coq.Logic.Classical_Prop.classic" (fully qualified with stdlib prefix)
      - "ClassicalDedekindReals.sig_forall_dec" (module-qualified, no stdlib prefix)
    All three forms are handled.
    """
    short = _axiom_short_name(name)
    if short not in _KNOWN_SAFE_AXIOMS:
        return False
    if "." not in name:
        # In Phase 3 (no Module M), generic names (add, sub, compare, ...)
        # could be user-defined and must be qualified.  Unique stdlib names
        # (classic, functional_extensionality_dep) are safe unqualified.
        if require_qualified and name in _AMBIGUOUS_AXIOM_NAMES:
            return False
        return True
    # Qualified: must come from stdlib (full prefix or known module name)
    if any(name.startswith(prefix) for prefix in _STDLIB_PREFIXES):
        return True
    return any(name.startswith(prefix) for prefix in _STDLIB_MODULE_PREFIXES)


def _check_module_name_shadowing(proof: str) -> str | None:
    """Reject proofs that define Modules with names matching stdlib module names.

    This prevents a proof from creating e.g. ``Module ClassicalDedekindReals``
    to spoof axiom qualifications that bypass the axiom whitelist.

    Handles variants:
    - ``Module Nat.`` (plain module)
    - ``Module Import Nat.`` (module with immediate import)
    - ``Module Export Nat.`` (module with immediate export)
    - ``Module Type Nat.`` (module type — also caught as defense-in-depth)

    Returns an error message if a protected module name is shadowed, or None.
    """
    neutralized = _neutralize_for_regex(proof)
    for mod_name in sorted(_PROTECTED_MODULE_NAMES):
        # Match: Module [Type|Import|Export] <name>
        pattern = rf"\bModule\s+(?:(?:Type|Import|Export)\s+)?{re.escape(mod_name)}\b"
        if re.search(pattern, neutralized):
            return (
                f"Proof defines Module '{mod_name}' which shadows a "
                f"standard library module name"
            )
    return None


# Axiom-like commands support multi-name declarations: ``Axiom a b c : T.``
# Also handles parenthetical syntax: ``Parameter (classic : False).``
# Capture all identifiers between the keyword and the colon.
_USER_AXIOM_MULTI_RE = re.compile(
    r"\b(?:Axioms?|Parameters?|Conjectures?|Hypothes[ie]s|Variables?)\s+([\w\s']+?)\s*:"
)
# Parenthetical syntax: ``Parameter (a b c : type).`` or multiple groups
# ``Parameter (a : nat) (b : bool).``  Captures the entire parenthesized
# group(s) so all names within can be extracted by _ROCQ_IDENT_RE.
_USER_AXIOM_PAREN_RE = re.compile(
    r"\b(?:Axioms?|Parameters?|Conjectures?|Hypothes[ie]s|Variables?|Context)"
    r"\s*(\((?:[^)]*)\)(?:\s*\([^)]*\))*)"
)
_ROCQ_IDENT_RE = re.compile(r"[A-Za-z_]\w*")

# Theorem-like commands declare a single name: ``Theorem name : T.``
# A proved Theorem (Qed) won't appear in Print Assumptions, but an
# Admitted one will — adding all theorem names to the suspicious set is
# safe defense-in-depth.
_USER_THEOREM_RE = re.compile(
    r"\b(?:Theorem|Lemma|Proposition|Corollary|Example|Fact|Remark)\s+(\w+)\b"
)

# Definition-like commands: ``Definition name``, ``Fixpoint name``, etc.
# These can also create axioms when followed by Admitted.
# Defense-in-depth: even though Phase 3 bans Admitted, this catches the
# names in case the ban is somehow bypassed.
_USER_DEF_RE = re.compile(
    r"\b(?:Definition|Fixpoint|CoFixpoint|Function|Let|Instance)\s+(\w+)\b"
)


def _extract_user_axiom_names(proof: str) -> set[str]:
    """Extract names declared by user-introduced commands.

    These names represent user-introduced bindings that must be treated as
    suspicious in Print Assumptions output, even if they match whitelist names.

    Covers:
    - Axiom-like: Axiom, Parameter, Conjecture, Hypothesis, Variable
      (including multi-name ``Axiom a b c : T.`` and parenthetical
      ``Parameter (name : type).`` syntax)
    - Theorem-like: Theorem, Lemma, Proposition, Corollary, Example, Fact, Remark
    - Definition-like: Definition, Fixpoint, CoFixpoint, Function, Let, Instance
    """
    neutralized = _neutralize_for_regex(proof)
    names: set[str] = set()

    # Axiom-like: may declare multiple names before ':'
    for m in _USER_AXIOM_MULTI_RE.finditer(neutralized):
        names_str = m.group(1)
        for ident_m in _ROCQ_IDENT_RE.finditer(names_str):
            names.add(ident_m.group())

    # Axiom-like: parenthetical syntax — may have multiple groups and
    # multiple names per group: ``Parameter (a b : nat) (c : bool).``
    # The regex captures all parenthetical groups as one string.
    # We split by parentheses, then extract identifiers before each ':'.
    for m in _USER_AXIOM_PAREN_RE.finditer(neutralized):
        paren_text = m.group(1)
        # Split into individual groups: "(a b : nat)" "(c : bool)"
        for group in re.findall(r"\(([^)]*)\)", paren_text):
            # Extract names before the colon
            before_colon = group.split(":")[0] if ":" in group else group
            for ident_m in _ROCQ_IDENT_RE.finditer(before_colon):
                names.add(ident_m.group())

    # Theorem-like: single name
    for m in _USER_THEOREM_RE.finditer(neutralized):
        names.add(m.group(1))

    # Definition-like: single name (defense-in-depth)
    for m in _USER_DEF_RE.finditer(neutralized):
        names.add(m.group(1))

    return names


# ---------------------------------------------------------------------------
# Print Assumptions parser
# ---------------------------------------------------------------------------


def parse_and_classify_assumptions(
    stdout: str,
    *,
    require_qualified: bool = False,
    user_axiom_names: set[str] | None = None,
) -> tuple[str, dict]:
    """Parse Print Assumptions output and classify axioms.

    Args:
        stdout: The coqc stdout containing Print Assumptions output.
        require_qualified: If True, reject ambiguous unqualified axiom names
            (``add``, ``sub``, ``compare``, etc.) even if they match the
            whitelist.  Unique stdlib names (``classic``,
            ``functional_extensionality_dep``) are still accepted unqualified.
        user_axiom_names: If provided, axiom names in this set are treated as
            suspicious regardless of whitelist match.  Use for Phase 3 with
            names extracted by :func:`_extract_user_axiom_names`.

    Returns:
        ("closed", {})  -- no assumptions
        ("standard_only", {"standard": [...]})  -- only known safe axioms
        ("suspicious", {"suspicious": [...], "suspicious_names": [...], "standard": [...]})
    """
    assumptions = _parse_assumptions_raw(stdout)
    if not assumptions:
        return "closed", {}

    standard: list[str] = []
    suspicious: list[str] = []
    suspicious_names: list[str] = []

    for name, ty in assumptions:
        short = _axiom_short_name(name)
        # If this axiom was explicitly declared by the user, it's suspicious
        # regardless of whitelist match.
        if user_axiom_names is not None and (
            name in user_axiom_names or short in user_axiom_names
        ):
            suspicious.append(f"{name} : {ty}")
            suspicious_names.append(name)
        elif _is_standard_axiom(name, require_qualified=require_qualified):
            standard.append(f"{name} : {ty}")
        else:
            suspicious.append(f"{name} : {ty}")
            suspicious_names.append(name)

    if not suspicious:
        return "standard_only", {"standard": standard}
    else:
        return "suspicious", {
            "standard": standard,
            "suspicious": suspicious,
            "suspicious_names": suspicious_names,
        }


def _parse_assumptions_raw(stdout: str) -> list[tuple[str, str]]:
    """Parse Print Assumptions output into (name, type) pairs.

    Handles multi-line type signatures by joining continuation lines.

    Format variants (all produced by Print Assumptions):
        Axioms:
        classic : forall P : Prop, P \\/ ~ P
        Coq.Reals.Raxioms.completeness
          : forall E : R -> Prop, ...
        ClassicalDedekindReals.sig_forall_dec :
          forall P : nat -> Prop, ...

    Or:
        Closed under the global context

    IMPORTANT: parses from the LAST ``Print Assumptions`` output block
    in stdout.  This prevents a proof inside Module M from injecting
    ``Print Assumptions clean_lemma.`` whose output (``Closed under the
    global context``) would otherwise shadow the template's real output.
    The template's ``Print Assumptions`` is always the last one because
    it appears after ``End M.``
    """
    lines = stdout.split("\n")

    # --- Find the LAST Print Assumptions output marker ---
    # Markers are "Closed under the global context" or "Axioms:".
    # We parse from the last marker to ignore any injected output from
    # commands inside Module M.
    last_marker_idx = None
    for i, line in enumerate(lines):
        s = line.strip()
        if s == "Closed under the global context":
            last_marker_idx = i
        elif s == "Axioms:" or s.startswith("Axioms:"):
            last_marker_idx = i

    if last_marker_idx is not None:
        # Check if the last marker is "Closed under the global context"
        if lines[last_marker_idx].strip() == "Closed under the global context":
            return []
        # Otherwise it's "Axioms:" — parse from there
        lines = lines[last_marker_idx:]

    assumptions: list[tuple[str, str]] = []
    current_name: str | None = None
    current_type_parts: list[str] = []

    for line in lines:
        stripped = line.strip()
        if stripped == "Closed under the global context":
            return []
        if not stripped or stripped == "Axioms:" or stripped.startswith("Axioms:"):
            continue

        # New assumption: starts with an identifier (non-whitespace at col 0, or
        # stripped line containing ' : ')
        if " : " in stripped and not line.startswith((" ", "\t")):
            # Flush previous
            if current_name is not None:
                assumptions.append((current_name, " ".join(current_type_parts)))
            name_part, _, type_part = stripped.partition(" : ")
            current_name = name_part.strip()
            current_type_parts = [type_part.strip()] if type_part.strip() else []
        elif stripped.endswith(" :") and not line.startswith((" ", "\t")):
            # Name with colon at end of line, type on next line(s)
            # e.g., "ClassicalDedekindReals.sig_forall_dec :"
            if current_name is not None:
                assumptions.append((current_name, " ".join(current_type_parts)))
            current_name = stripped[:-2].strip()
            current_type_parts = []
        elif stripped.startswith(": ") and current_name is not None:
            # Continuation: type starts on next line after name
            current_type_parts.append(stripped[2:].strip())
        elif line.startswith((" ", "\t")) and current_name is not None:
            # Indented continuation of type
            current_type_parts.append(stripped)
        elif " : " not in stripped and current_name is None:
            # Name on its own line (no ' : ' yet)
            current_name = stripped
            current_type_parts = []
        else:
            # Unknown format -- try to parse as name : type
            if " : " in stripped:
                if current_name is not None:
                    assumptions.append((current_name, " ".join(current_type_parts)))
                name_part, _, type_part = stripped.partition(" : ")
                current_name = name_part.strip()
                current_type_parts = [type_part.strip()]

    # Flush last
    if current_name is not None:
        assumptions.append((current_name, " ".join(current_type_parts)))

    return assumptions


# ---------------------------------------------------------------------------
# Verification hints
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Phase 3: Direct verification helpers
# ---------------------------------------------------------------------------

# Core types that must not be redefined by a proof.  Redefinition of these
# would let a proof silently prove a different statement than intended because
# Check output would look identical.
_CORE_NAMES: set[str] = {
    # Basic types
    "nat",
    "bool",
    "list",
    "option",
    "prod",
    "sum",
    "unit",
    "Empty_set",
    "comparison",
    "string",
    # Constructors of basic types — redefining these alters Check output
    "O",
    "S",
    "true",
    "false",
    "nil",
    "cons",
    "Some",
    "None",
    "pair",
    "tt",
    "inl",
    "inr",
    "Eq",
    "Lt",
    "Gt",
    "left",
    "right",
    # Propositions / logical connectives
    "eq",
    "True",
    "False",
    "and",
    "or",
    "not",
    "iff",
    "sig",
    "sigT",
    "ex",
    "sumbool",
    "sumor",
    # Number types
    "Z",
    "N",
    "positive",
    "Q",
    # Constructors of number types
    "Z0",
    "Zpos",
    "Zneg",
    "xH",
    "xO",
    "xI",
    "N0",
    "Npos",
    # Reals (axiomatized — commonly used in competition problems)
    "R",
    # Primitive types
    "int",
    "float",
    "array",
    # Comparisons (commonly used in Check output for propositions)
    "le",
    "lt",
    "ge",
    "gt",
    # Accessibility (well-founded recursion)
    "Acc",
    "well_founded",
    # Stdlib predicates — redefining these can make theorems trivially true
    "Sorted",
    "StronglySorted",
    "NoDup",
    "Permutation",
    "Forall",
    "Exists",
    "Forall2",
    "In",
    "incl",
    "even",
    "odd",
    "Nat.even",
    "Nat.odd",
    # String/Ascii types (commonly used in competition problems)
    "ascii",
    "byte",
    "Ascii",
    "Byte",
}

# Patterns that define or shadow names.  In Phase 3 (no Module M sandbox),
# ANY of these can redefine a core name and make Check output identical.
# Includes:
#   - Inductive-family: Inductive, CoInductive, Record, Variant, Structure, Class
#   - Value-defining: Definition, Fixpoint, CoFixpoint, Let, Function
#   - Axiom-like: Axiom, Parameter, Conjecture, Hypothesis, Variable
#   - Theorem-like: Theorem, Lemma, Proposition, Corollary, Example, Fact, Remark
#   - Primitive: Primitive (kernel-level type binding)
_NAME_DEF_KEYWORDS = (
    r"(?:Inductive|CoInductive|Record|Variant|Structure|Class"
    r"|Definition|Fixpoint|CoFixpoint|Let|Function|Primitive"
    r"|Axiom|Parameter|Conjecture|Hypothesis|Variable"
    r"|Theorem|Lemma|Proposition|Corollary|Example|Fact|Remark)"
)


def _check_type_shadowing(proof: str) -> str | None:
    """Reject proofs that redefine core names.

    Scans the proof for ``Inductive nat``, ``Definition eq``,
    ``Fixpoint bool``, ``Let nat``, etc. using
    :func:`_neutralize_for_regex` to ignore definitions inside comments
    and strings.

    Returns an error message if a core name is redefined, or None if clean.
    """
    neutralized = _neutralize_for_regex(proof)
    for typename in sorted(_CORE_NAMES):
        pattern = rf"\b{_NAME_DEF_KEYWORDS}\s+{re.escape(typename)}\b"
        if re.search(pattern, neutralized):
            return f"Proof redefines core name '{typename}'"
    return None


def _extract_definition_names(source: str) -> set[str]:
    """Extract all definition/type names from a Rocq source.

    Returns the set of names introduced by Definition, Fixpoint, Inductive,
    Record, etc. in *source*.  Used to extract names from the problem statement
    so Phase 3 can ban their redefinition in the proof.

    Reuses the same regexes as :func:`_extract_user_axiom_names` plus
    Inductive-family keywords (Inductive, CoInductive, Record, etc.) which
    that function does not cover (they are irrelevant for axiom tracking
    but critical for type-redefinition defense).
    """
    neutralized = _neutralize_for_regex(source)
    names: set[str] = set()

    # Definition-like (already captured by _USER_DEF_RE)
    for m in _USER_DEF_RE.finditer(neutralized):
        names.add(m.group(1))

    # Inductive-family: Inductive, CoInductive, Record, Variant, Structure, Class
    for m in _INDUCTIVE_DEF_RE.finditer(neutralized):
        names.add(m.group(1))

    # Theorem-like
    for m in _USER_THEOREM_RE.finditer(neutralized):
        names.add(m.group(1))

    return names


# Inductive-family keywords: ``Inductive name``, ``Record name``, etc.
_INDUCTIVE_DEF_RE = re.compile(
    r"\b(?:Inductive|CoInductive|Record|Variant|Structure|Class)\s+(\w+)\b"
)

# All definition keywords for sentence extraction (union of _NAME_DEF_KEYWORDS
# plus Inductive-family that _NAME_DEF_KEYWORDS already includes).
_ALL_DEF_KEYWORDS_RE_STR = (
    r"(?:Inductive|CoInductive|Record|Variant|Structure|Class"
    r"|Definition|Fixpoint|CoFixpoint|Let|Function|Primitive"
    r"|Axiom|Parameter|Conjecture|Hypothesis|Variable"
    r"|Theorem|Lemma|Proposition|Corollary|Example|Fact|Remark)"
)


def _extract_definition_sentence(source: str, name: str) -> str | None:
    """Extract the normalized definition sentence for *name* from *source*.

    Finds the Rocq sentence that defines *name* (from the keyword to the
    sentence-terminating period) and returns it with whitespace collapsed
    and comments/strings blanked.  Returns None if no definition is found.

    Used to compare definitions between problem and proof: if the
    normalized sentences are identical, the definitions are the same.
    """
    neutralized = _neutralize_for_regex(source)
    # Match: definition keyword + name + everything to sentence-ending period
    pattern = (
        rf"(?ms)\b{_ALL_DEF_KEYWORDS_RE_STR}\s+{re.escape(name)}\b" rf".*?\.(?=\s|$)"
    )
    m = re.search(pattern, neutralized)
    if m is None:
        return None
    # Use neutralized text (comments/strings blanked) and collapse whitespace
    sentence = neutralized[m.start() : m.end()]
    return re.sub(r"\s+", " ", sentence).strip()


def build_direct_verification_source(
    proof: str, problem_name: str, *, problem_statement: str = ""
) -> str:
    """Build source for Phase 3: proof + Check + Print Assumptions.

    Appends ``Check @<name>.`` (with ``Set Printing All``) and
    ``Print Assumptions <name>.`` to the proof.  The caller compiles
    this source and parses both outputs from stdout.

    When *problem_statement* is provided, extracts definition names from
    it and rejects any proof that redefines them.  This prevents the
    type-redefinition attack where a proof redefines a problem's
    Definition/Inductive with a trivially provable body while producing
    identical Check output.

    Raises ValueError if the proof contains forbidden commands, redefines
    a core type or problem definition, or if the problem_name is invalid.

    Known limitations (accepted, documented in verification_method="direct"):

    * **Notation/scope redefinition**: A proof can use
      ``Local Notation "a + b" := 0`` before reproducing a problem's
      Definition with character-identical text.  The definition has
      different kernel semantics but identical source text and opaque
      ``Check`` output.  ``Set Printing All`` does not unfold user
      definitions, so the type comparison cannot detect this.

    * **Stdlib function shadowing**: A proof can redefine a stdlib
      function (e.g. ``fold_left``) that the problem's definition calls.
      The problem's definition text is unchanged, and ``Check`` output
      is identical because user definitions are opaque.
    """
    forbidden = _check_forbidden_commands(proof)
    if forbidden:
        raise ValueError(forbidden)

    type_shadow = _check_type_shadowing(proof)
    if type_shadow:
        raise ValueError(type_shadow)

    module_shadow = _check_module_name_shadowing(proof)
    if module_shadow:
        raise ValueError(module_shadow)

    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", problem_name):
        raise ValueError(
            f"problem_name must be a valid Rocq identifier. Got: {problem_name!r}"
        )

    # Phase 3: Detect and reject redefinition of problem names with
    # DIFFERENT bodies.  Without Module M, a proof can redefine e.g.
    # "Definition is_even n := True." to make the theorem trivially
    # provable while producing identical Check output.
    #
    # Legitimate proofs that faithfully reproduce the same definitions
    # (e.g., the same Inductive color := Red | Green | Blue.) are allowed.
    if problem_statement:
        problem_names = _extract_definition_names(problem_statement)
        # Remove the theorem name itself (the proof must define it!)
        problem_names.discard(problem_name)
        if problem_names:
            proof_names = _extract_definition_names(proof)
            # Also extract Axiom-like names from proof (broader coverage)
            proof_names |= _extract_user_axiom_names(proof)
            shared_names = problem_names & proof_names
            if shared_names:
                # Compare definition text for each shared name.
                # If the definition text differs, it's an attack.
                changed = []
                for name in sorted(shared_names):
                    prob_text = _extract_definition_sentence(problem_statement, name)
                    proof_text = _extract_definition_sentence(proof, name)
                    if prob_text and proof_text and prob_text != proof_text:
                        changed.append(name)
                    elif proof_text and not prob_text:
                        # Proof defines a name that exists in the problem
                        # but we couldn't extract the problem's definition
                        # (e.g., different keyword). Flag it conservatively.
                        changed.append(name)
                if changed:
                    names_str = ", ".join(changed)
                    raise ValueError(
                        f"Proof redefines name(s) from the problem statement "
                        f"with different bodies: {names_str}. "
                        f"In direct verification mode (no Module M sandbox), "
                        f"the proof must not alter types or functions from "
                        f"the problem."
                    )

    # Phase 3 structural ban: Admitted and admit tactic.
    # A legitimate complete proof should never contain Admitted or admit.
    # Banning these closes the entire axiom-bypass vulnerability class
    # (Definition/Lemma/Theorem + Admitted creates axioms that could
    # pass the whitelist check).
    neutralized = _neutralize_for_regex(proof)
    if re.search(r"\bAdmitted\b", neutralized):
        raise ValueError(
            "Proof contains 'Admitted' which is not allowed in direct verification. "
            "Provide a complete proof without Admitted."
        )
    if re.search(r"\badmit\b", neutralized):
        raise ValueError(
            "Proof contains 'admit' tactic which is not allowed in direct "
            "verification. Provide a complete proof without admit."
        )
    if re.search(r"\bgive_up\b", neutralized):
        raise ValueError(
            "Proof contains 'give_up' tactic which is not allowed in direct "
            "verification. Provide a complete proof without give_up."
        )

    # Phase 3: Ban Declare Module — creates axioms from Module Type
    # parameters without any visible Axiom/Parameter keyword in the proof.
    # The axiom names use the declared module's name as prefix, which could
    # bypass the whitelist if the module name happens to match stdlib prefixes.
    if re.search(r"\bDeclare\s+Module\b", neutralized):
        # Allow "Declare Module Type" (harmless, defines a signature)
        # but reject "Declare Module <name>" (creates axioms)
        for dm_match in re.finditer(r"\bDeclare\s+Module\b", neutralized):
            after = neutralized[dm_match.end() :].lstrip()
            if not re.match(r"Type\b", after):
                raise ValueError(
                    "Forbidden command 'Declare Module' in direct verification "
                    "(creates axioms without visible Parameter/Axiom keywords). "
                    "Use explicit Parameter declarations instead."
                )

    # Phase 3-specific forbidden commands: bare Export, Include, and bare
    # Import can shadow names without Module M protection.
    # "Require Export" and "From ... Require Export" are safe (equivalent to
    # Require Import + re-export to downstream importers, harmless here).
    for m in re.finditer(r"\bExport\b", neutralized):
        preceding = neutralized[max(0, m.start() - 200) : m.start()]
        if not re.search(r"\bRequire\s*$", preceding):
            raise ValueError(
                "Forbidden bare 'Export' in direct verification "
                "(use 'Require Export' instead; bare Export may shadow names "
                "without Module M sandbox)"
            )
    if re.search(r"\bInclude\b", neutralized):
        raise ValueError(
            "Forbidden command 'Include' in direct verification "
            "(may shadow names without Module M sandbox)"
        )
    # Ban bare Import (not preceded by Require).  "Require Import" and
    # "From ... Require Import" are safe; bare "Import Foo." makes
    # module contents visible and can shadow names.
    for m in re.finditer(r"\bImport\b", neutralized):
        preceding = neutralized[max(0, m.start() - 200) : m.start()]
        if not re.search(r"\bRequire\s*$", preceding):
            raise ValueError(
                "Forbidden bare 'Import' in direct verification "
                "(use 'Require Import' instead; bare Import may shadow names "
                "without Module M sandbox)"
            )

    return (
        f"{proof}\n\n"
        # Reset printing flags before Check to prevent proof from
        # truncating output via Set Printing Depth 0, etc.
        f"Set Printing Width 120.\n"
        f"Set Printing Depth 1000000.\n"
        f"Unset Printing Universes.\n"
        f"Set Printing All.\n"
        f"Check @{problem_name}.\n\n"
        f"Unset Printing All.\n"
        f"Unset Printing Universes.\n"
        f"Set Printing Width 120.\n"
        f"Set Printing Depth 1000000.\n"
        f"Print Assumptions {problem_name}.\n"
    )


def build_direct_type_check_source(problem_statement: str, problem_name: str) -> str:
    """Build source for Phase 3 type extraction from the problem statement.

    Compiles the problem statement as-is (it should already contain
    ``Admitted.`` or similar) and appends ``Check @<name>.`` with
    ``Set Printing All`` to extract the expected type signature.

    Raises ValueError if the problem statement contains forbidden commands
    or if the problem_name is invalid.
    """
    forbidden = _check_forbidden_commands(problem_statement)
    if forbidden:
        raise ValueError(forbidden)

    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", problem_name):
        raise ValueError(
            f"problem_name must be a valid Rocq identifier. Got: {problem_name!r}"
        )

    return (
        f"{problem_statement}\n\n"
        # Reset printing flags to prevent truncation from problem statement settings.
        f"Set Printing Width 120.\n"
        f"Set Printing Depth 1000000.\n"
        f"Unset Printing Universes.\n"
        f"Set Printing All.\n"
        f"Check @{problem_name}.\n"
    )


def parse_check_type(stdout: str, name: str) -> str | None:
    """Extract type string from ``Check @<name>.`` output.

    Rocq outputs::

        @name
             : <type>

    or for short types::

        @name : <type>

    IMPORTANT: parses from the LAST matching ``@name`` occurrence in stdout.
    This prevents a proof from injecting its own ``Check @name.`` whose output
    would otherwise shadow the template's real output.  The template's
    ``Check`` is always the last one because it appears after the proof.

    Returns the raw type string (whitespace-normalized), or None if
    the Check output cannot be found/parsed.
    """
    lines = stdout.split("\n")
    # Find the LAST line containing the name from Check output.
    # Use exact matching: "@name" followed by whitespace, colon, or end of line.
    # This prevents prefix collisions (e.g., "@foobar" matching "@foo").
    at_name = f"@{name}"
    start_idx = None
    for i, line in enumerate(lines):
        stripped = line.strip()
        if (
            stripped == at_name
            or stripped.startswith(f"{at_name} ")
            or stripped.startswith(f"{at_name}\t")
        ):
            start_idx = i
        elif stripped == name:
            start_idx = i

    if start_idx is None:
        return None

    # Check if type is on the same line: "@name : type"
    first_line = lines[start_idx].strip()
    if " : " in first_line:
        _, _, type_part = first_line.partition(" : ")
        type_parts = [type_part.strip()]
    else:
        type_parts = []

    # Collect continuation lines (indented or starting with ":")
    for j in range(start_idx + 1, len(lines)):
        line = lines[j]
        stripped = line.strip()
        if not stripped:
            break
        if line.startswith((" ", "\t")):
            # Indented continuation
            if stripped.startswith(": "):
                type_parts.append(stripped[2:].strip())
            else:
                type_parts.append(stripped)
        else:
            break

    if not type_parts:
        return None

    return " ".join(type_parts)


def normalize_type_for_comparison(type_str: str) -> str:
    """Normalize a type string for comparison.

    - Collapses all whitespace (spaces, tabs, newlines) to single spaces
    - Strips universe annotations ``@{...}``
    - Strips leading/trailing whitespace
    """
    # Strip universe annotations @{...}
    result = re.sub(r"@\{[^}]*\}", "", type_str)
    # Collapse whitespace
    result = re.sub(r"\s+", " ", result)
    return result.strip()


# ---------------------------------------------------------------------------
# Verification hints
# ---------------------------------------------------------------------------


def verification_hint(stderr: str) -> str:
    """Generate a human-readable hint from a verification failure."""
    if ("Unable to unify" in stderr or "Cannot apply" in stderr) and "M." in stderr:
        return (
            "The proof may define custom types/functions that don't unify "
            "across the Module M. boundary. This is a known limitation. "
            "If rocq_compile succeeded, the proof is likely correct."
        )
    if "Unable to unify" in stderr or "Cannot apply" in stderr:
        return (
            "Type mismatch: the proof's result type does not match "
            "the expected theorem type."
        )
    if "not found" in stderr and "M." in stderr:
        return (
            "The theorem name in the proof does not match the expected name. "
            "Ensure your proof defines a theorem with the exact name provided."
        )
    if "Syntax error" in stderr:
        return "The proof has a syntax error."
    if "Timeout" in stderr:
        return "A tactic in the proof timed out."
    return "The proof does not prove the original statement."
