"""Module M. verification template, Print Assumptions parsing, axiom whitelist."""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum, auto

# ---------------------------------------------------------------------------
# Shared constants and helpers
# ---------------------------------------------------------------------------

_ROCQ_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_ROCQ_QUALIFIED_NAME_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def _validate_rocq_identifier(name: str, label: str = "problem_name") -> None:
    """Raise ValueError if *name* is not a valid Rocq identifier."""
    if not _ROCQ_IDENT_RE.fullmatch(name):
        raise ValueError(f"{label} must be a valid Rocq identifier. Got: {name!r}")


def is_rocq_qualified_name(name: str) -> bool:
    """Return True if *name* is a valid Rocq qualified identifier.

    Accepts either a bare identifier (``add_comm``) or a dotted
    qualified name (``Nat.add_comm``, ``Coq.Init.Logic.eq``).  Used
    by tools that take a theorem reference as input.
    """
    return bool(_ROCQ_QUALIFIED_NAME_RE.fullmatch(name))


# Block to reset printing flags after Module M, ensuring Print Assumptions
# output matches our parser's expected format.
_PRINT_RESET_BLOCK = (
    "Unset Printing All.\n"
    "Unset Printing Universes.\n"
    "Set Printing Width 120.\n"
    "Set Printing Depth 1000000.\n"
)


# ---------------------------------------------------------------------------
# Definition categories and problem structure
# ---------------------------------------------------------------------------


class DefCategory(Enum):
    """Classification of Rocq vernacular commands for template placement."""

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


def _iter_rocq_chars(text: str):
    """Shared per-character Rocq lexer driving :func:`_rocq_scan` and
    :func:`_neutralize_for_regex`.

    Yields ``(index, char, in_comment, in_string, consume)`` tuples
    tracking ``(* ... *)`` comment nesting (arbitrary depth) and
    ``"..."`` string literals (with ``""`` escape).  String literals
    inside comments are tracked so ``*)`` within a quoted string within
    a comment does NOT close the comment, matching Rocq's lexer.

    ``consume`` is ``2`` when the event represents a two-character
    token (``(*``, ``*)``, or a ``""`` string escape) and the second
    character is at ``index + 1``; otherwise ``1``.  Callers that need
    per-character output (e.g. position-preserving neutralization) use
    ``consume`` to fan a single yield out to both positions; callers
    that want one event per logical token (e.g. sentence-boundary
    detection) can ignore it.
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
                    yield i, ch, depth > 0, True, 2
                    i += 2
                    continue
                in_str = False
            yield i, ch, depth > 0, True, 1
        elif depth > 0:
            if ch == '"':
                in_str = True
                yield i, ch, True, True, 1
            elif ch == "*" and i + 1 < length and text[i + 1] == ")":
                depth -= 1
                yield i, ch, True, False, 2
                i += 2
                continue
            elif ch == "(" and i + 1 < length and text[i + 1] == "*":
                depth += 1
                yield i, ch, True, False, 2
                i += 2
                continue
            else:
                yield i, ch, True, False, 1
        else:
            if ch == '"':
                in_str = True
                yield i, ch, False, True, 1
            elif ch == "(" and i + 1 < length and text[i + 1] == "*":
                depth += 1
                yield i, ch, True, False, 2
                i += 2
                continue
            else:
                yield i, ch, False, False, 1
        i += 1


def _neutralize_for_regex(text: str) -> str:
    """Replace comment and string interiors with spaces, preserving text length.

    Comment delimiters ``(* ... *)`` and their contents become spaces.
    String interiors (between ``"..."``) become spaces but the quote
    delimiters are preserved outside comments.  This lets regex patterns
    match on the neutralized text with spans that map 1:1 back to the
    original.
    """
    result = list(text)
    for idx, ch, in_comment, in_str, consume in _iter_rocq_chars(text):
        if in_comment:
            result[idx] = " "
            if consume == 2:
                result[idx + 1] = " "
        elif in_str:
            if consume == 2:
                # "" escape inside a string — blank both characters
                result[idx] = " "
                result[idx + 1] = " "
            elif ch != '"':
                # String interior — blank; the lone " delimiter is preserved
                result[idx] = " "
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

    Thin wrapper over :func:`_iter_rocq_chars` — the underlying lexer state
    machine is shared with :func:`_neutralize_for_regex`.
    """
    for idx, ch, in_comment, in_str, _consume in _iter_rocq_chars(text):
        yield idx, ch, in_comment, in_str


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

    _validate_rocq_identifier(problem_name)

    clean_statement = _clean_problem_statement(problem_statement)

    return (
        f"Module M.\n"
        f"{proof}\n"
        f"End M.\n\n"
        f"{_PRINT_RESET_BLOCK}\n"
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

    _validate_rocq_identifier(problem_name)

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

    parts.extend(_PRINT_RESET_BLOCK.splitlines())
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
    # --- mathcomp.classical-specific short names ---
    # mathcomp re-exports most standard axioms (functional_extensionality_dep,
    # propositional_extensionality, etc.) under their stdlib short names,
    # which are already covered above.  These three are mathcomp-specific.
    "EM",  # excluded middle (boolp)
    "pselect",  # forall P, {P} + {~P}                       (boolp)
    "cid",  # constructive indefinite description           (boolp)
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
    # mathcomp.classical (commonly used by analysis/finmap proofs;
    # re-exports stdlib axioms under their stdlib short names plus a
    # few mathcomp-specific short names: EM, pselect, cid).
    "mathcomp.classical.boolp.",
    "mathcomp.classical.classical_sets.",
    # NOTE: bare ``boolp.`` / ``classical_sets.`` are intentionally NOT
    # in this list.  Together with the 2-char short name ``EM`` in the
    # whitelist, a workspace-supplied ``boolp.v`` containing
    # ``Axiom EM : False.`` would have been auto-trusted by rocq_verify
    # Phase 3 (no Module M wrapping; the proof-source ``\bAxiom\b``
    # block does not see what ``Require Import`` pulls in).  Require the
    # full ``mathcomp.classical.boolp.`` qualifier instead.
)


def _axiom_short_name(qualified_name: str) -> str:
    """Extract short name: 'Coq.Logic.Classical_Prop.classic' -> 'classic'."""
    return qualified_name.rsplit(".", 1)[-1]


def _is_standard_axiom(name: str) -> bool:
    """Check if an axiom name refers to a known standard library axiom.

    For qualified names (containing dots): the prefix must be from a known
    stdlib module AND the short name must be in the whitelist.

    For unqualified names: accepted if the short name is in the whitelist.

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
        return True
    # Qualified: must come from stdlib (full prefix or known module name)
    if any(name.startswith(prefix) for prefix in _STDLIB_PREFIXES):
        return True
    return any(name.startswith(prefix) for prefix in _STDLIB_MODULE_PREFIXES)


# ---------------------------------------------------------------------------
# Print Assumptions parser
# ---------------------------------------------------------------------------


def parse_and_classify_assumptions(
    stdout: str,
    admitted_names: set[str] | None = None,
) -> tuple[str, dict]:
    """Parse Print Assumptions output and classify axioms.

    The primary output is the three categorized name lists (``admitted``,
    ``classical_axioms``, ``user_axioms``) returned in ``details``.  Together
    they partition the assumptions: every parsed name appears in exactly one
    of the three lists.

    Args:
        stdout: Raw ``Print Assumptions`` output to parse.
        admitted_names: Optional set of names that the caller knows correspond
            to ``Admitted`` lemmas (or proofs ending in ``admit.``/``Admit.``).
            ``Print Assumptions`` does not distinguish ``Admitted`` from
            ``Axiom`` in its output — both appear under the ``Axioms:``
            header — so callers with extra context (e.g., access to the
            source file) can pass this set to surface admits separately
            from user-declared axioms.  Names in ``admitted_names`` that are
            *not* present in the parsed assumptions are silently ignored.

    Returns:
        ``(verdict, details)`` where ``details`` always contains the three
        categorized lists:

            * ``"admitted"`` (list[str]) — names the caller has externally
              identified as ``Admitted``/``admit`` (passed via
              ``admitted_names``).  **Currently always ``[]`` in the standard
              ``rocq_assumptions`` flow** because ``Print Assumptions`` does
              not distinguish ``Admitted`` from ``Axiom``/``Parameter``/
              ``Conjecture``.  Future enrichment may populate this from a
              source-file scan.  **Do not treat empty ``admitted`` as
              evidence of an admit-free proof.**
            * ``"classical_axioms"`` (list[str]) — axiom names matched
              against :data:`_KNOWN_SAFE_AXIOMS`, a static whitelist of
              classical-logic axioms (``Excluded_middle``,
              ``FunctionalExtensionality``, ``ProofIrrelevance``, primitive
              ints/floats/arrays/strings, …).  Match is by **exact qualified
              name**; user-defined axioms with whitelisted names (e.g. a
              custom ``classic`` outside ``Coq.Logic.Classical_Prop``) would
              currently be auto-trusted.
            * ``"user_axioms"`` (list[str]) — non-classical axiom names
              *not* known to be admits.  Anything user-declared
              (``Axiom``, ``Parameter``, ``Conjecture``) outside the
              whitelist lands here, and so do ``Admitted`` lemmas (until
              ``admitted`` is populated by a future phase).

        **Trusted closed proof**: ``not user_axioms and not admitted``
        (with ``classical_axioms`` allowed if you accept classical logic).

        Notes:
            ``verdict`` is **DEPRECATED**; prefer the structured lists above.
            For back-compat, it is one of:

                - ``"closed"``        ≡ ``not admitted and not classical_axioms
                                          and not user_axioms``
                - ``"standard_only"`` ≡ has ``classical_axioms`` only
                - ``"suspicious"``    ≡ has ``admitted`` or ``user_axioms``

            The ``verdict`` field is retained for back-compat; it will be
            removed in a future major version when the legacy callers have
            migrated.

            Legacy keys also preserved on ``details`` for back-compat:
                * ``"closed"``         -> ``{}`` (plus the new lists)
                * ``"standard_only"``  -> ``{"standard": [...]}``
                * ``"suspicious"``     -> ``{"standard": [...],
                                              "suspicious": [...],
                                              "suspicious_names": [...]}``
    """
    assumptions = _parse_assumptions_raw(stdout)
    admitted_set = set(admitted_names) if admitted_names else set()

    admitted: list[str] = []
    classical_axioms: list[str] = []
    user_axioms: list[str] = []

    standard: list[str] = []
    suspicious: list[str] = []
    suspicious_names: list[str] = []

    for name, ty in assumptions:
        is_classical = _is_standard_axiom(name)
        # Admitted classification takes precedence over classical: a lemma
        # the caller flagged as admitted is admitted, full stop.
        if name in admitted_set:
            admitted.append(name)
        elif is_classical:
            classical_axioms.append(name)
        else:
            user_axioms.append(name)
        # Legacy classification (for back-compat keys).
        if is_classical:
            standard.append(f"{name} : {ty}")
        else:
            suspicious.append(f"{name} : {ty}")
            suspicious_names.append(name)

    new_lists = {
        "admitted": admitted,
        "classical_axioms": classical_axioms,
        "user_axioms": user_axioms,
    }

    if not assumptions:
        return "closed", {**new_lists}
    # An admit overrides classical-only classification: the legacy verdict
    # must be consistent with the new ``admitted`` list.
    if admitted:
        return "suspicious", {
            "standard": standard,
            "suspicious": suspicious,
            "suspicious_names": suspicious_names,
            **new_lists,
        }
    if not suspicious:
        return "standard_only", {"standard": standard, **new_lists}
    return "suspicious", {
        "standard": standard,
        "suspicious": suspicious,
        "suspicious_names": suspicious_names,
        **new_lists,
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

    # Invariant: every entry pushed onto ``assumptions`` has a ``name`` that
    # starts with a dotted-alphanumeric Coq identifier — no whitespace, no
    # bare-line continuation absorbed as a fresh name.  Every branch below
    # that constructs a new ``current_name`` honours this; future branches
    # added here must preserve it.

    for line in lines:
        stripped = line.strip()
        if stripped == "Closed under the global context":
            return []
        if not stripped or stripped == "Axioms:" or stripped.startswith("Axioms:"):
            continue

        # New assumption: starts with an identifier (non-whitespace at col 0, or
        # stripped line containing ' : ')
        if " : " in stripped and not line.startswith((" ", "\t")):
            name_part, _, type_part = stripped.partition(" : ")
            name_part = name_part.strip()
            # Defense-in-depth: real Coq identifiers are dotted-path
            # alphanumerics with no whitespace.  Lines like
            # ``Fetching opaque proofs from disk : foo.vo`` otherwise match
            # this branch and pollute the assumptions list (the cosmetic
            # regex strip in ``interactive.run_assumptions`` is the first
            # line of defense; this guard catches anything that slips past).
            if not name_part or any(c.isspace() for c in name_part):
                continue
            # Flush previous
            if current_name is not None:
                assumptions.append((current_name, " ".join(current_type_parts)))
            current_name = name_part
            current_type_parts = [type_part.strip()] if type_part.strip() else []
        elif stripped.endswith(" :") and not line.startswith((" ", "\t")):
            # Name with colon at end of line, type on next line(s)
            # e.g., "ClassicalDedekindReals.sig_forall_dec :"
            name_part = stripped[:-2].strip()
            if not name_part or any(c.isspace() for c in name_part):
                continue
            if current_name is not None:
                assumptions.append((current_name, " ".join(current_type_parts)))
            current_name = name_part
            current_type_parts = []
        elif stripped.startswith(": ") and current_name is not None:
            # Continuation: type starts on next line after name
            current_type_parts.append(stripped[2:].strip())
        elif line.startswith((" ", "\t")) and current_name is not None:
            # Indented continuation of type
            current_type_parts.append(stripped)
        elif (
            " : " not in stripped
            and current_name is None
            and not line.startswith((" ", "\t"))
        ):
            # Name on its own line (no ' : ' yet).  Indented lines are NOT
            # valid here — they are hanging continuations from a name we
            # rejected above (e.g. a ``Fetching opaque proofs from disk :``
            # loader notice followed by an indented module path).
            current_name = stripped
            current_type_parts = []
        else:
            # Unknown format -- try to parse as name : type.  Same
            # whitespace-in-name guard as the primary branch — keep the
            # parser invariant symmetric across all entry points.
            if " : " in stripped:
                name_part, _, type_part = stripped.partition(" : ")
                name_part = name_part.strip()
                if not name_part or any(c.isspace() for c in name_part):
                    continue
                if current_name is not None:
                    assumptions.append((current_name, " ".join(current_type_parts)))
                current_name = name_part
                current_type_parts = [type_part.strip()]

    # Flush last
    if current_name is not None:
        assumptions.append((current_name, " ".join(current_type_parts)))

    return assumptions


# ---------------------------------------------------------------------------
# Phase 3: Direct verification helpers
# ---------------------------------------------------------------------------


def build_direct_verification_source(proof: str, problem_name: str) -> str:
    """Build source for Phase 3: proof + Check + Print Assumptions.

    Appends ``Check @<name>.`` (with ``Set Printing All``) and
    ``Print Assumptions <name>.`` to the proof.  The caller compiles
    this source and parses both outputs from stdout.

    Raises ValueError if the proof contains forbidden commands,
    incomplete proof markers (Admitted/admit/give_up), or if
    the problem_name is invalid.
    """
    forbidden = _check_forbidden_commands(proof)
    if forbidden:
        raise ValueError(forbidden)

    _validate_rocq_identifier(problem_name)

    # A complete proof should never contain Admitted, admit, or give_up.
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

    # Block axiom-introducing commands.  In Phase 1/2 these are harmless
    # (Module M wrapping makes them visible to Print Assumptions), but in
    # Phase 3 (direct compilation) a user-declared ``Axiom classic : False``
    # would be whitelisted by _is_standard_axiom because "classic" is in
    # _KNOWN_SAFE_AXIOMS.
    #
    # Note: Variable/Hypothesis are NOT blocked — they are section-local
    # and become parameters after ``End Section``.  They don't persist as
    # global axioms and are safe in Phase 3.
    for kw in ("Axiom", "Parameter", "Conjecture"):
        if re.search(rf"\b{kw}\b", neutralized):
            raise ValueError(
                f"Proof contains '{kw}' which is not allowed in direct verification. "
                f"A complete proof must not introduce axioms or unproven assumptions."
            )

    return (
        f"{proof}\n\n"
        f"Set Printing Width 120.\n"
        f"Set Printing Depth 1000000.\n"
        f"Unset Printing Universes.\n"
        f"Set Printing All.\n"
        f"Check @{problem_name}.\n\n"
        f"{_PRINT_RESET_BLOCK}"
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

    _validate_rocq_identifier(problem_name)

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
