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
    """
    if not shared_names:
        return proof
    result = proof
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
        # Strip ALL occurrences (count=0), not just the first. Using count=1
        # would allow an adversary to hide a decoy definition (e.g. in a
        # comment-like context) to protect their real redefinition from stripping.
        result = re.sub(pattern, "", result, count=0)
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
        re.compile(r"\bSeparate Extraction\b"),
        "Forbidden command 'Separate Extraction' (writes .ml/.mli files)",
    ),
    (
        re.compile(r"\bRecursive Extraction\b"),
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
        re.compile(r"\bDeclare ML Module\b"),
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


def _check_forbidden_commands(source: str) -> str | None:
    """Check for dangerous Rocq commands in the source text.

    Comments are stripped before scanning so that forbidden keywords
    inside ``(* ... *)`` do not trigger false positives, and attackers
    cannot hide commands inside comment-like constructs.

    Returns an error message string if a forbidden command is found,
    or None if the source is clean.
    """
    stripped = _strip_rocq_comments(source)
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

    clean_statement = _clean_problem_statement(problem_statement)

    return (
        f"Module M.\n"
        f"{proof}\n"
        f"End M.\n\n"
        # Reset printing flags that Module M may have changed, to ensure
        # Print Assumptions output matches our parser's expected format.
        f"Unset Printing All.\n"
        f"Unset Printing Universes.\n"
        f"Set Printing Width 120.\n\n"
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
    result = re.sub(r"\s*Proof\s*\.\s*$", "", result)
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
}

# Standard library module prefixes. Axioms qualified with these are safe.
_STDLIB_PREFIXES: tuple[str, ...] = ("Coq.", "Rocq.", "Stdlib.")

# Known stdlib module names that Print Assumptions outputs WITHOUT the full
# Stdlib./Coq. prefix. E.g., "ClassicalDedekindReals.sig_forall_dec" instead
# of "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec".
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
)


def _axiom_short_name(qualified_name: str) -> str:
    """Extract short name: 'Coq.Logic.Classical_Prop.classic' -> 'classic'."""
    return qualified_name.rsplit(".", 1)[-1]


def _is_standard_axiom(name: str) -> bool:
    """Check if an axiom name refers to a known standard library axiom.

    For qualified names (containing dots): the prefix must be from a known
    stdlib module AND the short name must be in the whitelist.

    For unqualified names: must be in the whitelist directly.

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
        # Unqualified: trust the whitelist
        return True
    # Qualified: must come from stdlib (full prefix or known module name)
    if any(name.startswith(prefix) for prefix in _STDLIB_PREFIXES):
        return True
    return any(name.startswith(prefix) for prefix in _STDLIB_MODULE_PREFIXES)


# ---------------------------------------------------------------------------
# Print Assumptions parser
# ---------------------------------------------------------------------------


def parse_and_classify_assumptions(stdout: str) -> tuple[str, dict]:
    """Parse Print Assumptions output and classify axioms.

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
        if _is_standard_axiom(name):
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
    """
    lines = stdout.split("\n")
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
