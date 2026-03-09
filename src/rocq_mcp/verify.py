"""Module M. verification template, Print Assumptions parsing, axiom whitelist."""

from __future__ import annotations

import re

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
]


def _check_forbidden_commands(source: str) -> str | None:
    """Check for dangerous Rocq commands in the source text.

    Returns an error message string if a forbidden command is found,
    or None if the source is clean.
    """
    for pattern, message in _FORBIDDEN_PATTERNS:
        if re.search(pattern, source):
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
        f"{clean_statement}\n"
        f"Proof.\n"
        f"apply M.{problem_name} || eapply M.{problem_name}.\n"
        f"all: first [ assumption | reflexivity | auto | simpl; auto ].\n"
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
}

# Standard library module prefixes. Axioms qualified with these are safe.
_STDLIB_PREFIXES: tuple[str, ...] = ("Coq.", "Rocq.", "Stdlib.")

# Known stdlib module names that Print Assumptions outputs WITHOUT the full
# Stdlib./Coq. prefix. E.g., "ClassicalDedekindReals.sig_forall_dec" instead
# of "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec".
_STDLIB_MODULE_PREFIXES: tuple[str, ...] = (
    "ClassicalDedekindReals.",  # Dedekind reals axioms
    "FunctionalExtensionality.",  # functional extensionality
    "Eqdep.Eq_rect_eq.",  # eq_rect_eq / UIP
    "Classical_Prop.",  # classic, proof_irrelevance
    "ClassicalEpsilon.",  # constructive_indefinite_description, epsilon
    "ClassicalUniqueChoice.",  # dependent_unique_choice, unique_choice
    "ClassicalDescription.",  # constructive_definite_description
    "RelationalChoice.",  # relational_choice
    "PropExtensionality.",  # propositional_extensionality
    "Raxioms.",  # R, Rplus, Rmult, etc.
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
    if "Unable to unify" in stderr or "Cannot apply" in stderr:
        return (
            "The proof may define custom types/functions that don't unify "
            "across the Module M. boundary. This is a known limitation. "
            "If rocq_compile succeeded, the proof is likely correct."
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
