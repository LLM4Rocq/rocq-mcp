"""Module M. verification template, Print Assumptions parsing, axiom whitelist."""

from __future__ import annotations

import re


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
    1. Places the preamble (imports) at the top level
    2. Wraps the proof body in Module M. ... End M.
    3. Places the cleaned problem statement outside the module
    4. Applies M.theorem_name to prove the original statement
    5. Runs Print Assumptions to check for axioms/admits
    """
    preamble, body = _split_preamble(proof)
    clean_statement = _clean_problem_statement(problem_statement)

    return (
        f"{preamble}\n\n"
        f"Module M.\n"
        f"{body}\n"
        f"End M.\n\n"
        f"{clean_statement}\n"
        f"Proof.\n"
        f"apply M.{problem_name} || eapply M.{problem_name}.\n"
        f"all: first [ assumption | reflexivity | auto | lia | lra | simpl; auto ].\n"
        f"Qed.\n\n"
        f"Print Assumptions {problem_name}.\n"
    )


def _clean_problem_statement(problem_statement: str) -> str:
    """Strip trailing Admitted./Abort./admit. from the problem statement.

    Only strips at end of text (not in the middle). Handles optional
    whitespace before the dot.
    """
    return re.sub(
        r"\s*(Admitted|Abort|admit)\s*\.\s*$",
        "",
        problem_statement,
    ).strip()


def _split_preamble(source: str) -> tuple[str, str]:
    """Split source into (preamble, body).

    Preamble = leading block of Require/Import/From/Set/Open/Notation/etc. lines,
    including blank lines and comments within that block.

    Handles multi-line statements by tracking whether we're inside an
    unfinished statement (no closing '.') or a multi-line comment.
    """
    lines = source.split("\n")
    preamble_kw = (
        "Require", "Import", "Export", "From", "Set", "Unset",
        "Open", "Close", "Notation", "Declare", "Bind", "Delimit",
        "Reserved", "Ltac", "Tactic",
    )
    preamble: list[str] = []
    in_comment = 0  # nesting depth
    in_statement = False  # inside a multi-line preamble statement

    body_start = len(lines)  # default: everything is preamble

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Track multi-line comments
        in_comment += stripped.count("(*") - stripped.count("*)")
        if in_comment < 0:
            in_comment = 0

        # Inside a multi-line comment: always preamble
        if in_comment > 0 or stripped.endswith("*)"):
            preamble.append(line)
            continue

        # Inside a multi-line statement (continuation of a From ... Require Import)
        if in_statement:
            preamble.append(line)
            if "." in stripped:
                in_statement = False
            continue

        # Blank line: preamble
        if not stripped:
            preamble.append(line)
            continue

        # Comment-only line that opened and closed on same line
        if stripped.startswith("(*") and "*)" in stripped:
            preamble.append(line)
            continue

        # Preamble keyword
        if any(stripped.startswith(kw) for kw in preamble_kw):
            preamble.append(line)
            # Check if statement is complete (has a '.')
            if "." not in stripped:
                in_statement = True
            continue

        # Line starting with '#[' (attribute like #[global], #[export])
        if stripped.startswith("#["):
            preamble.append(line)
            if "." not in stripped:
                in_statement = True
            continue

        # Non-preamble line: body starts here
        body_start = i
        break

    return "\n".join(preamble), "\n".join(lines[body_start:])


# ---------------------------------------------------------------------------
# Axiom whitelist
# ---------------------------------------------------------------------------

# Whitelist of known safe axioms by short name (last dot-separated component).
# Print Assumptions outputs either qualified ("Coq.Logic.Classical_Prop.classic")
# or unqualified ("classic") names. We match on short name AND verify the
# qualified prefix comes from a known standard library module.

_KNOWN_SAFE_AXIOMS: set[str] = {
    # --- Classical logic ---
    "classic",                                  # forall P : Prop, P \/ ~ P

    # --- Extensionality ---
    "functional_extensionality_dep",            # (forall x, f x = g x) -> f = g
    "propositional_extensionality",             # (P <-> Q) -> P = Q
    "proof_irrelevance",                        # forall (p1 p2 : P), p1 = p2
    "JMeq_eq",                                  # JMeq x y -> x = y
    "eq_rect_eq",                               # UIP / Streicher's K

    # --- Choice and descriptions ---
    "constructive_indefinite_description",      # sig form of indefinite choice
    "constructive_definite_description",        # sig form of definite description
    "dependent_unique_choice",
    "unique_choice",
    "relational_choice",
    "epsilon",                                   # Hilbert epsilon
    "epsilon_spec",

    # --- Reals axiomatization (Coq.Reals.Raxioms) ---
    "R", "R0", "R1",
    "Rplus", "Rmult", "Ropp", "Rinv",
    "Rlt",
    "up",
    "R1_neq_R0",
    "Rplus_comm", "Rplus_assoc",
    "Rplus_opp_r", "Rplus_0_l",
    "Rmult_comm", "Rmult_assoc",
    "Rmult_1_l", "Rmult_plus_distr_l",
    "Rinv_l",
    "Rlt_asym", "Rlt_trans",
    "Rplus_lt_compat_l", "Rmult_lt_compat_l",
    "archimed",
    "completeness",
    "total_order_T",

    # --- Decidability (used by classical reals) ---
    "sig_forall_dec",
}

# Standard library module prefixes. Axioms qualified with these are safe.
_STDLIB_PREFIXES: tuple[str, ...] = ("Coq.", "Rocq.", "Stdlib.")


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
    """
    short = _axiom_short_name(name)
    if short not in _KNOWN_SAFE_AXIOMS:
        return False
    if "." not in name:
        # Unqualified: trust the whitelist
        return True
    # Qualified: must come from stdlib
    return any(name.startswith(prefix) for prefix in _STDLIB_PREFIXES)


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

    Format:
        Axioms:
        Coq.Logic.Classical_Prop.classic : forall P : Prop, P \\/ ~ P
        Coq.Reals.Raxioms.completeness
          : forall E : R -> Prop, ...

    Or:
        Closed under the global context
    """
    lines = stdout.split("\n")
    assumptions: list[tuple[str, str]] = []
    current_name: str | None = None
    current_type_parts: list[str] = []

    for line in lines:
        if "Closed under the global context" in line:
            return []

        stripped = line.strip()
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
            current_type_parts = [type_part.strip()]
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
