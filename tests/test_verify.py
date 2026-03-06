"""Tests for rocq_verify tool and verification helpers in verify.py.

Part A: Unit tests for verify.py helpers (NO coqc needed)
    - TestSplitPreamble
    - TestCleanProblemStatement
    - TestAxiomClassification
    - TestParseAssumptions

Part B: Integration tests for rocq_verify (require coqc)
    - TestVerifySuccess
    - TestVerifyRejection
    - TestVerifyInputValidation
    - TestVerifyCleanup
"""

from __future__ import annotations

import glob as glob_mod

import pytest

from tests.conftest import COQC_AVAILABLE
from rocq_mcp.verify import (
    _split_preamble,
    _clean_problem_statement,
    _is_standard_axiom,
    _axiom_short_name,
    _parse_assumptions_raw,
    parse_and_classify_assumptions,
    build_verification_source,
)


# =========================================================================
# PART A: Unit tests (no coqc needed)
# =========================================================================


# ---------------------------------------------------------------------------
# _split_preamble
# ---------------------------------------------------------------------------

class TestSplitPreamble:
    """Test splitting Rocq source into preamble (imports) and body."""

    def test_simple_split(self):
        source = "Require Import Arith.\n\nTheorem t : True.\nProof. exact I. Qed."
        preamble, body = _split_preamble(source)
        assert "Require Import Arith." in preamble
        assert "Theorem t" in body

    def test_from_import(self):
        source = "From Coq Require Import Arith.\nTheorem t : True.\n"
        preamble, body = _split_preamble(source)
        assert "From Coq" in preamble
        assert "Theorem" in body

    def test_multiline_from_import(self):
        """Multi-line From ... Require Import with continuation lines."""
        source = (
            "From Coq Require Import\n"
            "  Arith\n"
            "  Lia.\n\n"
            "Theorem t : True.\n"
        )
        preamble, body = _split_preamble(source)
        assert "From Coq" in preamble
        assert "Arith" in preamble
        assert "Lia." in preamble
        assert "Theorem" in body

    def test_notation_in_preamble(self):
        source = (
            'Require Import Reals.\n'
            'Notation "x ^ y" := (Rpower x y).\n'
            'Theorem t : True.\n'
        )
        preamble, body = _split_preamble(source)
        assert "Notation" in preamble
        assert "Theorem" in body

    def test_multiline_comment(self):
        """Multi-line comments spanning multiple lines stay in preamble."""
        source = (
            "Require Import Arith.\n"
            "(* This is\n"
            "   a multi-line\n"
            "   comment *)\n"
            "Theorem t : True.\n"
        )
        preamble, body = _split_preamble(source)
        assert "comment *)" in preamble
        assert "Theorem" in body

    def test_all_preamble(self):
        """Source consisting only of import lines -> empty body."""
        source = "Require Import Arith.\nRequire Import Lia."
        preamble, body = _split_preamble(source)
        assert "Arith" in preamble
        assert "Lia" in preamble
        assert body == ""

    def test_empty_source(self):
        preamble, body = _split_preamble("")
        assert preamble == ""
        assert body == ""

    def test_set_and_open(self):
        source = (
            "Set Implicit Arguments.\n"
            "Open Scope nat_scope.\n"
            "Theorem t : True.\n"
        )
        preamble, body = _split_preamble(source)
        assert "Set Implicit" in preamble
        assert "Open Scope" in preamble
        assert "Theorem" in body

    def test_attribute_line(self):
        """Lines starting with #[...] (attributes) belong to preamble."""
        source = "#[global] Hint Resolve eq_refl : core.\nTheorem t : True.\n"
        preamble, body = _split_preamble(source)
        assert "#[global]" in preamble
        assert "Theorem" in body

    def test_single_line_comment_in_preamble(self):
        """A comment between imports stays in preamble."""
        source = (
            "Require Import Arith.\n"
            "(* helper imports *)\n"
            "Require Import Lia.\n"
            "Theorem t : True.\n"
        )
        preamble, body = _split_preamble(source)
        assert "(* helper imports *)" in preamble
        assert "Require Import Lia." in preamble
        assert "Theorem" in body

    def test_blank_lines_between_imports(self):
        """Blank lines between imports remain in preamble."""
        source = (
            "Require Import Arith.\n"
            "\n"
            "Require Import Lia.\n"
            "\n"
            "Theorem t : True.\n"
        )
        preamble, body = _split_preamble(source)
        assert "Arith" in preamble
        assert "Lia" in preamble
        assert "Theorem" in body

    def test_no_preamble(self):
        """Source starting directly with a Theorem has empty preamble."""
        source = "Theorem t : True.\nProof. exact I. Qed."
        preamble, body = _split_preamble(source)
        assert preamble == ""
        assert "Theorem" in body


# ---------------------------------------------------------------------------
# _clean_problem_statement
# ---------------------------------------------------------------------------

class TestCleanProblemStatement:
    """Test stripping trailing Admitted/Abort/admit from problem statements."""

    def test_trailing_admitted(self):
        cleaned = _clean_problem_statement("Theorem t : True.\nAdmitted.")
        assert "Theorem t : True." in cleaned
        assert "Admitted" not in cleaned

    def test_trailing_abort(self):
        cleaned = _clean_problem_statement("Theorem t : True.\nAbort.")
        assert "Abort" not in cleaned
        assert "Theorem t : True." in cleaned

    def test_trailing_admit(self):
        cleaned = _clean_problem_statement("Theorem t : True.\nadmit.")
        assert "admit" not in cleaned

    def test_admitted_with_spaces(self):
        """Admitted with optional spaces before/after the dot."""
        cleaned = _clean_problem_statement("Theorem t : True.\n  Admitted  .")
        assert "Admitted" not in cleaned

    def test_admitted_in_middle_preserved(self):
        """Only strip the TRAILING Admitted, not one in the middle."""
        source = "Lemma h : True. Admitted.\nTheorem t : True.\nAdmitted."
        cleaned = _clean_problem_statement(source)
        # The trailing Admitted should be stripped; the middle one is kept
        # because the regex only matches at end-of-string ($).
        assert "Theorem t : True." in cleaned
        # The middle "Admitted" from the helper should survive
        assert "Lemma h : True. Admitted." in cleaned

    def test_no_trailing_admitted(self):
        """Source without trailing Admitted stays unchanged."""
        source = "Theorem t : True.\nProof. exact I. Qed."
        cleaned = _clean_problem_statement(source)
        assert cleaned == source

    def test_empty_string(self):
        assert _clean_problem_statement("") == ""


# ---------------------------------------------------------------------------
# Axiom classification
# ---------------------------------------------------------------------------

class TestAxiomClassification:
    """Test _is_standard_axiom for correct accept/reject decisions.

    The axiom spoofing tests are CRITICAL for soundness.
    """

    # --- Standard axioms: should be ACCEPTED ---

    def test_qualified_standard_coq_prefix(self):
        assert _is_standard_axiom("Coq.Logic.Classical_Prop.classic") is True

    def test_qualified_rocq_prefix(self):
        assert _is_standard_axiom("Rocq.Logic.Classical_Prop.classic") is True

    def test_qualified_stdlib_prefix(self):
        assert _is_standard_axiom("Stdlib.Logic.Classical_Prop.classic") is True

    def test_unqualified_standard(self):
        assert _is_standard_axiom("classic") is True

    def test_unqualified_functional_extensionality(self):
        assert _is_standard_axiom("functional_extensionality_dep") is True

    def test_unqualified_eq_rect_eq(self):
        assert _is_standard_axiom("eq_rect_eq") is True

    def test_reals_axiom_qualified(self):
        assert _is_standard_axiom("Coq.Reals.Raxioms.completeness") is True

    def test_reals_axiom_unqualified(self):
        assert _is_standard_axiom("completeness") is True

    def test_functional_extensionality_qualified(self):
        name = "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep"
        assert _is_standard_axiom(name) is True

    def test_epsilon_accepted(self):
        assert _is_standard_axiom("epsilon") is True

    def test_proof_irrelevance(self):
        assert _is_standard_axiom("proof_irrelevance") is True

    # --- SPOOFED axioms: must be REJECTED ---

    def test_spoofed_m_classic_rejected(self):
        """CRITICAL: M.classic (user module) must be REJECTED."""
        assert _is_standard_axiom("M.classic") is False

    def test_spoofed_test_classic_rejected(self):
        """Test.classic (user module) must be REJECTED."""
        assert _is_standard_axiom("Test.classic") is False

    def test_spoofed_mymod_classic_rejected(self):
        """MyModule.classic must be REJECTED."""
        assert _is_standard_axiom("MyModule.classic") is False

    def test_spoofed_nested_module_rejected(self):
        """Deeply nested user module must be REJECTED."""
        assert _is_standard_axiom("A.B.C.classic") is False

    # --- Unknown axioms: must be REJECTED ---

    def test_unqualified_unknown(self):
        assert _is_standard_axiom("my_cheat_axiom") is False

    def test_qualified_unknown(self):
        assert _is_standard_axiom("my_module.my_axiom") is False

    def test_random_user_axiom(self):
        assert _is_standard_axiom("Foo.Bar.baz") is False

    # --- Helper: short name extraction ---

    def test_axiom_short_name_qualified(self):
        assert _axiom_short_name("Coq.Logic.Classical_Prop.classic") == "classic"

    def test_axiom_short_name_unqualified(self):
        assert _axiom_short_name("classic") == "classic"

    def test_axiom_short_name_single_dot(self):
        assert _axiom_short_name("M.classic") == "classic"


# ---------------------------------------------------------------------------
# Print Assumptions parser
# ---------------------------------------------------------------------------

class TestParseAssumptions:
    """Test _parse_assumptions_raw and parse_and_classify_assumptions."""

    def test_closed(self):
        stdout = "Closed under the global context\n"
        assert _parse_assumptions_raw(stdout) == []

    def test_single_axiom(self):
        stdout = (
            "Axioms:\n"
            "Coq.Logic.Classical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
        )
        result = _parse_assumptions_raw(stdout)
        assert len(result) == 1
        assert result[0][0] == "Coq.Logic.Classical_Prop.classic"
        assert "forall" in result[0][1]

    def test_multiple_axioms(self):
        stdout = (
            "Axioms:\n"
            "classic : forall P : Prop, P \\/ ~ P\n"
            "completeness : forall E : R -> Prop, bound E -> {m : R | is_lub E m}\n"
        )
        result = _parse_assumptions_raw(stdout)
        assert len(result) == 2
        names = {r[0] for r in result}
        assert "classic" in names
        assert "completeness" in names

    def test_multiline_type(self):
        stdout = (
            "Axioms:\n"
            "Coq.Reals.Raxioms.completeness\n"
            "  : forall E : R -> Prop,\n"
            "    bound E -> (exists x : R, E x) ->\n"
            "    {m : R | is_lub E m}\n"
        )
        result = _parse_assumptions_raw(stdout)
        assert len(result) == 1
        assert result[0][0] == "Coq.Reals.Raxioms.completeness"
        assert "forall" in result[0][1]

    def test_empty_stdout(self):
        assert _parse_assumptions_raw("") == []

    def test_no_axioms_header_with_closed(self):
        """Output that contains both noise and 'Closed under...'."""
        stdout = "add_0_r : \nClosed under the global context\n"
        assert _parse_assumptions_raw(stdout) == []

    # --- parse_and_classify_assumptions (higher-level) ---

    def test_classify_closed(self):
        stdout = "Closed under the global context\n"
        verdict, details = parse_and_classify_assumptions(stdout)
        assert verdict == "closed"
        assert details == {}

    def test_classify_standard_only(self):
        stdout = (
            "Axioms:\n"
            "Coq.Logic.Classical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
        )
        verdict, details = parse_and_classify_assumptions(stdout)
        assert verdict == "standard_only"
        assert "standard" in details
        assert len(details["standard"]) == 1

    def test_classify_suspicious(self):
        stdout = (
            "Axioms:\n"
            "M.classic : False\n"
        )
        verdict, details = parse_and_classify_assumptions(stdout)
        assert verdict == "suspicious"
        assert "suspicious" in details
        assert "M.classic" in details["suspicious_names"]

    def test_classify_mixed(self):
        """Mix of standard and suspicious axioms."""
        stdout = (
            "Axioms:\n"
            "Coq.Logic.Classical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
            "M.cheat : False\n"
        )
        verdict, details = parse_and_classify_assumptions(stdout)
        assert verdict == "suspicious"
        assert len(details["standard"]) == 1
        assert len(details["suspicious"]) == 1
        assert "M.cheat" in details["suspicious_names"]


# ---------------------------------------------------------------------------
# build_verification_source
# ---------------------------------------------------------------------------

class TestBuildVerificationSource:
    """Test that the Module M. template is constructed correctly."""

    def test_contains_module_wrapper(self):
        source = build_verification_source(
            proof="Require Import Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        assert "Module M." in source
        assert "End M." in source

    def test_contains_apply(self):
        source = build_verification_source(
            proof="Theorem foo : True. Proof. exact I. Qed.",
            problem_name="foo",
            problem_statement="Theorem foo : True.\nAdmitted.",
        )
        assert "apply M.foo" in source

    def test_contains_print_assumptions(self):
        source = build_verification_source(
            proof="Theorem bar : True. Proof. exact I. Qed.",
            problem_name="bar",
            problem_statement="Theorem bar : True.\nAdmitted.",
        )
        assert "Print Assumptions bar." in source

    def test_preamble_outside_module(self):
        """Imports should appear before Module M., not inside it."""
        source = build_verification_source(
            proof="Require Import Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        module_pos = source.index("Module M.")
        require_pos = source.index("Require Import Arith.")
        assert require_pos < module_pos

    def test_strips_trailing_admitted(self):
        source = build_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        # The problem statement should appear outside the module WITHOUT Admitted
        # Find the text after "End M."
        after_end = source[source.index("End M."):]
        assert "Admitted" not in after_end

    def test_braces_in_proof_safe(self):
        """Braces { } in proof text must survive template construction."""
        proof = (
            "Require Import Arith.\n"
            "Theorem t : forall n m, n + m = m + n.\n"
            "Proof. intros. { apply Nat.add_comm. } Qed."
        )
        source = build_verification_source(
            proof=proof,
            problem_name="t",
            problem_statement="Theorem t : forall n m, n + m = m + n.\nAdmitted.",
        )
        assert "{ apply Nat.add_comm. }" in source


# =========================================================================
# PART B: Integration tests (require coqc)
# =========================================================================

# We import rocq_verify at the top level so monkeypatch tests work,
# but skip all integration classes if coqc is not available.
from rocq_mcp.server import rocq_verify  # noqa: E402


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifySuccess:
    """Valid proofs that should pass verification."""

    def test_valid_proof(self, workspace, simple_proof, simple_problem_statement):
        result = rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is True

    def test_classical_proof_accepted(
        self, workspace, classical_proof, classical_problem
    ):
        """Proof using classical logic should be accepted with axiom listed."""
        result = rocq_verify(
            proof=classical_proof,
            problem_name="lem_example",
            problem_statement=classical_problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True
        # Should list classic as a standard axiom
        if (
            "assumptions" in result
            and result["assumptions"] != "Closed under the global context"
        ):
            assert any("classic" in a for a in result["assumptions"])

    def test_braces_in_proof(self, workspace, braces_proof):
        """Proofs with { } subgoal braces should verify correctly."""
        problem = (
            "Require Import Arith.\n\n"
            "Theorem add_comm_example : forall n m : nat, n + m = m + n.\n"
            "Admitted.\n"
        )
        result = rocq_verify(
            proof=braces_proof,
            problem_name="add_comm_example",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True

    def test_multiline_import_proof(
        self, workspace, multiline_import_proof
    ):
        """Proof with multi-line From...Require Import should verify."""
        problem = (
            "From Coq Require Import\n"
            "  Arith\n"
            "  Lia.\n\n"
            "Theorem test : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = rocq_verify(
            proof=multiline_import_proof,
            problem_name="test",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifyRejection:
    """Proofs that must be REJECTED by verification."""

    def test_type_redefinition(
        self, workspace, cheating_proof, simple_problem_statement
    ):
        """Redefining nat as bool must be caught."""
        result = rocq_verify(
            proof=cheating_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    def test_axiom_spoofing(self, workspace, axiom_spoofing_proof):
        """CRITICAL: user-defined 'Axiom classic : False' must be rejected.

        Inside Module M., this becomes M.classic which is NOT a standard library
        axiom. The _is_standard_axiom check must reject the M. prefix.
        """
        problem = "Theorem anything : 1 = 2.\nAdmitted.\n"
        result = rocq_verify(
            proof=axiom_spoofing_proof,
            problem_name="anything",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    def test_admitted_inside_module(
        self, workspace, admitted_proof, simple_problem_statement
    ):
        """Proof using an Admitted helper lemma must be rejected."""
        result = rocq_verify(
            proof=admitted_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        # Should either have suspicious assumptions or a compilation error
        assert "assumptions" in result or "error" in result

    def test_wrong_theorem_name(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """Using a wrong problem_name must fail (M.wrong_name not found)."""
        result = rocq_verify(
            proof=simple_proof,
            problem_name="wrong_name",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifyInputValidation:
    """Input validation checks."""

    def test_dotted_problem_name(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """Qualified names (containing dots) must be rejected early."""
        result = rocq_verify(
            proof=simple_proof,
            problem_name="Nat.add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "unqualified" in result["error"].lower()

    def test_bad_workspace(self, simple_proof, simple_problem_statement):
        """Non-existent workspace should return a clear error."""
        result = rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace="/nonexistent/path/xyz",
        )
        assert result["verified"] is False
        assert "error" in result

    def test_timeout(self, workspace, timeout_proof):
        """Diverging proof inside verification template should timeout."""
        problem = "Theorem loop : True.\nAdmitted.\n"
        result = rocq_verify(
            proof=timeout_proof,
            problem_name="loop",
            problem_statement=problem,
            workspace=str(workspace),
            timeout=3,
        )
        assert result["verified"] is False
        assert "timed out" in result["error"].lower()

    def test_oversized_proof(self, workspace):
        """Proof exceeding max size should be rejected."""
        result = rocq_verify(
            proof="x" * 2_000_000,
            problem_name="test",
            problem_statement="Theorem test : True.\nAdmitted.",
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "size" in result["error"].lower()


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifyCleanup:
    """Verification should not leave temp files behind."""

    def test_no_artifacts_left(
        self, workspace, simple_proof, simple_problem_statement
    ):
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_failure(
        self, workspace, cheating_proof, simple_problem_statement
    ):
        """Even when verification fails, no temp files should remain."""
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_verify(
            proof=cheating_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"
