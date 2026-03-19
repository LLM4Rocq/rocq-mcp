"""Tests for rocq_verify tool and verification helpers in verify.py.

Part A: Unit tests for verify.py helpers (NO coqc needed)
    - TestCleanProblemStatement
    - TestAxiomClassification
    - TestParseAssumptions
    - TestBuildVerificationSource
    - TestGateFunctions
    - TestClassifyTocDetail
    - TestVerificationHint
    - TestStripSharedDefs
    - TestBuildSharedDefsVerificationSource
    - TestVerifyInputSanitization

Part B: Integration tests for rocq_verify (require coqc)
    - TestVerifySuccess
    - TestVerifyRejection
    - TestVerifyInputValidation
    - TestVerifyCleanup
    - TestSharedDefsIntegration
"""

from __future__ import annotations

import glob as glob_mod

import pytest

from tests.conftest import COQC_AVAILABLE
from rocq_mcp.verify import (
    _clean_problem_statement,
    _is_standard_axiom,
    _axiom_short_name,
    _parse_assumptions_raw,
    _SHARED_DEF_DETAILS,
    _strip_shared_defs,
    build_shared_defs_verification_source,
    classify_toc_detail,
    DefCategory,
    DefinitionInfo,
    parse_and_classify_assumptions,
    ProblemStructure,
    build_verification_source,
    verification_hint,
)

# =========================================================================
# PART A: Unit tests (no coqc needed)
# =========================================================================


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

    def test_trailing_give_up(self):
        cleaned = _clean_problem_statement("Theorem t : True.\ngive_up.")
        assert "give_up" not in cleaned
        assert "Theorem t : True." in cleaned

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

    def test_proof_admitted_no_double_proof(self):
        """Stripping 'Proof.\\nAdmitted.' must also strip trailing Proof."""
        cleaned = _clean_problem_statement("Theorem t : True.\nProof.\nAdmitted.")
        assert not cleaned.endswith("Proof.")
        assert "Theorem t : True." in cleaned


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

    # --- Dedekind reals: module-qualified (no stdlib prefix) ---

    def test_dedekind_sig_forall_dec(self):
        """Print Assumptions outputs this without Stdlib. prefix."""
        assert _is_standard_axiom("ClassicalDedekindReals.sig_forall_dec") is True

    def test_dedekind_sig_not_dec(self):
        """sig_not_dec is used by completeness."""
        assert _is_standard_axiom("ClassicalDedekindReals.sig_not_dec") is True

    def test_dedekind_sig_not_dec_unqualified(self):
        assert _is_standard_axiom("sig_not_dec") is True

    def test_functional_extensionality_module_qualified(self):
        """Print Assumptions outputs this without Stdlib. prefix."""
        assert (
            _is_standard_axiom("FunctionalExtensionality.functional_extensionality_dep")
            is True
        )

    def test_eqdep_eq_rect_eq_module_qualified(self):
        """Print Assumptions outputs this with Eqdep.Eq_rect_eq. prefix."""
        assert _is_standard_axiom("Eqdep.Eq_rect_eq.eq_rect_eq") is True

    def test_classical_prop_classic(self):
        """Classical_Prop.classic (module-qualified, no Stdlib prefix)."""
        assert _is_standard_axiom("Classical_Prop.classic") is True

    def test_classical_epsilon_module_qualified(self):
        assert _is_standard_axiom("ClassicalEpsilon.epsilon") is True

    def test_eq_rect_eq_without_eqdep_prefix(self):
        """From Stdlib Require Import Eqdep outputs Eq_rect_eq.eq_rect_eq (no Eqdep. prefix)."""
        assert _is_standard_axiom("Eq_rect_eq.eq_rect_eq") is True

    def test_raxioms_module_qualified(self):
        assert _is_standard_axiom("Raxioms.completeness") is True

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

    # --- Ensembles axiom: should be ACCEPTED ---

    def test_extensionality_ensembles_accepted(self):
        assert _is_standard_axiom("Extensionality_Ensembles") is True

    def test_ensembles_qualified_accepted(self):
        assert _is_standard_axiom("Coq.Sets.Ensembles.Extensionality_Ensembles") is True

    def test_ensembles_module_prefix_accepted(self):
        assert _is_standard_axiom("Ensembles.Extensionality_Ensembles") is True

    def test_user_extensionality_ensembles_rejected(self):
        """User-qualified Ensembles axiom should be rejected."""
        assert _is_standard_axiom("M.Extensionality_Ensembles") is False


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

    def test_name_colon_on_same_line_type_on_next(self):
        """Dedekind axioms use 'name :\\n  type' format."""
        stdout = (
            "Axioms:\n"
            "ClassicalDedekindReals.sig_forall_dec :\n"
            "  forall P : nat -> Prop,\n"
            "  (forall n : nat, {P n} + {~ P n}) ->\n"
            "  {n : nat | ~ P n} + {forall n : nat, P n}\n"
        )
        result = _parse_assumptions_raw(stdout)
        assert len(result) == 1
        assert result[0][0] == "ClassicalDedekindReals.sig_forall_dec"
        assert "forall" in result[0][1]

    def test_dedekind_reals_classified_standard(self):
        """Full Dedekind reals axiom set must be classified as standard."""
        stdout = (
            "Axioms:\n"
            "ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}\n"
            "ClassicalDedekindReals.sig_forall_dec :\n"
            "  forall P : nat -> Prop,\n"
            "  (forall n : nat, {P n} + {~ P n}) ->\n"
            "  {n : nat | ~ P n} + {forall n : nat, P n}\n"
            "FunctionalExtensionality.functional_extensionality_dep :\n"
            "  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),\n"
            "  (forall x : A, f x = g x) -> f = g\n"
        )
        verdict, details = parse_and_classify_assumptions(stdout)
        assert verdict == "standard_only"
        assert len(details["standard"]) == 3

    def test_empty_stdout(self):
        assert _parse_assumptions_raw("") == []

    def test_no_axioms_header_with_closed(self):
        """Output that contains both noise and 'Closed under...'."""
        stdout = "add_0_r : \nClosed under the global context\n"
        assert _parse_assumptions_raw(stdout) == []

    def test_closed_substring_in_type_not_fooled(self):
        """An axiom whose type contains the 'Closed under...' string must NOT be treated as closed."""
        stdout = 'cheat : let _ := "Closed under the global context" in False\n'
        result = _parse_assumptions_raw(stdout)
        assert len(result) == 1
        assert result[0][0] == "cheat"

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
        stdout = "Axioms:\n" "M.classic : False\n"
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

    def test_entire_proof_inside_module(self):
        """Entire proof (including imports) should be inside Module M."""
        source = build_verification_source(
            proof="Require Import Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        module_pos = source.index("Module M.")
        end_pos = source.index("End M.")
        require_pos = source.index("Require Import Arith.")
        assert module_pos < require_pos < end_pos

    def test_strips_trailing_admitted(self):
        source = build_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        # The problem statement should appear outside the module WITHOUT Admitted
        # Find the text after "End M."
        after_end = source[source.index("End M.") :]
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


# ---------------------------------------------------------------------------
# Gate functions (_has_definition_keywords)
# ---------------------------------------------------------------------------


class TestGateFunctions:
    """Test the gate functions that decide Phase 2 fallback eligibility."""

    def test_has_definition_keywords_inductive(self):
        from rocq_mcp.server import _has_definition_keywords

        assert _has_definition_keywords("Inductive color := Red.")

    def test_has_definition_keywords_coinductive(self):
        from rocq_mcp.server import _has_definition_keywords

        assert _has_definition_keywords(
            "CoInductive stream := Cons : nat -> stream -> stream."
        )

    def test_has_definition_keywords_record(self):
        from rocq_mcp.server import _has_definition_keywords

        assert _has_definition_keywords("Record point := { x : nat; y : nat }.")

    def test_has_definition_keywords_fixpoint(self):
        from rocq_mcp.server import _has_definition_keywords

        assert _has_definition_keywords("Fixpoint f (n : nat) := n.")

    def test_has_definition_keywords_no_match(self):
        from rocq_mcp.server import _has_definition_keywords

        assert not _has_definition_keywords("Theorem foo : True.\nAdmitted.")


# ---------------------------------------------------------------------------
# classify_toc_detail
# ---------------------------------------------------------------------------


class TestClassifyTocDetail:
    """Test classification of coq-lsp toc detail strings."""

    def test_inductive(self):
        assert classify_toc_detail("Inductive") == DefCategory.SHARED_DEF

    def test_theorem(self):
        assert classify_toc_detail("Theorem") == DefCategory.THEOREM

    def test_notation(self):
        assert classify_toc_detail("Notation") == DefCategory.NOTATION

    def test_section(self):
        assert classify_toc_detail("Section") == DefCategory.OTHER

    def test_all_shared_defs(self):
        for detail in _SHARED_DEF_DETAILS:
            assert (
                classify_toc_detail(detail) == DefCategory.SHARED_DEF
            ), f"{detail} not classified as SHARED_DEF"

    def test_lemma(self):
        assert classify_toc_detail("Lemma") == DefCategory.THEOREM

    def test_infix(self):
        assert classify_toc_detail("Infix") == DefCategory.NOTATION

    def test_unknown(self):
        assert classify_toc_detail("SomethingUnknown") == DefCategory.OTHER


# ---------------------------------------------------------------------------
# verification_hint
# ---------------------------------------------------------------------------


class TestVerificationHint:
    """Test human-readable hints from verification failures."""

    def test_unification_with_m_prefix_hint(self):
        """Unification error mentioning M. -> Module M boundary hint."""
        hint = verification_hint("Unable to unify M.foo with foo")
        assert "Module M" in hint

    def test_cannot_apply_with_m_prefix_hint(self):
        """Cannot apply error mentioning M. -> Module M boundary hint."""
        hint = verification_hint("Cannot apply M.foo")
        assert "Module M" in hint

    def test_unification_without_m_prefix_hint(self):
        """Unification error without M. -> generic type mismatch hint."""
        hint = verification_hint('Unable to unify "nat" with "bool"')
        assert "type mismatch" in hint.lower() or "Type mismatch" in hint

    def test_cannot_apply_without_m_prefix_hint(self):
        """Cannot apply error without M. -> generic type mismatch hint."""
        hint = verification_hint("Cannot apply foo_lemma")
        assert "type mismatch" in hint.lower() or "Type mismatch" in hint

    def test_not_found_hint(self):
        hint = verification_hint("M.foo not found in the current environment")
        assert "name" in hint.lower() or "match" in hint.lower()

    def test_syntax_error_hint(self):
        hint = verification_hint("Syntax error: unexpected token")
        assert "syntax" in hint.lower()

    def test_timeout_hint(self):
        hint = verification_hint("Timeout in tactic evaluation")
        assert "timeout" in hint.lower() or "timed out" in hint.lower()

    def test_default_hint(self):
        hint = verification_hint("Some unknown error occurred")
        assert len(hint) > 0  # Should return something


# ---------------------------------------------------------------------------
# _strip_shared_defs and build_shared_defs_verification_source
# ---------------------------------------------------------------------------


class TestStripSharedDefs:
    """Test stripping shared definitions from proof text."""

    def test_strip_single_definition(self):
        proof = (
            "From Stdlib Require Import List.\n"
            "Definition state := list nat.\n"
            "Theorem foo : state = state.\n"
            "Proof. reflexivity. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state"})
        assert "Definition state" not in result
        assert "From Stdlib Require Import List." in result
        assert "Theorem foo" in result

    def test_strip_inductive(self):
        proof = (
            "Inductive color :=\n"
            "  | Red\n"
            "  | Green\n"
            "  | Blue.\n"
            "Theorem foo : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"color"})
        assert "Inductive color" not in result
        assert "Red" not in result
        assert "Theorem foo" in result

    def test_strip_multiple(self):
        proof = (
            "Definition state := list nat.\n"
            "Inductive color := Red | Green | Blue.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state", "color"})
        assert "Definition state" not in result
        assert "Inductive color" not in result
        assert "Theorem foo" in result

    def test_no_strip_non_matching(self):
        proof = (
            "Definition helper := 42.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state"})
        assert "Definition helper" in result
        assert "Theorem foo" in result

    def test_empty_shared_names(self):
        proof = "Theorem foo : True.\nProof. exact I. Qed.\n"
        result = _strip_shared_defs(proof, set())
        assert result == proof

    def test_preserves_helper_definitions(self):
        """Helper defs not in shared_names should be preserved."""
        proof = (
            "Definition shared := 0.\n"
            "Definition helper := shared + 1.\n"
            "Theorem foo : helper = 1.\n"
            "Proof. reflexivity. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"shared"})
        assert "Definition shared" not in result
        assert "Definition helper" in result
        assert "Theorem foo" in result

    def test_strip_fixpoint(self):
        proof = (
            "Fixpoint f (n : nat) : nat :=\n"
            "  match n with\n"
            "  | O => O\n"
            "  | S n' => S (f n')\n"
            "  end.\n"
            "Theorem foo : f 0 = 0.\n"
            "Proof. reflexivity. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"f"})
        assert "Fixpoint f" not in result
        assert "Theorem foo" in result

    def test_strip_record(self):
        proof = (
            "Record point := { x : nat; y : nat }.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"point"})
        assert "Record point" not in result
        assert "Theorem foo" in result

    def test_dot_in_qualified_name_not_confused(self):
        """Dots in Nat.add etc. should not end the sentence early."""
        proof = (
            "Definition myval := Nat.add 1 2.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"myval"})
        assert "Definition myval" not in result
        assert "Nat.add" not in result
        assert "Theorem foo" in result

    def test_strip_name_with_prime(self):
        """Names with primes (e.g., x') may not be stripped due to \\b word boundary.

        The prime character is not a word character, so \\b after x' doesn't
        match when followed by whitespace.  This documents current behavior:
        _strip_shared_defs does NOT strip definitions with primed names.
        """
        proof = "Definition x' := 0.\n" "Theorem foo : True.\n" "Proof. exact I. Qed.\n"
        result = _strip_shared_defs(proof, {"x'"})
        # Due to \b limitation, primed names are NOT stripped (known limitation)
        assert "Definition x'" in result
        assert "Theorem foo" in result

    def test_strip_name_with_digits(self):
        """Names with digits (e.g., state2) should be stripped correctly."""
        proof = (
            "Definition state2 := 0.\n" "Theorem foo : True.\n" "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state2"})
        assert "Definition state2" not in result
        assert "Theorem foo" in result

    def test_strip_def_with_inner_period_space(self):
        """Dot inside qualified name (Nat.add) should not terminate the sentence."""
        proof = (
            "Definition f := Nat.add 1 2.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"f"})
        assert "Definition f" not in result
        assert "Nat.add" not in result
        assert "Theorem foo" in result

    def test_strip_coinductive(self):
        """CoInductive definitions should be stripped correctly."""
        proof = (
            "CoInductive stream := Cons : nat -> stream -> stream.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"stream"})
        assert "CoInductive stream" not in result
        assert "Theorem foo" in result

    def test_strip_all_occurrences(self):
        """If a definition name appears twice, both should be stripped (count=0)."""
        proof = (
            "Definition state := list nat.\n"
            "Definition state := list nat.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state"})
        # _strip_shared_defs uses count=0 to strip ALL occurrences,
        # preventing adversaries from hiding decoys in comments
        assert result.count("Definition state") == 0
        assert "Theorem foo" in result


class TestBuildSharedDefsVerificationSource:
    """Test the shared-defs verification template builder."""

    def _make_structure(
        self,
        preamble: str = "",
        defs: list[tuple[str, str, str]] | None = None,
        theorem_source: str = "Theorem foo : True.",
        full_source: str = "",
    ) -> ProblemStructure:
        definitions = []
        if defs:
            for name, detail, source in defs:
                definitions.append(
                    DefinitionInfo(
                        name=name,
                        detail=detail,
                        category=DefCategory.SHARED_DEF,
                        source_text=source,
                        start_line=0,
                        end_line=0,
                    )
                )
        return ProblemStructure(
            preamble_source=preamble,
            definitions=definitions,
            theorem_source=theorem_source,
            theorem_name="foo",
            has_shared_defs=bool(definitions),
            full_source=full_source or theorem_source,
        )

    def test_defs_outside_stripped_inside(self):
        """Shared defs appear outside Module M, stripped from proof inside."""
        structure = self._make_structure(
            preamble="From Stdlib Require Import List.",
            defs=[("state", "Definition", "Definition state := list nat.")],
            theorem_source="Theorem foo : state = state.",
            full_source=(
                "From Stdlib Require Import List.\n"
                "Definition state := list nat.\n"
                "Theorem foo : state = state.\nAdmitted."
            ),
        )
        proof = (
            "From Stdlib Require Import List.\n"
            "Definition state := list nat.\n"
            "Theorem foo : state = state.\n"
            "Proof. reflexivity. Qed.\n"
        )
        source = build_shared_defs_verification_source(proof, "foo", structure)

        # Shared def should appear ONCE (outside Module M), not inside
        assert source.count("Definition state") == 1
        # The one occurrence should be before Module M
        idx_def = source.index("Definition state")
        idx_module = source.index("Module M.")
        assert idx_def < idx_module
        # Proof should be inside Module M
        assert "Module M." in source
        assert "End M." in source
        assert "Theorem foo : state = state." in source
        assert "apply M.foo" in source

    def test_inductive_stripped_from_proof(self):
        """Inductive types should be stripped from the proof inside Module M."""
        structure = self._make_structure(
            defs=[("color", "Inductive", "Inductive color := Red | Green | Blue.")],
            theorem_source="Theorem foo : forall c : color, c = c.",
            full_source=(
                "Inductive color := Red | Green | Blue.\n"
                "Theorem foo : forall c : color, c = c.\nAdmitted."
            ),
        )
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem foo : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )
        source = build_shared_defs_verification_source(proof, "foo", structure)

        # Inductive should appear once (outside Module M)
        assert source.count("Inductive color") == 1
        idx_ind = source.index("Inductive color")
        idx_module = source.index("Module M.")
        assert idx_ind < idx_module

    def test_helpers_preserved_inside_module(self):
        """Definitions not in shared defs should remain inside Module M."""
        structure = self._make_structure(
            defs=[("state", "Definition", "Definition state := list nat.")],
            theorem_source="Theorem foo : True.",
            full_source=(
                "Definition state := list nat.\n" "Theorem foo : True.\nAdmitted."
            ),
        )
        proof = (
            "Definition state := list nat.\n"
            "Definition helper := 42.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        source = build_shared_defs_verification_source(proof, "foo", structure)

        # helper should be inside Module M
        assert "Definition helper" in source
        idx_helper = source.index("Definition helper")
        idx_module = source.index("Module M.")
        idx_end = source.index("End M.")
        assert idx_module < idx_helper < idx_end

    def test_end_m_in_proof_rejected_shared_defs(self):
        """End M. in proof must be rejected even in shared-defs template."""
        structure = self._make_structure(
            defs=[("state", "Definition", "Definition state := list nat.")],
            theorem_source="Theorem foo : True.",
            full_source=(
                "Definition state := list nat.\n" "Theorem foo : True.\nAdmitted."
            ),
        )
        proof = (
            "Definition state := list nat.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
            "End M.\n"
            "Axiom cheat : False.\n"
            "Module M.\n"
        )
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_shared_defs_verification_source(proof, "foo", structure)

    def test_forbidden_in_full_source_rejected(self):
        """Forbidden commands in the full_source (problem statement) must be rejected."""
        structure = self._make_structure(
            full_source='Redirect "/tmp/evil" Print nat.\nTheorem foo : True.\nAdmitted.',
        )
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_shared_defs_verification_source(
                "Theorem foo : True.\nProof. exact I. Qed.", "foo", structure
            )


# ---------------------------------------------------------------------------
# Input sanitization (injection attacks)
# ---------------------------------------------------------------------------


class TestVerifyInputSanitization:
    """Test that malicious inputs are rejected."""

    def test_problem_name_with_newline(self):
        """Newlines in problem_name must be rejected by build_verification_source."""
        # The server-level regex rejects this before build_verification_source
        # is ever called, but let's verify the template isn't abusable either.
        # build_verification_source doesn't validate problem_name itself,
        # so we test via the server's rocq_verify which does the regex check.
        # For a pure unit test, we verify the regex pattern rejects it.
        import re

        pattern = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
        assert pattern.match("add_0_r\nAxiom cheat : False") is None

    def test_problem_name_with_spaces(self):
        import re

        pattern = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
        assert pattern.match("add_0_r Axiom cheat") is None

    def test_problem_name_with_semicolon(self):
        import re

        pattern = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
        assert pattern.match("add_0_r;evil") is None

    def test_problem_name_valid_identifier(self):
        """A valid Rocq identifier should work."""
        source = build_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        assert "Module M." in source

    def test_problem_name_with_prime(self):
        """Primes are valid in Rocq identifiers: t'"""
        source = build_verification_source(
            proof="Theorem t' : True. Proof. exact I. Qed.",
            problem_name="t'",
            problem_statement="Theorem t' : True.\nAdmitted.",
        )
        assert "M.t'" in source

    def test_redirect_in_proof_rejected(self):
        """Proof containing Redirect command must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Redirect "/tmp/evil" Print nat.\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_extraction_in_proof_rejected(self):
        """Proof containing Extraction to file must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Require Import Extraction.\nExtraction "/tmp/evil.ml" nat.\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_drop_in_proof_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Drop.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_separate_extraction_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Separate Extraction nat.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_cd_in_proof_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Cd "/tmp".\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_load_in_proof_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Load "/tmp/evil".\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_declare_ml_module_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Declare ML Module "evil".\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_unset_guard_checking_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Unset Guard Checking.\nFixpoint loop (n : nat) : False := loop n.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_unset_positivity_checking_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Unset Positivity Checking.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_unset_universe_checking_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Unset Universe Checking.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_bypass_check_attribute_rejected(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="#[bypass_check(guard)]\nFixpoint loop (n : nat) : False := loop n.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_end_m_in_proof_rejected(self):
        """Proof containing 'End M.' to escape module sandbox must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.\nEnd M.\nAxiom cheat : False.\nModule M.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_end_m_with_extra_whitespace_rejected(self):
        """'End  M .' with extra whitespace must also be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.\nEnd  M .",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_end_my_module_not_rejected(self):
        """'End MyModule.' must NOT be rejected -- only 'End M.' is forbidden."""
        source = build_verification_source(
            proof="Module Inner.\nEnd Inner.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        assert "Module M." in source

    def test_reset_in_proof_rejected(self):
        """Proof containing Reset must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Reset Initial.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_back_in_proof_rejected(self):
        """Proof containing Back must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Back 2.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_undo_in_proof_rejected(self):
        """Proof containing Undo must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Theorem t : True. Proof. Undo. exact I. Qed.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_forbidden_in_problem_statement(self):
        """Forbidden commands in problem_statement must also be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
                problem_statement='Redirect "/tmp/evil" Print nat.\nTheorem t : True.\nAdmitted.',
            )

    def test_forbidden_inside_comment_not_rejected(self):
        """Forbidden keywords inside comments must NOT trigger rejection."""
        source = build_verification_source(
            proof="(* End M. Redirect Drop *)\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        assert "Module M." in source

    def test_forbidden_outside_comment_still_rejected(self):
        """Forbidden commands after a comment must still be caught."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof="(* harmless *) End M.",
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_string_inside_comment_desync_rejected(self):
        """CRITICAL: string inside comment must not desynchronize scanner.

        Rocq tracks strings inside comments, so in (* " (* " *), the
        inner (* is inside a string and does NOT nest.  The *) closes the
        comment, making End M. executable code.  A naive scanner (without
        string tracking in comments) would treat (* as nesting, keeping
        the comment open and hiding End M. from the forbidden check.
        """
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='(* " (* " *) End M.\nAxiom cheat : False.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_string_with_close_comment_inside_comment(self):
        """*) inside a quoted string within a comment must NOT close it."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='(* " *) " *) End M.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_add_loadpath_rejected(self):
        """Add LoadPath must be rejected (loads .vo from arbitrary dirs)."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Add LoadPath "/tmp/evil".\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_add_rec_loadpath_rejected(self):
        """Add Rec LoadPath must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Add Rec LoadPath "/tmp/evil".\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_add_ml_path_rejected(self):
        """Add ML Path must be rejected."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Add ML Path "/tmp/evil".\nTheorem t : True. Proof. exact I. Qed.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_comment_replaced_with_space(self):
        """Comments should be replaced with space, not removed.

        This prevents Load(* *)bar from becoming Loadbar (bypassing \\b).
        """
        from rocq_mcp.verify import _strip_rocq_comments

        stripped = _strip_rocq_comments("Load(* *)bar")
        # Comment replaced with space(s), not removed — words stay separate
        assert "Loadbar" not in stripped
        assert "Load" in stripped and "bar" in stripped
        # No stray delimiter characters in output
        assert "*" not in stripped

    def test_strip_desync_exploit_direct(self):
        """Direct test: desync exploit makes End M. visible after stripping."""
        from rocq_mcp.verify import _strip_rocq_comments

        assert "End M." in _strip_rocq_comments('(* " (* " *) End M.')

    def test_strip_close_in_string_direct(self):
        """Direct test: *) in string inside comment does not close comment."""
        from rocq_mcp.verify import _strip_rocq_comments

        assert "End M." in _strip_rocq_comments('(* " *) " *) End M.')

    def test_strip_escaped_quote_in_string_in_comment(self):
        """\"\" escape in string inside comment must not end the string."""
        from rocq_mcp.verify import _strip_rocq_comments

        # (* "a""*)" *) — the "" is escape, *) still inside string
        stripped = _strip_rocq_comments('(* "a""*)" *) End M.')
        assert "End M." in stripped

    def test_strip_multiple_strings_in_comment(self):
        from rocq_mcp.verify import _strip_rocq_comments

        stripped = _strip_rocq_comments('(* "a" and "b" *) visible')
        assert "visible" in stripped
        assert "and" not in stripped

    def test_strip_no_stray_delimiter_chars(self):
        """Closing *) must not leave a stray * in the output."""
        from rocq_mcp.verify import _strip_rocq_comments

        # Comment replaced with a space; no stray * or ) in output
        assert _strip_rocq_comments("(* comment *)") == " "
        assert _strip_rocq_comments("a(* x *)b") == "a  b"
        assert _strip_rocq_comments("(* (* nested *) *)") == " "
        assert _strip_rocq_comments("x (* a *) y (* b *) z") == "x    y    z"

    def test_scanners_agree_on_comment_ranges(self):
        """Cross-validate _rocq_scan (via _rocq_comment_ranges) and _strip_rocq_comments."""
        from rocq_mcp.verify import _rocq_scan, _strip_rocq_comments
        from rocq_mcp.server import _rocq_comment_ranges

        cases = [
            '(* " (* " *) End M.',
            '(* " *) " *) End M.',
            '(* "a""*)" *) x.',
            '"(* not a comment *)" y.',
            '(* "a" and "b" *) z.',
            "normal code. (* comment *) more.",
            "(* (* nested *) *) after.",
            "(* a *)(* b *)",
            "x (* end *)",
        ]
        for text in cases:
            ranges = _rocq_comment_ranges(text)
            # Build set of positions inside comments from ranges
            in_comment_positions = set()
            for start, end in ranges:
                in_comment_positions.update(range(start, end))

            # Build set from _rocq_scan
            scan_comment_chars = set()
            for idx, _ch, in_comment, _in_str in _rocq_scan(text):
                if in_comment:
                    scan_comment_chars.add(idx)

            # The scanner skips the second char of two-char tokens (*, ))
            # so scan positions are a subset of range positions.  Every
            # scan-comment position must be inside a range, and every
            # range position must either be a scan-comment position or
            # the skipped second char of a two-char delimiter.
            assert scan_comment_chars <= in_comment_positions, (
                f"Scanner has comment positions outside ranges for: {text!r}\n"
                f"  scan only: {scan_comment_chars - in_comment_positions}"
            )
            extra = in_comment_positions - scan_comment_chars
            for pos in extra:
                # Each extra position must be the skipped second char
                # of a two-char token: (*, *), or "" (escaped quote)
                assert pos > 0 and (text[pos - 1 : pos + 1] in ("(*", "*)", '""')), (
                    f"Range position {pos} is not a skipped delimiter char "
                    f"for: {text!r}"
                )

            # _strip_rocq_comments should produce only non-comment chars
            stripped = _strip_rocq_comments(text)
            # Collect non-comment chars from the scan in order
            expected_chars = [
                ch for _, ch, in_comment, _ in _rocq_scan(text) if not in_comment
            ]
            # Stripped output (ignoring replacement spaces) must contain
            # exactly the non-comment characters in order
            stripped_chars = [c for c in stripped if c != " "]
            expected_non_space = [c for c in expected_chars if c != " "]
            assert stripped_chars == expected_non_space, (
                f"Stripped output has wrong characters for: {text!r}\n"
                f"  expected: {expected_non_space}\n"
                f"  got:      {stripped_chars}"
            )


# =========================================================================
# PART B: Integration tests (require coqc)
# =========================================================================

# We import rocq_verify at the top level so monkeypatch tests work,
# but skip all integration classes if coqc is not available.
from rocq_mcp.server import rocq_verify  # noqa: E402


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifySuccess:
    """Valid proofs that should pass verification."""

    async def test_valid_proof(self, workspace, simple_proof, simple_problem_statement):
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is True

    async def test_classical_proof_accepted(
        self, workspace, classical_proof, classical_problem
    ):
        """Proof using classical logic should be accepted with axiom listed."""
        result = await rocq_verify(
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

    async def test_braces_in_proof(self, workspace, braces_proof):
        """Proofs with { } subgoal braces should verify correctly."""
        problem = (
            "Require Import Arith.\n\n"
            "Theorem add_comm_example : forall n m : nat, n + m = m + n.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=braces_proof,
            problem_name="add_comm_example",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True

    async def test_multiline_import_proof(self, workspace, multiline_import_proof):
        """Proof with multi-line From...Require Import should verify."""
        problem = (
            "From Coq Require Import\n"
            "  Arith\n"
            "  Lia.\n\n"
            "Theorem test : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=multiline_import_proof,
            problem_name="test",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifyRejection:
    """Proofs that must be REJECTED by verification."""

    async def test_type_redefinition(
        self, workspace, cheating_proof, simple_problem_statement
    ):
        """Redefining nat as bool must be caught."""
        result = await rocq_verify(
            proof=cheating_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_axiom_spoofing(self, workspace, axiom_spoofing_proof):
        """CRITICAL: user-defined 'Axiom classic : False' must be rejected.

        Inside Module M., this becomes M.classic which is NOT a standard library
        axiom. The _is_standard_axiom check must reject the M. prefix.
        """
        problem = "Theorem anything : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=axiom_spoofing_proof,
            problem_name="anything",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_admitted_inside_module(
        self, workspace, admitted_proof, simple_problem_statement
    ):
        """Proof using an Admitted helper lemma must be rejected."""
        result = await rocq_verify(
            proof=admitted_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        # Should either have suspicious assumptions or a compilation error
        assert "assumptions" in result or "error" in result

    async def test_wrong_theorem_name(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """Using a wrong problem_name must fail (M.wrong_name not found)."""
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="wrong_name",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_end_module_escape(self, workspace):
        """Proof containing 'End M.' to try to escape the module sandbox.

        The proof tries to close Module M early, then declare an axiom at
        top level. Rocq should reject this with a compilation error, which
        is the safe outcome (verified=False).
        """
        escape_proof = (
            "Theorem t : True.\n"
            "Proof. exact I. Qed.\n"
            "End M.\n"
            "Axiom cheat : False.\n"
            "Module M.\n"
            "Theorem t2 : False. Proof. exact cheat. Qed.\n"
        )
        result = await rocq_verify(
            proof=escape_proof,
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_module_m_in_problem_statement(self, workspace):
        """Problem statement containing 'Module M.' must not break template.

        A crafted problem_statement could try to reopen Module M after
        End M. Rocq should reject this with a compilation error.
        """
        proof = "Theorem t : True.\n" "Proof. exact I. Qed.\n"
        malicious_statement = (
            "Theorem t : True.\n"
            "Admitted.\n"
            "Module M.\n"
            "Axiom cheat : False.\n"
            "End M.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=malicious_statement,
            workspace=str(workspace),
        )
        # Should fail: either the module structure is invalid, or the
        # extra Module M. causes a redefinition error
        assert result["verified"] is False


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifyInputValidation:
    """Input validation checks."""

    async def test_dotted_problem_name(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """Qualified names (containing dots) must be rejected early."""
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="Nat.add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "valid rocq identifier" in result["error"].lower()

    async def test_bad_workspace(self, simple_proof, simple_problem_statement):
        """Non-existent workspace should return a clear error."""
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace="/nonexistent/path/xyz",
        )
        assert result["verified"] is False
        assert "error" in result

    async def test_timeout(self, workspace, timeout_proof):
        """Diverging proof inside verification template should timeout."""
        problem = "Theorem loop_thm : True.\nAdmitted.\n"
        result = await rocq_verify(
            proof=timeout_proof,
            problem_name="loop_thm",
            problem_statement=problem,
            workspace=str(workspace),
            timeout=3,
        )
        assert result["verified"] is False
        assert "timed out" in result["error"].lower()

    async def test_oversized_proof(self, workspace):
        """Proof exceeding max size should be rejected."""
        result = await rocq_verify(
            proof="x" * 2_000_000,
            problem_name="test",
            problem_statement="Theorem test : True.\nAdmitted.",
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "size" in result["error"].lower()

    async def test_newline_in_problem_name(
        self, workspace, simple_proof, simple_problem_statement
    ):
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r\nAxiom cheat : False",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_space_in_problem_name(
        self, workspace, simple_proof, simple_problem_statement
    ):
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r Axiom cheat",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is False


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestVerifyCleanup:
    """Verification should not leave temp files behind."""

    async def test_no_artifacts_left(
        self, workspace, simple_proof, simple_problem_statement
    ):
        before = set(glob_mod.glob(str(workspace / "*")))
        await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    async def test_no_artifacts_on_failure(
        self, workspace, cheating_proof, simple_problem_statement
    ):
        """Even when verification fails, no temp files should remain."""
        before = set(glob_mod.glob(str(workspace / "*")))
        await rocq_verify(
            proof=cheating_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"


# ---------------------------------------------------------------------------
# Shared-defs integration tests (Phase 2 template + coqc)
# ---------------------------------------------------------------------------


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestSharedDefsIntegration:
    """Test the shared-defs verification template against real coqc.

    These tests exercise the Phase 2 template builder + coqc compilation
    directly, without requiring pytanque (no ctx needed).
    """

    async def test_shared_defs_template_compiles_with_inductive(self):
        """The shared-defs template should compile when Inductive types are involved."""
        structure = ProblemStructure(
            preamble_source="",
            definitions=[
                DefinitionInfo(
                    name="color",
                    detail="Inductive",
                    category=DefCategory.SHARED_DEF,
                    source_text="Inductive color := Red | Green | Blue.",
                    start_line=0,
                    end_line=0,
                )
            ],
            theorem_source="Theorem foo : forall c : color, c = c.",
            theorem_name="foo",
            has_shared_defs=True,
            full_source=(
                "Inductive color := Red | Green | Blue.\n"
                "Theorem foo : forall c : color, c = c.\n"
                "Admitted."
            ),
        )
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem foo : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )
        source = build_shared_defs_verification_source(proof, "foo", structure)
        # Actually compile it with coqc
        from rocq_mcp.server import _run_coqc

        result = _run_coqc(source, "/tmp", 60)
        assert result["returncode"] == 0, f"coqc failed: {result['stderr']}"
        assert (
            "Closed under the global context" in result["stdout"]
            or "Axioms" not in result["stdout"]
        )

    async def test_module_m_fails_with_inductive(self, workspace):
        """Standard Module M should fail when proof has Inductive types."""
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem foo : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed."
        )
        problem = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem foo : forall c : color, c = c.\n"
            "Admitted."
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="foo",
            problem_statement=problem,
            workspace=str(workspace),
        )
        # Without pytanque ctx, Phase 2 cannot run, so this falls back to
        # Phase 1 which should fail due to type unification across Module M.
        assert result["verified"] is False
