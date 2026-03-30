"""Tests for rocq_verify tool and verification helpers in verify.py.

Part A: Unit tests for verify.py helpers (NO coqc needed)
    - TestCleanProblemStatement
    - TestAxiomClassification
    - TestParseAssumptionsUserAxiomNames
    - TestParseAssumptions
    - TestBuildVerificationSource
    - TestClassifyTocDetail
    - TestVerificationHint
    - TestStripSharedDefs
    - TestBuildSharedDefsVerificationSource
    - TestVerifyInputSanitization
    - TestCheckForbiddenCommands
    - TestCheckTypeShadowing
    - TestCheckModuleNameShadowing
    - TestExtractUserAxiomNames
    - TestBuildDirectVerificationSource
    - TestBuildDirectTypeCheckSource
    - TestParseCheckType
    - TestNormalizeTypeForComparison

Part B: Integration tests for rocq_verify (require coqc)
    - TestVerifySuccess
    - TestVerifyRejection
    - TestVerifyInputValidation
    - TestVerifyCleanup
    - TestSharedDefsIntegration
    - TestDirectVerification
    - TestTimeoutFallbackToPhase3
"""

from __future__ import annotations

import glob as glob_mod

import pytest

from tests.conftest import COQC_AVAILABLE
from rocq_mcp.verify import (
    _check_forbidden_commands,
    _check_module_name_shadowing,
    _check_type_shadowing,
    _clean_problem_statement,
    _extract_definition_names,
    _extract_definition_sentence,
    _extract_user_axiom_names,
    _is_standard_axiom,
    _axiom_short_name,
    _AMBIGUOUS_AXIOM_NAMES,
    _parse_assumptions_raw,
    _PROTECTED_MODULE_NAMES,
    _SHARED_DEF_DETAILS,
    _strip_shared_defs,
    build_direct_type_check_source,
    build_direct_verification_source,
    build_shared_defs_verification_source,
    classify_toc_detail,
    DefCategory,
    DefinitionInfo,
    normalize_type_for_comparison,
    parse_and_classify_assumptions,
    parse_check_type,
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

    def test_proof_using_stripped(self):
        """'Proof using vars. Admitted.' must strip both Admitted and Proof using."""
        cleaned = _clean_problem_statement(
            "Theorem t : True.\nProof using x y.\nAdmitted."
        )
        assert "Proof" not in cleaned
        assert "Theorem t : True." in cleaned

    def test_proof_with_stripped(self):
        """'Proof with tactic. Admitted.' must strip both Admitted and Proof with."""
        cleaned = _clean_problem_statement(
            "Theorem t : True.\nProof with auto.\nAdmitted."
        )
        assert "Proof" not in cleaned
        assert "Theorem t : True." in cleaned

    def test_proof_using_multiple_vars(self):
        """'Proof using a b c.' must be fully stripped."""
        cleaned = _clean_problem_statement(
            "Theorem t : True.\nProof using a b c.\nAdmitted."
        )
        assert "Proof" not in cleaned
        assert "Theorem t : True." in cleaned

    def test_proof_using_qualified_name(self):
        """Proof using with qualified names (dots) must be fully stripped."""
        cleaned = _clean_problem_statement(
            "Theorem t : True.\nProof using Nat.add.\nAdmitted."
        )
        assert "Proof" not in cleaned
        assert "Theorem t : True." in cleaned

    def test_proof_with_qualified_name(self):
        """Proof with tactic containing dots must be fully stripped."""
        cleaned = _clean_problem_statement(
            "Theorem t : True.\nProof with Nat.add_comm.\nAdmitted."
        )
        assert "Proof" not in cleaned
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

    # --- require_qualified mode (Phase 3) ---

    def test_unqualified_add_rejected_when_require_qualified(self):
        """In Phase 3, unqualified 'add' must be rejected (could be user axiom)."""
        assert _is_standard_axiom("add", require_qualified=True) is False

    def test_unqualified_classic_accepted_when_require_qualified(self):
        """In Phase 3, unqualified 'classic' is accepted (unique stdlib name)."""
        assert _is_standard_axiom("classic", require_qualified=True) is True

    def test_qualified_stdlib_accepted_when_require_qualified(self):
        """In Phase 3, fully qualified stdlib axioms are still accepted."""
        assert (
            _is_standard_axiom(
                "Coq.Logic.Classical_Prop.classic", require_qualified=True
            )
            is True
        )

    def test_module_qualified_accepted_when_require_qualified(self):
        """In Phase 3, module-qualified stdlib axioms are still accepted."""
        assert (
            _is_standard_axiom("Classical_Prop.classic", require_qualified=True) is True
        )

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

    # --- Primitive integers (PrimInt63 / Uint63Axioms): should be ACCEPTED ---

    def test_int_unqualified(self):
        assert _is_standard_axiom("int") is True

    def test_int_primint63_qualified(self):
        assert _is_standard_axiom("PrimInt63.int") is True

    def test_int_corelib_qualified(self):
        assert _is_standard_axiom("Corelib.Numbers.Cyclic.Int63.PrimInt63.int") is True

    def test_add_unqualified(self):
        assert _is_standard_axiom("add") is True

    def test_sub_unqualified(self):
        assert _is_standard_axiom("sub") is True

    def test_eqb_unqualified(self):
        assert _is_standard_axiom("eqb") is True

    def test_eqb_correct_unqualified(self):
        assert _is_standard_axiom("eqb_correct") is True

    def test_eqb_refl_unqualified(self):
        assert _is_standard_axiom("eqb_refl") is True

    def test_of_to_Z_unqualified(self):
        assert _is_standard_axiom("of_to_Z") is True

    def test_add_spec_unqualified(self):
        assert _is_standard_axiom("add_spec") is True

    def test_uint63_axioms_module_qualified(self):
        assert _is_standard_axiom("Uint63Axioms.add_spec") is True

    def test_land_unqualified(self):
        assert _is_standard_axiom("land") is True

    def test_lsr_unqualified(self):
        assert _is_standard_axiom("lsr") is True

    def test_user_int_rejected(self):
        """User-qualified 'int' must be rejected."""
        assert _is_standard_axiom("M.int") is False

    def test_user_add_rejected(self):
        """User-qualified 'add' must be rejected."""
        assert _is_standard_axiom("M.add") is False

    # --- Primitive floats (PrimFloat): should be ACCEPTED ---

    def test_float_unqualified(self):
        assert _is_standard_axiom("float") is True

    def test_float_primfloat_qualified(self):
        assert _is_standard_axiom("PrimFloat.sqrt") is True

    def test_float_corelib_qualified(self):
        assert _is_standard_axiom("Corelib.Floats.PrimFloat.float") is True

    def test_classify_unqualified(self):
        assert _is_standard_axiom("classify") is True

    def test_normfr_mantissa_unqualified(self):
        assert _is_standard_axiom("normfr_mantissa") is True

    def test_next_up_unqualified(self):
        assert _is_standard_axiom("next_up") is True

    def test_user_float_rejected(self):
        assert _is_standard_axiom("M.float") is False

    # --- Primitive arrays (PrimArray): should be ACCEPTED ---

    def test_array_unqualified(self):
        assert _is_standard_axiom("array") is True

    def test_get_primarray_qualified(self):
        assert _is_standard_axiom("PrimArray.get") is True

    def test_make_primarray_qualified(self):
        assert _is_standard_axiom("PrimArray.make") is True

    def test_copy_unqualified(self):
        assert _is_standard_axiom("copy") is True

    def test_user_array_rejected(self):
        assert _is_standard_axiom("M.array") is False

    # --- Primitive strings (PrimString): should be ACCEPTED ---

    def test_string_unqualified(self):
        assert _is_standard_axiom("string") is True

    def test_cat_unqualified(self):
        assert _is_standard_axiom("cat") is True

    def test_primstring_qualified(self):
        assert _is_standard_axiom("PrimString.cat") is True

    def test_user_string_rejected(self):
        assert _is_standard_axiom("M.string") is False

    # --- Refined require_qualified: ambiguous vs unique ---

    def test_ambiguous_add_rejected_require_qualified(self):
        """'add' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("add", require_qualified=True) is False

    def test_ambiguous_compare_rejected_require_qualified(self):
        """'compare' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("compare", require_qualified=True) is False

    def test_ambiguous_length_rejected_require_qualified(self):
        """'length' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("length", require_qualified=True) is False

    def test_ambiguous_epsilon_rejected_require_qualified(self):
        """'epsilon' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("epsilon", require_qualified=True) is False

    def test_unique_funcext_accepted_require_qualified(self):
        """'functional_extensionality_dep' is unique — accepted in Phase 3."""
        assert (
            _is_standard_axiom("functional_extensionality_dep", require_qualified=True)
            is True
        )

    def test_unique_proof_irrelevance_accepted_require_qualified(self):
        """'proof_irrelevance' is unique — accepted in Phase 3."""
        assert _is_standard_axiom("proof_irrelevance", require_qualified=True) is True

    def test_ambiguous_completeness_rejected_require_qualified(self):
        """'completeness' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("completeness", require_qualified=True) is False

    def test_unique_Rplus_comm_accepted_require_qualified(self):
        """'Rplus_comm' is unique — accepted in Phase 3."""
        assert _is_standard_axiom("Rplus_comm", require_qualified=True) is True

    def test_ambiguous_R_rejected_require_qualified(self):
        """'R' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("R", require_qualified=True) is False

    def test_ambiguous_R0_rejected_require_qualified(self):
        """'R0' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("R0", require_qualified=True) is False

    def test_ambiguous_R1_rejected_require_qualified(self):
        """'R1' is ambiguous — must be rejected in Phase 3."""
        assert _is_standard_axiom("R1", require_qualified=True) is False

    def test_qualified_R_accepted_require_qualified(self):
        """Qualified 'Raxioms.R' should still be accepted."""
        assert _is_standard_axiom("Raxioms.R", require_qualified=True) is True

    def test_ambiguous_names_coverage(self):
        """All _AMBIGUOUS_AXIOM_NAMES must be rejected when require_qualified."""
        for name in _AMBIGUOUS_AXIOM_NAMES:
            assert (
                _is_standard_axiom(name, require_qualified=True) is False
            ), f"Ambiguous name '{name}' should be rejected with require_qualified"


# ---------------------------------------------------------------------------
# parse_and_classify_assumptions with user_axiom_names
# ---------------------------------------------------------------------------


class TestParseAssumptionsUserAxiomNames:
    """Test user_axiom_names parameter in parse_and_classify_assumptions."""

    def test_user_axiom_overrides_whitelist(self):
        """User-declared 'classic' must be suspicious even though it's in whitelist."""
        stdout = "Axioms:\nclassic : False\n"
        verdict, details = parse_and_classify_assumptions(
            stdout, user_axiom_names={"classic"}
        )
        assert verdict == "suspicious"
        assert "classic" in details["suspicious_names"]

    def test_user_axiom_add_caught(self):
        """User-declared 'add' must be suspicious."""
        stdout = "Axioms:\nadd : False\n"
        verdict, details = parse_and_classify_assumptions(
            stdout, user_axiom_names={"add"}
        )
        assert verdict == "suspicious"

    def test_stdlib_axiom_not_in_user_set_accepted(self):
        """Stdlib axiom not in user set should be accepted."""
        stdout = "Axioms:\nclassic : forall P : Prop, P \\/ ~ P\n"
        verdict, _details = parse_and_classify_assumptions(
            stdout, user_axiom_names=set()
        )
        assert verdict == "standard_only"

    def test_mixed_user_and_stdlib(self):
        """Mix of user axiom and stdlib axiom."""
        stdout = "Axioms:\nclassic : forall P : Prop, P \\/ ~ P\nmy_cheat : False\n"
        verdict, details = parse_and_classify_assumptions(
            stdout, user_axiom_names={"my_cheat"}
        )
        assert verdict == "suspicious"
        assert "my_cheat" in details["suspicious_names"]

    def test_qualified_user_axiom_caught_by_short_name(self):
        """Module-qualified user axiom caught by short name match."""
        stdout = "Axioms:\nMyMod.add : False\n"
        verdict, details = parse_and_classify_assumptions(
            stdout, user_axiom_names={"add"}
        )
        assert verdict == "suspicious"


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

    def test_injected_closed_before_real_axioms(self):
        """CRITICAL: injected 'Closed under the global context' before real axioms.

        An adversary can inject ``Print Assumptions clean_lemma.`` inside
        Module M, producing 'Closed under the global context' on stdout
        before the template's real Print Assumptions output that shows
        suspicious axioms.  The parser must use the LAST output block.
        """
        stdout = (
            "Closed under the global context\n"
            "Axioms:\n"
            "M.helper : forall n : nat, n + 0 = n\n"
        )
        result = _parse_assumptions_raw(stdout)
        assert len(result) == 1
        assert result[0][0] == "M.helper"

    def test_injected_closed_before_real_closed(self):
        """Multiple 'Closed' lines: last one wins (still closed)."""
        stdout = "Closed under the global context\n" "Closed under the global context\n"
        result = _parse_assumptions_raw(stdout)
        assert result == []

    def test_injected_axioms_before_real_closed(self):
        """Injected Axioms block before real 'Closed': last block wins."""
        stdout = "Axioms:\n" "M.fake : False\n" "Closed under the global context\n"
        result = _parse_assumptions_raw(stdout)
        assert result == []

    def test_classify_injected_closed_before_suspicious(self):
        """Higher-level: injected Closed before suspicious axioms must be suspicious."""
        stdout = "Closed under the global context\n" "Axioms:\n" "M.cheat : False\n"
        verdict, details = parse_and_classify_assumptions(stdout)
        assert verdict == "suspicious"
        assert "M.cheat" in details["suspicious_names"]

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

    def test_rejects_invalid_problem_name(self):
        """problem_name with newlines or special chars must be rejected."""
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="foo.\nAxiom cheat : False.\nPrint Assumptions",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_rejects_empty_problem_name(self):
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_printing_depth_reset_in_standard_template(self):
        """Standard Module M template must reset Printing Depth after End M."""
        source = build_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        after_end = source[source.index("End M.") :]
        assert "Set Printing Depth 1000000." in after_end


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
        assert "does not prove" in hint


# ---------------------------------------------------------------------------
# _neutralize_for_regex
# ---------------------------------------------------------------------------


class TestNeutralizeForRegex:
    """Test the position-preserving neutralization function."""

    def test_preserves_length(self):
        from rocq_mcp.verify import _neutralize_for_regex

        for text in [
            "no comments or strings",
            "(* a comment *)",
            '"a string"',
            '(* "string in comment" *)',
            "(* (* nested *) *)",
            'x (* c *) "s" y',
            '(* "a""b" *) z',
        ]:
            result = _neutralize_for_regex(text)
            assert len(result) == len(
                text
            ), f"Length mismatch for {text!r}: {len(result)} != {len(text)}"

    def test_blanks_comment_interiors(self):
        from rocq_mcp.verify import _neutralize_for_regex

        result = _neutralize_for_regex("a(* comment *)b")
        assert result[0] == "a"
        assert result[-1] == "b"
        assert result[1:14] == " " * 13

    def test_blanks_string_interiors(self):
        from rocq_mcp.verify import _neutralize_for_regex

        result = _neutralize_for_regex('a"Load"b')
        assert result[0] == "a"
        assert result[-1] == "b"
        assert result[1] == '"'
        assert result[6] == '"'
        assert result[2:6] == "    "

    def test_no_change_for_plain_text(self):
        from rocq_mcp.verify import _neutralize_for_regex

        text = "Definition foo := 42."
        assert _neutralize_for_regex(text) == text


# ---------------------------------------------------------------------------
# _extract_source_range
# ---------------------------------------------------------------------------


class TestExtractSourceRange:
    """Test _extract_source_range bounds checking."""

    def test_single_line(self):
        from rocq_mcp.server import _extract_source_range

        lines = ["hello world", "second line"]
        assert _extract_source_range(lines, 0, 0, 0, 5) == "hello"

    def test_multi_line(self):
        from rocq_mcp.server import _extract_source_range

        lines = ["first", "second", "third"]
        assert _extract_source_range(lines, 0, 0, 2, 5) == "first\nsecond\nthird"

    def test_negative_start_raises(self):
        from rocq_mcp.server import _extract_source_range

        with pytest.raises(IndexError):
            _extract_source_range(["hello"], -1, 0, 0, 5)

    def test_end_beyond_lines_raises(self):
        from rocq_mcp.server import _extract_source_range

        with pytest.raises(IndexError):
            _extract_source_range(["hello"], 0, 0, 5, 0)

    def test_start_after_end_raises(self):
        from rocq_mcp.server import _extract_source_range

        with pytest.raises(IndexError):
            _extract_source_range(["first", "second"], 1, 0, 0, 5)


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

    def test_strip_nested_definition_in_body(self):
        """A definition whose body textually contains another definition pattern.

        If 'outer' and 'inner' are both in shared_names, the regex for
        'outer' produces a span that contains the span for 'inner'.
        Without merging, removing the inner span first corrupts the
        outer removal because offsets shift.
        """
        proof = (
            "Definition inner := 0.\n"
            "Definition outer := Definition inner := 0.\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"outer", "inner"})
        assert "Definition outer" not in result
        assert "Definition inner" not in result
        assert "Theorem foo" in result
        # The theorem and proof must survive intact.
        assert "Proof. exact I. Qed." in result

    def test_comments_outside_stripped_def_preserved(self):
        """Comments NOT inside a stripped definition should be preserved."""
        proof = (
            "Definition state := 0.\n"
            "(* This is an important comment. *)\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state"})
        assert "Definition state" not in result
        assert "(* This is an important comment. *)" in result
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

    def test_printing_depth_reset_in_shared_defs_template(self):
        """Shared-defs template must reset Printing Depth after End M."""
        structure = self._make_structure(
            defs=[("state", "Definition", "Definition state := list nat.")],
            theorem_source="Theorem foo : True.",
            full_source=(
                "Definition state := list nat.\n" "Theorem foo : True.\nAdmitted."
            ),
        )
        source = build_shared_defs_verification_source(
            proof="Definition state := list nat.\nTheorem foo : True.\nProof. exact I. Qed.",
            problem_name="foo",
            structure=structure,
        )
        after_end = source[source.index("End M.") :]
        assert "Set Printing Depth 1000000." in after_end

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

    def test_rejects_invalid_problem_name(self):
        """problem_name with injection payload must be rejected."""
        structure = self._make_structure()
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_shared_defs_verification_source(
                proof="Theorem foo : True. Proof. exact I. Qed.",
                problem_name="foo.\nAxiom cheat : False",
                structure=structure,
            )


# ---------------------------------------------------------------------------
# Input sanitization (injection attacks)
# ---------------------------------------------------------------------------


class TestVerifyInputSanitization:
    """Test that malicious inputs are rejected."""

    def test_problem_name_with_newline(self):
        """Newlines in problem_name must be rejected by build_verification_source."""
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="add_0_r\nAxiom cheat : False",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_problem_name_with_spaces(self):
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="add_0_r Axiom cheat",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_problem_name_with_semicolon(self):
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="add_0_r;evil",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

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

    def test_forbidden_inside_string_not_rejected(self):
        """Forbidden keywords inside string literals must NOT trigger rejection."""
        source = build_verification_source(
            proof='Definition msg := "Load something".\nTheorem t : True. Proof. exact I. Qed.',
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.",
        )
        assert "Module M." in source

    def test_forbidden_outside_string_still_rejected(self):
        """Forbidden commands outside strings must still be caught."""
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_verification_source(
                proof='Definition msg := "safe".\nLoad evil.',
                problem_name="t",
                problem_statement="Theorem t : True.\nAdmitted.",
            )

    def test_strip_rocq_strings(self):
        """_strip_rocq_strings blanks interior of strings, keeps delimiters."""
        from rocq_mcp.verify import _strip_rocq_strings

        assert _strip_rocq_strings('"Load"') == '"    "'
        assert _strip_rocq_strings('x "ab" y') == 'x "  " y'
        assert _strip_rocq_strings("no strings") == "no strings"

    def test_strip_shared_defs_ignores_def_in_comment(self):
        """_strip_shared_defs should not match definition keywords inside comments."""
        proof = (
            "(* Definition state := old. *)\n"
            "Theorem foo : True.\n"
            "Proof. exact I. Qed.\n"
        )
        result = _strip_shared_defs(proof, {"state"})
        # The Definition inside the comment should not be stripped;
        # the comment itself is replaced with spaces.
        assert "Theorem foo" in result

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


# ---------------------------------------------------------------------------
# Direct tests for _check_forbidden_commands
# ---------------------------------------------------------------------------


class TestCheckForbiddenCommands:
    """Direct unit tests for the forbidden command scanner."""

    def test_clean_source_returns_none(self):
        assert (
            _check_forbidden_commands("Theorem t : True. Proof. exact I. Qed.") is None
        )

    def test_redirect_detected(self):
        assert _check_forbidden_commands('Redirect "/tmp/out" Print nat.') is not None

    def test_extraction_to_file_detected(self):
        assert _check_forbidden_commands('Extraction "/tmp/evil.ml" nat.') is not None

    def test_drop_detected(self):
        assert _check_forbidden_commands("Drop.") is not None

    def test_separate_extraction_detected(self):
        assert _check_forbidden_commands("Separate Extraction nat.") is not None

    def test_recursive_extraction_detected(self):
        assert _check_forbidden_commands("Recursive Extraction nat.") is not None

    def test_cd_detected(self):
        assert _check_forbidden_commands('Cd "/tmp".') is not None

    def test_load_detected(self):
        assert _check_forbidden_commands("Load evil.") is not None

    def test_extraction_library_detected(self):
        assert _check_forbidden_commands("Extraction Library nat.") is not None

    def test_declare_ml_module_detected(self):
        assert _check_forbidden_commands('Declare ML Module "evil".') is not None

    def test_unset_guard_checking_detected(self):
        assert _check_forbidden_commands("Unset Guard Checking.") is not None

    def test_unset_positivity_checking_detected(self):
        assert _check_forbidden_commands("Unset Positivity Checking.") is not None

    def test_unset_universe_checking_detected(self):
        assert _check_forbidden_commands("Unset Universe Checking.") is not None

    def test_bypass_check_detected(self):
        assert (
            _check_forbidden_commands("#[bypass_check(guard)] Fixpoint f := f.")
            is not None
        )

    def test_end_m_detected(self):
        assert _check_forbidden_commands("End M.") is not None

    def test_reset_detected(self):
        assert _check_forbidden_commands("Reset Initial.") is not None

    def test_back_detected(self):
        assert _check_forbidden_commands("Back 2.") is not None

    def test_undo_detected(self):
        assert _check_forbidden_commands("Undo.") is not None

    def test_add_loadpath_detected(self):
        assert _check_forbidden_commands('Add LoadPath "/tmp".') is not None

    def test_add_rec_loadpath_detected(self):
        assert _check_forbidden_commands('Add Rec LoadPath "/tmp".') is not None

    def test_add_ml_path_detected(self):
        assert _check_forbidden_commands('Add ML Path "/tmp".') is not None

    def test_forbidden_inside_comment_ignored(self):
        """Forbidden commands inside comments must NOT be detected."""
        assert _check_forbidden_commands("(* Drop. Load evil. End M. *)") is None

    def test_forbidden_inside_string_ignored(self):
        """Forbidden commands inside strings must NOT be detected."""
        assert _check_forbidden_commands('"Drop. Load evil."') is None

    def test_forbidden_after_comment_detected(self):
        """Forbidden commands after a comment must be caught."""
        result = _check_forbidden_commands("(* safe *) Drop.")
        assert result is not None

    def test_end_other_module_not_detected(self):
        """End Foo. must not be detected — only End M. is forbidden."""
        assert _check_forbidden_commands("End Foo.") is None

    def test_print_universes_with_file_blocked(self):
        """Print Universes with a file argument writes to disk and must be blocked."""
        assert _check_forbidden_commands('Print Universes "/tmp/out.txt".') is not None

    def test_print_sorted_universes_with_file_blocked(self):
        """Print Sorted Universes with a file argument writes to disk and must be blocked."""
        assert (
            _check_forbidden_commands('Print Sorted Universes "/tmp/out.txt".')
            is not None
        )

    def test_print_universes_without_file_allowed(self):
        """Print Universes without a file (stdout only) is safe and must be allowed."""
        assert _check_forbidden_commands("Print Universes.") is None

    def test_extraction_testcompile_blocked(self):
        """Extraction TestCompile invokes an external compiler and must be blocked."""
        assert _check_forbidden_commands("Extraction TestCompile nat.") is not None

    def test_extraction_bare_allowed(self):
        """Plain Extraction (stdout) is acceptable and must not be blocked."""
        assert _check_forbidden_commands("Extraction nat.") is None

    def test_print_universes_in_comment_allowed(self):
        """Print Universes inside a comment must not trigger the scanner."""
        assert (
            _check_forbidden_commands('(* Print Universes "/tmp/out.txt". *)') is None
        )

    def test_returns_descriptive_message(self):
        """Error messages should describe the forbidden command."""
        msg = _check_forbidden_commands("Drop.")
        assert "Drop" in msg


# ---------------------------------------------------------------------------
# Whitespace bypass variants for multi-word forbidden patterns (SEC-1/2/3/4)
# ---------------------------------------------------------------------------


class TestForbiddenWhitespaceBypasses:
    """Verify that multi-word forbidden patterns match newline/tab/multi-space variants."""

    def test_declare_ml_module_newline(self):
        result = _check_forbidden_commands('Declare ML\n  Module "test".')
        assert result is not None
        assert "Declare ML Module" in result

    def test_declare_ml_module_tab(self):
        result = _check_forbidden_commands('Declare ML\tModule "test".')
        assert result is not None

    def test_declare_ml_module_double_space(self):
        result = _check_forbidden_commands('Declare  ML  Module "test".')
        assert result is not None

    def test_separate_extraction_newline(self):
        result = _check_forbidden_commands("Separate\nExtraction foo.")
        assert result is not None
        assert "Separate Extraction" in result

    def test_separate_extraction_tab(self):
        result = _check_forbidden_commands("Separate\tExtraction foo.")
        assert result is not None

    def test_recursive_extraction_newline(self):
        result = _check_forbidden_commands("Recursive\n  Extraction foo.")
        assert result is not None
        assert "Recursive Extraction" in result

    def test_recursive_extraction_crlf(self):
        result = _check_forbidden_commands("Recursive\r\nExtraction foo.")
        assert result is not None

    def test_extraction_output_directory_basic(self):
        result = _check_forbidden_commands('Set Extraction Output Directory "/tmp".')
        assert result is not None
        assert "Extraction Output Directory" in result

    def test_extraction_output_directory_newline(self):
        result = _check_forbidden_commands('Set Extraction\nOutput\nDirectory "/tmp".')
        assert result is not None

    def test_extraction_output_directory_in_comment_ok(self):
        """Extraction Output Directory inside a comment should NOT be flagged."""
        result = _check_forbidden_commands(
            '(* Set Extraction Output Directory "/tmp". *)'
        )
        assert result is None

    def test_extraction_output_directory_in_string_ok(self):
        """Extraction Output Directory inside a string should NOT be flagged."""
        result = _check_forbidden_commands(
            'Definition x := "Extraction Output Directory".'
        )
        assert result is None


# ---------------------------------------------------------------------------
# Phase 3: _check_type_shadowing
# ---------------------------------------------------------------------------


class TestCheckTypeShadowing:
    """Test the core type redefinition scanner."""

    def test_inductive_nat_detected(self):
        assert _check_type_shadowing("Inductive nat := O | S (n : nat).") is not None

    def test_inductive_bool_detected(self):
        assert _check_type_shadowing("Inductive bool := true | false.") is not None

    def test_coinductive_list_detected(self):
        assert _check_type_shadowing("CoInductive list := nil | cons.") is not None

    def test_record_eq_detected(self):
        assert _check_type_shadowing("Record eq := {}.") is not None

    def test_variant_Z_detected(self):
        assert _check_type_shadowing("Variant Z := Zpos | Zneg | Z0.") is not None

    def test_noncore_type_allowed(self):
        assert _check_type_shadowing("Inductive color := Red | Green.") is None

    def test_definition_of_core_name_detected(self):
        """Definition of core name is now caught (prevents Phase 3 bypass)."""
        assert _check_type_shadowing("Definition nat := bool.") is not None

    def test_fixpoint_of_core_name_detected(self):
        """Fixpoint of core name is caught."""
        assert (
            _check_type_shadowing("Fixpoint nat (x : unit) : Type := bool.") is not None
        )

    def test_let_of_core_name_detected(self):
        """Let of core name is caught."""
        assert _check_type_shadowing("Let eq := True.") is not None

    def test_primitive_of_core_name_detected(self):
        """Primitive of core name is caught."""
        assert _check_type_shadowing("Primitive nat := #int63_type.") is not None

    def test_definition_of_noncore_name_allowed(self):
        """Definition of non-core names should still be allowed."""
        assert _check_type_shadowing("Definition my_helper := 42.") is None

    def test_inside_comment_ignored(self):
        assert _check_type_shadowing("(* Inductive nat := O. *)") is None

    def test_inside_string_ignored(self):
        assert _check_type_shadowing('"Inductive nat := O."') is None

    def test_clean_proof_returns_none(self):
        proof = "Require Import Arith.\n" "Theorem t : True. Proof. exact I. Qed.\n"
        assert _check_type_shadowing(proof) is None

    def test_multiple_core_types(self):
        """If multiple core types are redefined, at least one is caught."""
        proof = "Inductive nat := O.\nInductive bool := B.\n"
        result = _check_type_shadowing(proof)
        assert result is not None

    def test_structure_prod_detected(self):
        """Structure is a synonym for Record — must catch core type redefinition."""
        assert (
            _check_type_shadowing("Structure prod (A B : Type) := pair { fst : A }.")
            is not None
        )

    def test_class_eq_detected(self):
        """Class creates a Record-based type — must catch core type redefinition."""
        assert _check_type_shadowing("Class eq := { }.") is not None

    def test_new_core_types_detected(self):
        """Newly added core types (comparison, sumbool, Q, string) are caught."""
        assert _check_type_shadowing("Inductive comparison := Eq.") is not None
        assert _check_type_shadowing("Inductive sumbool := left | right.") is not None
        assert _check_type_shadowing("Record Q := { Qnum : Z }.") is not None
        assert _check_type_shadowing("Inductive string := EmptyString.") is not None

    def test_function_of_core_name_detected(self):
        """Function keyword must catch core name redefinition."""
        assert _check_type_shadowing("Function nat (x : unit) := x.") is not None

    def test_axiom_of_core_name_detected(self):
        """Axiom keyword must catch core name redefinition."""
        assert _check_type_shadowing("Axiom nat : Type.") is not None

    def test_parameter_of_core_name_detected(self):
        """Parameter keyword must catch core name redefinition."""
        assert _check_type_shadowing("Parameter bool : Type.") is not None

    def test_conjecture_of_core_name_detected(self):
        """Conjecture keyword must catch core name redefinition."""
        assert _check_type_shadowing("Conjecture eq : False.") is not None

    def test_hypothesis_of_core_name_detected(self):
        """Hypothesis keyword must catch core name redefinition."""
        assert _check_type_shadowing("Hypothesis eq : False.") is not None

    def test_variable_of_core_name_detected(self):
        """Variable keyword must catch core name redefinition."""
        assert _check_type_shadowing("Variable nat : Type.") is not None

    def test_le_lt_ge_gt_in_core_names(self):
        """le/lt/ge/gt are core names — redefinition must be caught."""
        assert _check_type_shadowing("Definition le (x y : nat) := True.") is not None
        assert (
            _check_type_shadowing("Definition lt := fun x y : nat => True.") is not None
        )
        assert (
            _check_type_shadowing("Definition ge := fun x y : nat => True.") is not None
        )
        assert (
            _check_type_shadowing("Definition gt := fun x y : nat => True.") is not None
        )

    def test_theorem_of_core_name_detected(self):
        """Theorem keyword must catch core name redefinition."""
        assert _check_type_shadowing("Theorem nat : True.") is not None

    def test_lemma_of_core_name_detected(self):
        """Lemma keyword must catch core name redefinition."""
        assert _check_type_shadowing("Lemma eq : True.") is not None

    def test_proposition_of_core_name_detected(self):
        """Proposition keyword must catch core name redefinition."""
        assert _check_type_shadowing("Proposition bool : True.") is not None

    def test_corollary_of_core_name_detected(self):
        """Corollary keyword must catch core name redefinition."""
        assert _check_type_shadowing("Corollary False : True.") is not None

    def test_example_of_core_name_detected(self):
        """Example keyword must catch core name redefinition."""
        assert _check_type_shadowing("Example nat : True.") is not None

    def test_fact_of_core_name_detected(self):
        """Fact keyword must catch core name redefinition."""
        assert _check_type_shadowing("Fact eq : True.") is not None

    def test_remark_of_core_name_detected(self):
        """Remark keyword must catch core name redefinition."""
        assert _check_type_shadowing("Remark bool : True.") is not None


# ---------------------------------------------------------------------------
# Phase 3: _check_module_name_shadowing
# ---------------------------------------------------------------------------


class TestCheckModuleNameShadowing:
    """Test module name shadowing detection for Phase 3."""

    def test_catches_classicaldedekindreals(self):
        """Module ClassicalDedekindReals must be caught (spoofs axiom prefix)."""
        proof = "Module ClassicalDedekindReals.\nAxiom sig_forall_dec : False.\nEnd ClassicalDedekindReals."
        result = _check_module_name_shadowing(proof)
        assert result is not None
        assert "ClassicalDedekindReals" in result

    def test_catches_primint63(self):
        """Module PrimInt63 must be caught."""
        proof = "Module PrimInt63.\nAxiom add : False.\nEnd PrimInt63."
        result = _check_module_name_shadowing(proof)
        assert result is not None
        assert "PrimInt63" in result

    def test_catches_raxioms(self):
        """Module Raxioms must be caught."""
        proof = "Module Raxioms.\nEnd Raxioms."
        result = _check_module_name_shadowing(proof)
        assert result is not None

    def test_allows_custom_module(self):
        """Module MyHelper should not be caught (not a protected name)."""
        proof = "Module MyHelper.\nDefinition x := 0.\nEnd MyHelper."
        assert _check_module_name_shadowing(proof) is None

    def test_module_in_comment_ignored(self):
        """Module declaration inside a comment should be ignored."""
        proof = "(* Module ClassicalDedekindReals. End ClassicalDedekindReals. *)"
        assert _check_module_name_shadowing(proof) is None

    def test_module_type_caught(self):
        """Module Type with protected name IS caught (defense-in-depth).

        Although Module Type alone doesn't create axioms, it could be used
        with Declare Module to create axioms with stdlib-matching prefixes.
        """
        proof = "Module Type ClassicalDedekindReals.\nEnd ClassicalDedekindReals."
        assert _check_module_name_shadowing(proof) is not None

    def test_catches_module_coq(self):
        """Module Coq must be caught (spoofs Coq.Logic.* axiom prefix)."""
        proof = "Module Coq.\nEnd Coq."
        result = _check_module_name_shadowing(proof)
        assert result is not None
        assert "Coq" in result

    def test_catches_module_rocq(self):
        """Module Rocq must be caught."""
        proof = "Module Rocq.\nEnd Rocq."
        result = _check_module_name_shadowing(proof)
        assert result is not None

    def test_catches_module_stdlib(self):
        """Module Stdlib must be caught."""
        proof = "Module Stdlib.\nEnd Stdlib."
        result = _check_module_name_shadowing(proof)
        assert result is not None

    def test_catches_module_corelib(self):
        """Module Corelib must be caught."""
        proof = "Module Corelib.\nEnd Corelib."
        result = _check_module_name_shadowing(proof)
        assert result is not None

    def test_protected_names_cover_stdlib_prefixes(self):
        """All stdlib module prefixes should have their first component protected."""
        from rocq_mcp.verify import _STDLIB_MODULE_PREFIXES

        for prefix in _STDLIB_MODULE_PREFIXES:
            first_component = prefix.split(".")[0]
            assert first_component in _PROTECTED_MODULE_NAMES

    def test_protected_names_cover_stdlib_top_level(self):
        """Top-level stdlib namespace prefixes (Coq, Rocq, etc.) must be protected."""
        from rocq_mcp.verify import _STDLIB_PREFIXES

        for prefix in _STDLIB_PREFIXES:
            name = prefix.rstrip(".")
            assert (
                name in _PROTECTED_MODULE_NAMES
            ), f"'{name}' from _STDLIB_PREFIXES should be in _PROTECTED_MODULE_NAMES"


# ---------------------------------------------------------------------------
# Phase 3: _extract_user_axiom_names
# ---------------------------------------------------------------------------


class TestExtractUserAxiomNames:
    """Test extraction of user-declared axiom names."""

    def test_axiom(self):
        assert _extract_user_axiom_names("Axiom foo : nat.") == {"foo"}

    def test_parameter(self):
        assert _extract_user_axiom_names("Parameter bar : Type.") == {"bar"}

    def test_conjecture(self):
        assert _extract_user_axiom_names("Conjecture baz : False.") == {"baz"}

    def test_hypothesis(self):
        assert _extract_user_axiom_names("Hypothesis h : True.") == {"h"}

    def test_variable(self):
        assert _extract_user_axiom_names("Variable x : nat.") == {"x"}

    def test_multiple(self):
        proof = "Axiom a : nat.\nParameter b : Type.\nConjecture c : False."
        names = _extract_user_axiom_names(proof)
        assert names == {"a", "b", "c"}

    def test_inside_comment_ignored(self):
        assert _extract_user_axiom_names("(* Axiom foo : False. *)") == set()

    def test_inside_string_ignored(self):
        assert _extract_user_axiom_names('"Axiom foo : False."') == set()

    def test_no_axioms_no_theorems_no_defs(self):
        proof = "Require Import Arith."
        assert _extract_user_axiom_names(proof) == set()

    def test_axiom_inside_module(self):
        """Axiom inside a Module should still be extracted."""
        proof = "Module M.\nAxiom classic : False.\nEnd M."
        assert _extract_user_axiom_names(proof) == {"classic"}

    def test_multi_name_axiom(self):
        """Axiom a b c : T. should extract all three names."""
        assert _extract_user_axiom_names("Axiom a b c : nat.") == {"a", "b", "c"}

    def test_multi_name_parameter(self):
        """Parameter x y : T. should extract both names."""
        assert _extract_user_axiom_names("Parameter x y : Type.") == {"x", "y"}

    def test_multi_name_variable(self):
        """Variable a b : T. should extract both names."""
        assert _extract_user_axiom_names("Variable a b : nat.") == {"a", "b"}

    def test_theorem_name_extracted(self):
        """Theorem name should be extracted (defense-in-depth for Admitted)."""
        proof = "Theorem classic : False. Admitted."
        assert "classic" in _extract_user_axiom_names(proof)

    def test_lemma_name_extracted(self):
        """Lemma name should be extracted."""
        proof = "Lemma helper : forall n, n = n. Admitted."
        assert "helper" in _extract_user_axiom_names(proof)

    def test_proposition_name_extracted(self):
        """Proposition name should be extracted."""
        proof = "Proposition foo : True. Proof. exact I. Qed."
        assert "foo" in _extract_user_axiom_names(proof)

    def test_corollary_name_extracted(self):
        """Corollary name should be extracted."""
        proof = "Corollary bar : True. Proof. exact I. Qed."
        assert "bar" in _extract_user_axiom_names(proof)

    def test_mixed_axiom_and_lemma(self):
        """Both axiom-like and theorem-like declarations should be extracted."""
        proof = (
            "Axiom cheat : False.\n"
            "Lemma helper : True. Admitted.\n"
            "Theorem main : True. Proof. exact I. Qed."
        )
        names = _extract_user_axiom_names(proof)
        assert "cheat" in names
        assert "helper" in names
        assert "main" in names


# ---------------------------------------------------------------------------
# Phase 3: build_direct_verification_source
# ---------------------------------------------------------------------------


class TestBuildDirectVerificationSource:
    """Test the Phase 3 direct verification template builder."""

    def test_contains_check_and_print_assumptions(self):
        source = build_direct_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source
        assert "Print Assumptions t." in source

    def test_contains_set_printing_all(self):
        source = build_direct_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Set Printing All." in source

    def test_proof_preserved(self):
        proof = "Require Import Arith.\nTheorem t : True. Proof. exact I. Qed."
        source = build_direct_verification_source(proof=proof, problem_name="t")
        assert proof in source

    def test_rejects_forbidden_command(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_direct_verification_source(
                proof="Drop.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_core_type_redefinition(self):
        with pytest.raises(ValueError, match="core name"):
            build_direct_verification_source(
                proof="Inductive nat := O | S (n : nat).\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_export(self):
        with pytest.raises(ValueError, match="Export"):
            build_direct_verification_source(
                proof="Module Inner. End Inner. Export Inner.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_export_in_comment_allowed(self):
        """Export inside a comment should not trigger rejection."""
        source = build_direct_verification_source(
            proof="(* Export M. *)\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_rejects_include(self):
        """Include can shadow names — must be rejected in Phase 3."""
        with pytest.raises(ValueError, match="Include"):
            build_direct_verification_source(
                proof="Module Inner. Definition x := 0. End Inner.\nInclude Inner.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_bare_import(self):
        """Bare Import (without Require) can shadow names — must be rejected."""
        with pytest.raises(ValueError, match="Import"):
            build_direct_verification_source(
                proof="Module Inner. Definition x := 0. End Inner.\nImport Inner.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_require_import_allowed(self):
        """Require Import is safe and must NOT be rejected."""
        source = build_direct_verification_source(
            proof="Require Import Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_from_require_import_allowed(self):
        """From ... Require Import is safe and must NOT be rejected."""
        source = build_direct_verification_source(
            proof="From Coq Require Import Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_require_export_allowed(self):
        """Require Export is safe (equivalent to Require Import for this file)."""
        source = build_direct_verification_source(
            proof="Require Export Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_from_require_export_allowed(self):
        """From ... Require Export is safe and must NOT be rejected."""
        source = build_direct_verification_source(
            proof="From Coq Require Export Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_rejects_bare_export(self):
        """Bare Export (without Require) must be rejected."""
        with pytest.raises(ValueError, match="Export"):
            build_direct_verification_source(
                proof="Module Inner. End Inner. Export Inner.\nTheorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_definition_of_core_name(self):
        """Definition of core name (e.g. 'Definition eq') must be rejected."""
        with pytest.raises(ValueError, match="core"):
            build_direct_verification_source(
                proof="Definition eq {A : Type} (x y : A) := True.\n"
                "Theorem t : eq 0 0. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_long_from_require_import_allowed(self):
        """Require Import with long From path must NOT be falsely rejected."""
        source = build_direct_verification_source(
            proof="From Coq.Init.Datatypes Require Import Arith.\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_rejects_invalid_name(self):
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_direct_verification_source(
                proof="Theorem t : True. Proof. exact I. Qed.",
                problem_name="bad name",
            )

    def test_printing_depth_reset_before_check(self):
        """Printing Depth/Width must be reset BEFORE Check to prevent truncation."""
        source = build_direct_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        # Printing flags must appear before Check
        depth_pos = source.index("Set Printing Depth 1000000.")
        check_pos = source.index("Check @t.")
        assert depth_pos < check_pos

    def test_printing_depth_also_before_print_assumptions(self):
        """Printing flags must also be reset before Print Assumptions."""
        source = build_direct_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        pa_pos = source.index("Print Assumptions t.")
        # There should be a second Set Printing Depth before Print Assumptions
        last_depth_pos = source.rindex("Set Printing Depth 1000000.")
        assert last_depth_pos < pa_pos

    def test_rejects_module_classicaldedekindreals(self):
        """Module that shadows stdlib module name must be rejected."""
        with pytest.raises(ValueError, match="ClassicalDedekindReals"):
            build_direct_verification_source(
                proof="Module ClassicalDedekindReals.\nAxiom sig_forall_dec : False.\nEnd ClassicalDedekindReals.\n"
                "Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_module_primint63(self):
        """Module PrimInt63 must be rejected (spoofs primitive int axioms)."""
        with pytest.raises(ValueError, match="PrimInt63"):
            build_direct_verification_source(
                proof="Module PrimInt63.\nAxiom add : False.\nEnd PrimInt63.\n"
                "Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_allows_custom_module(self):
        """Module MyHelper should not be rejected."""
        source = build_direct_verification_source(
            proof="Module MyHelper.\nDefinition x := 0.\nEnd MyHelper.\n"
            "Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_rejects_theorem_of_core_name(self):
        """Theorem nat : ... must be caught by _check_type_shadowing."""
        with pytest.raises(ValueError, match="core name"):
            build_direct_verification_source(
                proof="Theorem nat : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_lemma_of_core_name(self):
        """Lemma eq : ... must be caught by _check_type_shadowing."""
        with pytest.raises(ValueError, match="core name"):
            build_direct_verification_source(
                proof="Lemma eq : True. Proof. exact I. Qed.\n"
                "Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_module_coq(self):
        """Module Coq must be rejected (spoofs Coq.* axiom prefix)."""
        with pytest.raises(ValueError, match="Coq"):
            build_direct_verification_source(
                proof="Module Coq.\nEnd Coq.\n"
                "Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_rejects_le_redefinition(self):
        """Redefining le must be caught (re-added to core names)."""
        with pytest.raises(ValueError, match="core name"):
            build_direct_verification_source(
                proof="Definition le (x y : nat) := True.\n"
                "Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )


# ---------------------------------------------------------------------------
# Phase 3: build_direct_type_check_source
# ---------------------------------------------------------------------------


class TestBuildDirectTypeCheckSource:
    """Test the Phase 3 type check source builder for problem statements."""

    def test_contains_check(self):
        source = build_direct_type_check_source(
            problem_statement="Theorem t : True.\nAdmitted.",
            problem_name="t",
        )
        assert "Check @t." in source
        assert "Set Printing All." in source

    def test_preserves_problem_as_is(self):
        source = build_direct_type_check_source(
            problem_statement="Theorem t : True.\nAdmitted.",
            problem_name="t",
        )
        # The problem statement is included as-is (with Admitted.)
        assert "Theorem t : True." in source
        assert "Admitted." in source

    def test_rejects_forbidden_in_problem(self):
        with pytest.raises(ValueError, match="[Ff]orbidden"):
            build_direct_type_check_source(
                problem_statement='Redirect "/tmp/evil".\nTheorem t : True.\nAdmitted.',
                problem_name="t",
            )

    def test_rejects_invalid_name(self):
        with pytest.raises(ValueError, match="valid Rocq identifier"):
            build_direct_type_check_source(
                problem_statement="Theorem t : True.\nAdmitted.",
                problem_name="bad\nname",
            )

    def test_printing_depth_reset_before_check(self):
        """Printing Depth must be reset before Check to prevent truncation."""
        source = build_direct_type_check_source(
            problem_statement="Theorem t : True.\nAdmitted.",
            problem_name="t",
        )
        depth_pos = source.index("Set Printing Depth 1000000.")
        check_pos = source.index("Check @t.")
        assert depth_pos < check_pos


# ---------------------------------------------------------------------------
# Phase 3: parse_check_type
# ---------------------------------------------------------------------------


class TestParseCheckType:
    """Test parsing Check output from coqc stdout."""

    def test_single_line(self):
        stdout = "@t : True\n"
        result = parse_check_type(stdout, "t")
        assert result is not None
        assert "True" in result

    def test_multiline_type(self):
        stdout = "@add_0_r\n" "     : forall n : nat,\n" "       n + 0 = n\n"
        result = parse_check_type(stdout, "add_0_r")
        assert result is not None
        assert "forall" in result
        assert "nat" in result

    def test_missing_name_returns_none(self):
        stdout = "Some unrelated output\n"
        assert parse_check_type(stdout, "nonexistent") is None

    def test_empty_stdout_returns_none(self):
        assert parse_check_type("", "t") is None

    def test_colon_on_next_line(self):
        stdout = "@foo\n" "     : nat -> nat\n"
        result = parse_check_type(stdout, "foo")
        assert result is not None
        assert "nat -> nat" in result

    def test_with_other_output_before(self):
        """Check output appears after other compilation output."""
        stdout = "some warning here\n" "@t\n" "     : True\n"
        result = parse_check_type(stdout, "t")
        assert result is not None
        assert "True" in result

    def test_last_match_wins(self):
        """If @name appears twice, the LAST match is used (prevents stdout injection)."""
        stdout = "@t : nat\n\n@t : True\n"
        result = parse_check_type(stdout, "t")
        assert result is not None
        assert "True" in result
        assert "nat" not in result

    def test_no_prefix_collision(self):
        """@foobar must not match when searching for @foo."""
        stdout = "@foobar : nat\n\n@foo : True\n"
        result = parse_check_type(stdout, "foo")
        assert result is not None
        assert "True" in result
        assert "nat" not in result

    def test_prefix_name_no_match_when_only_prefix_exists(self):
        """If only @foobar exists, searching for @foo returns None."""
        stdout = "@foobar : nat\n"
        result = parse_check_type(stdout, "foo")
        assert result is None

    def test_bare_name_without_at_prefix(self):
        """Check output without @ prefix should still be parsed."""
        stdout = "t\n     : True\n"
        result = parse_check_type(stdout, "t")
        assert result is not None
        assert result == "True"

    def test_single_line_exact_type(self):
        """Verify exact type extraction, not just substring."""
        stdout = "@t : True\n"
        result = parse_check_type(stdout, "t")
        assert result == "True"


# ---------------------------------------------------------------------------
# Phase 3: _remaining_timeout
# ---------------------------------------------------------------------------


class TestRemainingTimeout:
    """Test the timeout budget tracking helper."""

    def test_returns_remaining_when_budget_available(self):
        import time

        from rocq_mcp.compile import _remaining_timeout

        t0 = time.monotonic()
        result = _remaining_timeout(t0, timeout=60, minimum=10)
        assert result >= 59  # just started, nearly full budget

    def test_returns_minimum_when_budget_exceeded(self):
        import time

        from rocq_mcp.compile import _remaining_timeout

        t0 = time.monotonic() - 100  # 100 seconds ago
        result = _remaining_timeout(t0, timeout=60, minimum=10)
        assert result == 10

    def test_returns_minimum_when_exactly_expired(self):
        import time

        from rocq_mcp.compile import _remaining_timeout

        t0 = time.monotonic() - 60
        result = _remaining_timeout(t0, timeout=60, minimum=10)
        assert result == 10


# ---------------------------------------------------------------------------
# Phase 3: normalize_type_for_comparison
# ---------------------------------------------------------------------------


class TestNormalizeTypeForComparison:
    """Test type string normalization for comparison."""

    def test_collapses_whitespace(self):
        assert normalize_type_for_comparison("forall  n :  nat,  n = n") == (
            "forall n : nat, n = n"
        )

    def test_collapses_newlines(self):
        result = normalize_type_for_comparison("forall n : nat,\n  n + 0 = n")
        assert "\n" not in result
        assert "forall n : nat, n + 0 = n" == result

    def test_strips_universe_annotations(self):
        assert normalize_type_for_comparison("Type@{Set}") == "Type"
        assert normalize_type_for_comparison("eq@{u v}") == "eq"

    def test_strips_complex_universe(self):
        result = normalize_type_for_comparison("forall (A : Type@{u+1}), A -> A")
        assert "@{" not in result
        assert "forall (A : Type), A -> A" == result

    def test_identity_for_clean_type(self):
        t = "forall n : nat, n + 0 = n"
        assert normalize_type_for_comparison(t) == t

    def test_strips_leading_trailing(self):
        assert normalize_type_for_comparison("  True  ") == "True"


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
        if "assumptions" in result and result["assumptions"] != []:
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

    async def test_printing_depth_reset(self, workspace):
        """Proof that sets Printing Depth to 1 must still verify.

        If Set Printing Depth 1 is inside the proof (Module M), it could
        truncate Print Assumptions output. The template resets Printing Depth
        to 1000000 after End M., so verification should succeed.
        """
        proof = (
            "Require Import Arith.\n"
            "Theorem depth_test : 1 + 1 = 2.\n"
            "Proof. Set Printing Depth 1. reflexivity. Qed.\n"
        )
        problem = "Require Import Arith.\nTheorem depth_test : 1 + 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="depth_test",
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

    async def test_oversized_problem_statement(self, workspace):
        """Problem statement exceeding max size should be rejected."""
        result = await rocq_verify(
            proof="Theorem test : True. Proof. exact I. Qed.",
            problem_name="test",
            problem_statement="x" * 2_000_000,
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

    async def test_module_m_fails_with_inductive_phase3_succeeds(self, workspace):
        """Standard Module M fails with Inductive types, but Phase 3 catches it."""
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
        # Without pytanque ctx, Phase 2 cannot run.  Phase 1 fails due to
        # type unification across Module M.  Phase 3 succeeds (direct compilation).
        assert result["verified"] is True
        assert result["verification_method"] == "direct"


# ---------------------------------------------------------------------------
# Phase 3: Direct verification integration tests
# ---------------------------------------------------------------------------


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestDirectVerification:
    """Test Phase 3 direct verification against real coqc.

    Phase 3 compiles the proof as-is (no Module M), then verifies via
    Print Assumptions + Check type comparison.
    """

    async def test_simple_proof_phase3(self, workspace):
        """A simple valid proof should pass Phase 3 when Phase 1 fails."""
        # Use Section/Variable which Module M can't handle
        proof = (
            "Section Foo.\n"
            "Variable A : Type.\n"
            "Theorem foo_id : A -> A.\n"
            "Proof. intro x. exact x. Qed.\n"
            "End Foo.\n"
        )
        problem = (
            "Section Foo.\n"
            "Variable A : Type.\n"
            "Theorem foo_id : A -> A.\n"
            "Admitted.\n"
            "End Foo.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="foo_id",
            problem_statement=problem,
            workspace=str(workspace),
        )
        # Phase 1 will fail (Section inside Module M causes issues),
        # Phase 3 should succeed
        assert result["verified"] is True
        assert result["verification_method"] == "direct"

    async def test_cheating_axiom_caught(self, workspace):
        """Phase 3 must catch proofs that use custom axioms."""
        proof = (
            "Axiom cheat : False.\n"
            "Theorem anything : 1 = 2.\n"
            "Proof. destruct cheat. Qed.\n"
        )
        problem = "Theorem anything : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="anything",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_admitted_helper_caught(self, workspace):
        """Phase 3 must catch proofs with Admitted helper lemmas."""
        proof = (
            "Require Import Arith.\n"
            "Lemma helper : forall n : nat, n + 0 = n. Admitted.\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Proof. apply helper. Qed.\n"
        )
        problem = (
            "Require Import Arith.\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="add_0_r",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_type_mismatch_caught(self, workspace):
        """Phase 3 must catch proofs that prove the wrong statement."""
        proof = (
            "Require Import Arith.\n"
            "Theorem wrong : forall n : nat, n + 0 = n.\n"
            "Proof. intros. lia. Qed.\n"
        )
        # Problem asks for a different theorem
        problem = (
            "Require Import Arith.\n"
            "Theorem wrong : forall n m : nat, n + m = m + n.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="wrong",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_core_type_redefinition_caught(self, workspace):
        """Phase 3 must reject proofs that redefine core types like nat."""
        proof = (
            "Inductive nat := O | S (n : nat).\n"
            "Theorem t : forall n : nat, n = n.\n"
            "Proof. reflexivity. Qed.\n"
        )
        problem = "Theorem t : forall n : nat, n = n.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        # Phase 1 catches this via Module M.  If Phase 1 somehow passed,
        # Phase 3's _check_type_shadowing would catch it.
        assert result["verified"] is False

    async def test_export_in_proof_caught(self, workspace):
        """Phase 3 must reject proofs that use Export."""
        proof = (
            "Module Inner. Definition x := 0. End Inner.\n"
            "Export Inner.\n"
            "Theorem t : x = 0.\n"
            "Proof. reflexivity. Qed.\n"
        )
        problem = "Theorem t : x = 0.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        # Phase 1 should catch this via Module M compilation error,
        # and Phase 3 rejects Export
        assert result["verified"] is False

    async def test_full_fallback_chain(self, workspace):
        """Phase 1 fails → Phase 2 skipped (no ctx) → Phase 3 succeeds."""
        # A proof with Inductive types that Module M can't handle
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_eq : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )
        problem = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_eq : forall c : color, c = c.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="color_eq",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True
        assert result["verification_method"] == "direct"

    async def test_direct_method_has_note(self, workspace):
        """Phase 3 results should include a note about reduced security."""
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_eq : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )
        problem = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_eq : forall c : color, c = c.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="color_eq",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True
        assert "direct" in result.get("note", "").lower()

    async def test_valid_proof_still_uses_phase1(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """A normal proof that works with Phase 1 should NOT use Phase 3."""
        result = await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert result["verified"] is True
        assert result["verification_method"] == "module_m"


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestTimeoutFallbackToPhase3:
    """Phase 1/2 timeout should fall through to Phase 3.

    Uses monkeypatch to deterministically force Phase 1 timeout (the
    real-world scenario is compute-heavy proofs where Module M doubles
    the work, e.g. mathd_numbertheory_543).  Phase 3 calls use real coqc.
    """

    async def test_phase1_timeout_triggers_phase3(self, workspace, monkeypatch):
        """When Phase 1 times out, Phase 3 should run and succeed."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — simulate timeout
                return {
                    "returncode": -1,
                    "stdout": "",
                    "stderr": "",
                    "timed_out": True,
                }
            # Phase 3 calls — delegate to real coqc
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Proof.\n"
            "  intros n. induction n as [| n' IH].\n"
            "  - reflexivity.\n"
            "  - simpl. rewrite IH. reflexivity.\n"
            "Qed.\n"
        )
        problem = (
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="add_0_r",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True
        assert result["verification_method"] == "direct"
        # Phase 1 (1 call) + Phase 3 Run A + Run B = 3 calls
        assert call_count == 3

    async def test_phase1_timeout_phase3_catches_axiom(self, workspace, monkeypatch):
        """Phase 1 times out, Phase 3 runs and catches cheating (custom axiom).

        Uses monkeypatch to force Phase 1 timeout deterministically,
        then verifies Phase 3 catches the cheating proof via real coqc.
        """
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — simulate timeout
                return {
                    "returncode": -1,
                    "stdout": "",
                    "stderr": "",
                    "timed_out": True,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Axiom cheat : False.\n"
            "Theorem anything : 1 = 2.\n"
            "Proof. destruct cheat. Qed.\n"
        )
        problem = "Theorem anything : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="anything",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "cheat" in result.get("error", "").lower()

    async def test_phase1_timeout_phase3_also_times_out(self, workspace, monkeypatch):
        """When Phase 1 and Phase 3 both timeout, return Phase 1 timeout error."""
        import rocq_mcp.server as srv

        def mock_run_coqc(source, ws, timeout):
            return {
                "returncode": -1,
                "stdout": "",
                "stderr": "",
                "timed_out": True,
            }

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        result = await rocq_verify(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
            problem_statement="Theorem t : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "timed out" in result["error"].lower()

    async def test_phase1_timeout_phase3_type_mismatch(self, workspace, monkeypatch):
        """Phase 1 times out, Phase 3 catches type mismatch (wrong statement)."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — simulate timeout
                return {
                    "returncode": -1,
                    "stdout": "",
                    "stderr": "",
                    "timed_out": True,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        # Proof proves 0 + n = n but problem expects n + 0 = n
        proof = (
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, 0 + n = n.\n"
            "Proof.\n"
            "  intros n. reflexivity.\n"
            "Qed.\n"
        )
        problem = (
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="add_0_r",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "type mismatch" in result.get("error", "").lower()


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestPhase3SecurityHardening:
    """Tests for fixes to Phase 3 security vulnerabilities found in review."""

    async def test_definition_eq_bypass_blocked(self, workspace, monkeypatch):
        """CRITICAL: Definition eq := True must be caught by _check_type_shadowing.

        Previously, _TYPE_DEF_KEYWORDS only had Inductive/Record/etc. so
        'Definition eq' was not caught, allowing a trivial Phase 3 bypass.
        """
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — simulate failure
                return {
                    "returncode": 1,
                    "stdout": "",
                    "stderr": "Error: unable to unify",
                    "timed_out": False,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Definition eq {A : Type} (x y : A) := True.\n"
            "Theorem t : @eq nat 0 1.\n"
            "Proof. exact I. Qed.\n"
        )
        problem = "Theorem t : @eq nat 0 1.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        # Phase 3 catches it via _check_type_shadowing (Definition eq)
        assert "core" in result.get("error", "").lower() or result["verified"] is False

    async def test_definition_nat_bypass_blocked(self, workspace, monkeypatch):
        """Definition nat := unit must be caught by _check_type_shadowing."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                return {
                    "returncode": 1,
                    "stdout": "",
                    "stderr": "Error",
                    "timed_out": False,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Definition nat := unit.\n"
            "Definition O : nat := tt.\n"
            "Theorem t : forall n : nat, @eq nat n O.\n"
            "Proof. intro n. destruct n. reflexivity. Qed.\n"
        )
        problem = "Theorem t : forall n : nat, @eq nat n O.\n" "Admitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False

    async def test_unqualified_axiom_add_rejected_in_phase3(
        self, workspace, monkeypatch
    ):
        """CRITICAL: Axiom add : False must be caught in Phase 3.

        Previously, unqualified 'add' matched _KNOWN_SAFE_AXIOMS (PrimInt63)
        and passed Phase 3 axiom check.  With require_qualified=True, it's
        correctly rejected.
        """
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — simulate timeout
                return {
                    "returncode": -1,
                    "stdout": "",
                    "stderr": "",
                    "timed_out": True,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Axiom add : False.\n" "Theorem t : 1 = 2.\n" "Proof. destruct add. Qed.\n"
        )
        problem = "Theorem t : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        # Should mention the axiom name in the error
        assert "add" in result.get("error", "").lower()

    async def test_require_export_proof_accepted(self, workspace):
        """Require Export in a proof must NOT be falsely rejected."""
        proof = (
            "From Coq Require Export Arith.\n\n"
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_eq : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )
        problem = (
            "From Coq Require Export Arith.\n\n"
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_eq : forall c : color, c = c.\n"
            "Admitted.\n"
        )
        result = await rocq_verify(
            proof=proof,
            problem_name="color_eq",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is True

    async def test_phase3_valueerror_returns_specific_error(
        self, workspace, monkeypatch
    ):
        """Phase 3 ValueError (e.g. Export ban) returns specific error, not None."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — failure
                return {
                    "returncode": 1,
                    "stdout": "",
                    "stderr": "Error: unable to unify",
                    "timed_out": False,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Module Inner. Definition x := 0. End Inner.\n"
            "Export Inner.\n"
            "Theorem t : x = 0. Proof. reflexivity. Qed.\n"
        )
        problem = "Theorem t : x = 0.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        # Should see the Phase 3 Export error, not a generic Phase 1 error
        assert "export" in result.get("error", "").lower()
        assert result.get("verification_method") == "direct"

    async def test_verification_method_on_suspicious_verdict(
        self, workspace, monkeypatch
    ):
        """Suspicious verdict should include verification_method field."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                # Phase 1 — timeout to force Phase 3
                return {
                    "returncode": -1,
                    "stdout": "",
                    "stderr": "",
                    "timed_out": True,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Axiom cheat : False.\n"
            "Theorem t : 1 = 2.\n"
            "Proof. destruct cheat. Qed.\n"
        )
        problem = "Theorem t : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "verification_method" in result

    async def test_module_spoofing_blocked_in_phase3(self, workspace, monkeypatch):
        """CRITICAL: Module ClassicalDedekindReals axiom spoofing must be caught."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                return {
                    "returncode": 1,
                    "stdout": "",
                    "stderr": "Error: unable to unify",
                    "timed_out": False,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Module ClassicalDedekindReals.\n"
            "Axiom sig_forall_dec : False.\n"
            "End ClassicalDedekindReals.\n"
            "Theorem t : 1 = 2.\n"
            "Proof. destruct ClassicalDedekindReals.sig_forall_dec. Qed.\n"
        )
        problem = "Theorem t : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        assert "ClassicalDedekindReals" in result.get("error", "")

    async def test_user_axiom_classic_caught_in_phase3(self, workspace, monkeypatch):
        """User Axiom classic : False must be caught via user_axiom_names."""
        import rocq_mcp.server as srv

        real_run_coqc = srv._run_coqc
        call_count = 0

        def mock_run_coqc(source, ws, timeout):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                return {
                    "returncode": -1,
                    "stdout": "",
                    "stderr": "",
                    "timed_out": True,
                }
            return real_run_coqc(source, ws, timeout)

        monkeypatch.setattr(srv, "_run_coqc", mock_run_coqc)

        proof = (
            "Axiom classic : False.\n"
            "Theorem t : 1 = 2.\n"
            "Proof. destruct classic. Qed.\n"
        )
        problem = "Theorem t : 1 = 2.\nAdmitted.\n"
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert result["verified"] is False
        # 'classic' should be caught by user_axiom_names extraction
        assert "classic" in result.get("error", "").lower()


# ---------------------------------------------------------------------------
# Phase 3: Admitted/admit ban in direct verification
# ---------------------------------------------------------------------------


class TestAdmittedBanInDirectVerification:
    """Test that Admitted, admit, and give_up are banned in Phase 3."""

    def test_admitted_rejected(self):
        """Proof containing Admitted must be rejected."""
        with pytest.raises(ValueError, match="Admitted"):
            build_direct_verification_source(
                proof="Lemma helper : False. Admitted.\n"
                "Theorem t : True. Proof. exact I. Qed.",
                problem_name="t",
            )

    def test_admit_tactic_rejected(self):
        """Proof containing admit tactic must be rejected."""
        with pytest.raises(ValueError, match="admit"):
            build_direct_verification_source(
                proof="Theorem t : True. Proof. admit. Qed.",
                problem_name="t",
            )

    def test_admitted_in_comment_allowed(self):
        """Admitted inside a comment must NOT trigger the ban."""
        source = build_direct_verification_source(
            proof="(* Admitted *)\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source

    def test_clean_proof_allowed(self):
        """A clean proof without Admitted/admit must pass."""
        source = build_direct_verification_source(
            proof="Theorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source
        assert "Print Assumptions t." in source

    def test_give_up_rejected(self):
        """Proof containing give_up should be rejected."""
        with pytest.raises(ValueError, match="give_up"):
            build_direct_verification_source(
                proof="Theorem t : True.\nProof. give_up. Qed.",
                problem_name="t",
            )

    def test_give_up_in_comment_ok(self):
        """give_up inside comment should not trigger."""
        source = build_direct_verification_source(
            proof="(* give_up *)\nTheorem t : True. Proof. exact I. Qed.",
            problem_name="t",
        )
        assert "Check @t." in source


# ---------------------------------------------------------------------------
# Phase 3: _extract_user_axiom_names expanded coverage (Definition/Fixpoint/etc.)
# ---------------------------------------------------------------------------


class TestExtractUserAxiomNamesExpanded:
    """Test _extract_user_axiom_names with Definition-like keywords."""

    def test_definition_name_extracted(self):
        assert "foo" in _extract_user_axiom_names("Definition foo := 0.")

    def test_fixpoint_name_extracted(self):
        assert "f" in _extract_user_axiom_names(
            "Fixpoint f (n : nat) : nat := match n with | O => O | S m => f m end."
        )

    def test_cofixpoint_name_extracted(self):
        assert "g" in _extract_user_axiom_names("CoFixpoint g := g.")

    def test_function_name_extracted(self):
        assert "h" in _extract_user_axiom_names("Function h (x : nat) := x.")

    def test_let_name_extracted(self):
        assert "x" in _extract_user_axiom_names("Let x := 0.")

    def test_instance_name_extracted(self):
        assert "myInst" in _extract_user_axiom_names("Instance myInst : True.")

    def test_context_parenthetical_extracted(self):
        """Context (classic : P). should extract classic."""
        names = _extract_user_axiom_names("Context (classic : False).")
        assert "classic" in names

    def test_context_multi_name_extracted(self):
        """Context (a b : nat) (c : bool). should extract all names."""
        names = _extract_user_axiom_names("Context (a b : nat) (c : bool).")
        assert {"a", "b", "c"} <= names

    def test_context_in_comment_ignored(self):
        """Context inside comment should not extract names."""
        names = _extract_user_axiom_names("(* Context (classic : False). *)")
        assert "classic" not in names


# ---------------------------------------------------------------------------
# C-1: Problem definition redefinition ban
# ---------------------------------------------------------------------------


class TestExtractDefinitionNames:
    """Tests for _extract_definition_names."""

    def test_definition(self):
        assert "foo" in _extract_definition_names("Definition foo := 0.")

    def test_fixpoint(self):
        assert "f" in _extract_definition_names("Fixpoint f (n : nat) := n.")

    def test_inductive(self):
        assert "mytype" in _extract_definition_names("Inductive mytype := A | B.")

    def test_record(self):
        assert "myrec" in _extract_definition_names("Record myrec := { field : nat }.")

    def test_theorem(self):
        assert "thm" in _extract_definition_names(
            "Theorem thm : True. Proof. exact I. Qed."
        )

    def test_class(self):
        assert "MyClass" in _extract_definition_names(
            "Class MyClass := { meth : nat }."
        )

    def test_cofixpoint(self):
        assert "g" in _extract_definition_names("CoFixpoint g := g.")

    def test_comment_ignored(self):
        assert _extract_definition_names("(* Definition foo := 0. *)") == set()

    def test_multiple_definitions(self):
        src = "Definition a := 0.\nInductive b := C.\nFixpoint c n := n."
        names = _extract_definition_names(src)
        assert {"a", "b", "c"} <= names

    def test_no_definitions(self):
        assert _extract_definition_names("Require Import Arith.") == set()


class TestExtractDefinitionSentence:
    """Tests for _extract_definition_sentence."""

    def test_simple_definition(self):
        result = _extract_definition_sentence("Definition foo := 0.", "foo")
        assert result is not None
        assert "Definition foo" in result
        assert "0" in result

    def test_inductive(self):
        result = _extract_definition_sentence(
            "Inductive color := Red | Green | Blue.", "color"
        )
        assert result is not None
        assert "Inductive color" in result

    def test_not_found(self):
        assert _extract_definition_sentence("Definition bar := 0.", "foo") is None

    def test_whitespace_normalized(self):
        """Multiple whitespace variants produce the same result."""
        s1 = _extract_definition_sentence("Definition foo := 0.", "foo")
        s2 = _extract_definition_sentence("Definition  foo  :=  0.", "foo")
        assert s1 == s2

    def test_comment_content_blanked(self):
        """Comments inside definition are blanked but don't affect match."""
        result = _extract_definition_sentence(
            "Definition foo (* a comment *) := 0.", "foo"
        )
        assert result is not None
        # Comment content should be blanked (spaces)
        assert "comment" not in result

    def test_fixpoint(self):
        result = _extract_definition_sentence("Fixpoint f (n : nat) := n.", "f")
        assert result is not None
        assert "Fixpoint f" in result


class TestProblemRedefinitionBan:
    """Tests for the C-1 fix: ban redefinition of problem names in Phase 3.

    The check compares definition text between proof and problem.
    Same definition text = allowed (legitimate reproduction).
    Different definition text = rejected (attack).
    """

    def test_redefining_problem_definition_with_different_body_rejected(self):
        """Proof that redefines a Definition with different body is rejected."""
        problem = "Definition is_even n := exists k, n = 2 * k.\nTheorem thm : is_even 3.\nProof. Admitted."
        proof = "Definition is_even n := True.\nTheorem thm : is_even 3.\nProof. exact I. Qed."
        with pytest.raises(ValueError, match="redefines name.*is_even"):
            build_direct_verification_source(proof, "thm", problem_statement=problem)

    def test_redefining_problem_inductive_with_different_body_rejected(self):
        """Proof that redefines an Inductive with different constructors is rejected."""
        problem = "Inductive mylist := Nil | Cons (h : nat) (t : mylist).\nTheorem thm : True.\nProof. Admitted."
        proof = "Inductive mylist := Nil.\nTheorem thm : True.\nProof. exact I. Qed."
        with pytest.raises(ValueError, match="redefines name.*mylist"):
            build_direct_verification_source(proof, "thm", problem_statement=problem)

    def test_same_definition_allowed(self):
        """Proof that reproduces the exact same definition is allowed."""
        problem = "Inductive color := Red | Green | Blue.\nTheorem thm : True.\nProof. Admitted."
        proof = "Inductive color := Red | Green | Blue.\nTheorem thm : True.\nProof. exact I. Qed."
        result = build_direct_verification_source(
            proof, "thm", problem_statement=problem
        )
        assert "Check @thm" in result

    def test_same_definition_different_whitespace_allowed(self):
        """Same definition with different whitespace is still allowed."""
        problem = "Definition foo := 0.\nTheorem thm : True.\nProof. Admitted."
        proof = "Definition  foo  :=  0.\nTheorem thm : True.\nProof. exact I. Qed."
        result = build_direct_verification_source(
            proof, "thm", problem_statement=problem
        )
        assert "Check @thm" in result

    def test_theorem_name_not_banned(self):
        """The theorem name itself must NOT be banned (proof must define it)."""
        problem = "Theorem thm : True.\nProof. Admitted."
        proof = "Theorem thm : True.\nProof. exact I. Qed."
        result = build_direct_verification_source(
            proof, "thm", problem_statement=problem
        )
        assert "Check @thm" in result

    def test_no_problem_statement_allows_anything(self):
        """Without problem_statement, no redefinition check is applied."""
        proof = (
            "Definition is_even n := True.\nTheorem thm : True.\nProof. exact I. Qed."
        )
        result = build_direct_verification_source(proof, "thm")
        assert "Check @thm" in result

    def test_different_names_pass(self):
        """Proof with different definition names from problem passes."""
        problem = "Definition foo := 0.\nTheorem thm : True.\nProof. Admitted."
        proof = "Definition bar := 1.\nTheorem thm : True.\nProof. exact I. Qed."
        result = build_direct_verification_source(
            proof, "thm", problem_statement=problem
        )
        assert "Check @thm" in result

    def test_axiom_spoofing_problem_name_different_kind(self):
        """Proof using Axiom for a problem Definition name is caught (different sentence)."""
        problem = "Definition is_even n := exists k, n = 2 * k.\nTheorem thm : True.\nProof. Admitted."
        proof = (
            "Axiom is_even : nat -> Prop.\nTheorem thm : True.\nProof. exact I. Qed."
        )
        with pytest.raises(ValueError, match="redefines name.*is_even"):
            build_direct_verification_source(proof, "thm", problem_statement=problem)

    def test_redefinition_in_comment_ignored(self):
        """Definition name inside comment doesn't count as redefinition."""
        problem = "Definition foo := 0.\nTheorem thm : True.\nProof. Admitted."
        proof = (
            "(* Definition foo := 999. *)\nTheorem thm : True.\nProof. exact I. Qed."
        )
        result = build_direct_verification_source(
            proof, "thm", problem_statement=problem
        )
        assert "Check @thm" in result


# ---------------------------------------------------------------------------
# C-2 / H-2: Multi-name parenthetical regex
# ---------------------------------------------------------------------------


class TestMultiNameParenthetical:
    """Tests for multi-name and multi-group parenthetical axiom extraction."""

    def test_multi_name_single_group(self):
        """Parameter (a b c : nat). captures all three."""
        names = _extract_user_axiom_names("Parameter (a b c : nat).")
        assert {"a", "b", "c"} <= names

    def test_multi_name_multi_group(self):
        """Parameter (a b : nat) (c d : bool). captures all four."""
        names = _extract_user_axiom_names("Parameter (a b : nat) (c d : bool).")
        assert {"a", "b", "c", "d"} <= names

    def test_type_name_not_captured(self):
        """Type names after ':' should NOT be captured."""
        names = _extract_user_axiom_names("Parameter (a : nat).")
        assert "nat" not in names

    def test_multi_group_different_keywords(self):
        """Parameter (a : nat) (b : bool). captures both groups."""
        names = _extract_user_axiom_names("Parameter (a : nat) (b : bool).")
        assert {"a", "b"} <= names


# ---------------------------------------------------------------------------
# H-1: Declare Module ban
# ---------------------------------------------------------------------------


class TestDeclareModuleBan:
    """Tests for Declare Module ban in Phase 3."""

    def test_declare_module_rejected(self):
        """Declare Module should be rejected in Phase 3."""
        proof = (
            "Module Type SIG.\n"
            "  Parameter t : Type.\n"
            "End SIG.\n"
            "Declare Module M : SIG.\n"
            "Theorem thm : True.\nProof. exact I. Qed."
        )
        with pytest.raises(ValueError, match="Declare Module"):
            build_direct_verification_source(proof, "thm")

    def test_declare_module_type_allowed(self):
        """Declare Module Type should NOT be rejected (harmless)."""
        # Note: "Declare Module Type" is not standard Rocq, but the check
        # should not trigger for "Module Type" preceded by any context.
        proof = "Module Type SIG.\nEnd SIG.\nTheorem thm : True.\nProof. exact I. Qed."
        result = build_direct_verification_source(proof, "thm")
        assert "Check @thm" in result

    def test_declare_module_in_comment_ok(self):
        """Declare Module inside comment should not trigger."""
        proof = (
            "(* Declare Module M : SIG. *)\nTheorem thm : True.\nProof. exact I. Qed."
        )
        result = build_direct_verification_source(proof, "thm")
        assert "Check @thm" in result


# ---------------------------------------------------------------------------
# H-4: Module Import/Export bypass fix
# ---------------------------------------------------------------------------


class TestModuleImportExportShadowing:
    """Tests for Module Import/Export bypass in _check_module_name_shadowing."""

    def test_module_import_nat_caught(self):
        """Module Import Nat. should be caught."""
        result = _check_module_name_shadowing("Module Import Nat.")
        assert result is not None
        assert "Nat" in result

    def test_module_export_nat_caught(self):
        """Module Export Nat. should be caught."""
        result = _check_module_name_shadowing("Module Export Nat.")
        assert result is not None
        assert "Nat" in result

    def test_declare_module_nat_caught(self):
        """Declare Module Nat. should be caught (Module regex matches)."""
        result = _check_module_name_shadowing("Declare Module Nat : SIG.")
        assert result is not None
