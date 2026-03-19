"""Tests for the rocq_auto_solve tool.

Part A: Unit tests for helper functions (NO coqc needed)
    - TestParsing: _parse_last_theorem with various input shapes
    - TestBuildSource: generated `first [...]` source structure
    - TestBuildSingleTacticSource: generated single-tactic source
    - TestInputValidation: bad workspace, oversized, forbidden commands

Part B: Integration tests (require coqc)
    - TestTrivial: True / exact I
    - TestLia: arithmetic via lia
    - TestRing: Z ring arithmetic
    - TestWithPreamble: intros + automation
    - TestUnsolvable: problems automation cannot solve
    - TestEdgeCases: multiple theorems, keyword variants, etc.
    - TestTimeout: diverging problems
    - TestCleanup: no temp files left behind
"""

from __future__ import annotations

import glob as glob_mod

import pytest

from tests.conftest import COQC_AVAILABLE
from rocq_mcp.server import (
    rocq_auto_solve,
    _parse_last_theorem,
    _build_auto_solve_source,
    _build_single_tactic_source,
    _AUTO_SOLVE_TACTICS,
    _rocq_comment_ranges,
    _find_sentence_end,
)

# =========================================================================
# PART A: Unit tests (no coqc needed)
# =========================================================================


# ---------------------------------------------------------------------------
# _rocq_comment_ranges
# ---------------------------------------------------------------------------


class TestRocqCommentRanges:
    """Direct unit tests for the Rocq comment scanner."""

    def test_no_comments(self):
        assert _rocq_comment_ranges("Theorem t : True.") == []

    def test_single_comment(self):
        assert _rocq_comment_ranges("(* hello *)") == [(0, 11)]

    def test_nested_comments(self):
        assert _rocq_comment_ranges("(* (* inner *) *)") == [(0, 17)]

    def test_triple_nested(self):
        assert _rocq_comment_ranges("(* a (* b (* c *) d *) e *)") == [(0, 27)]

    def test_multiple_comments(self):
        ranges = _rocq_comment_ranges("x (* a *) y (* b *) z")
        assert ranges == [(2, 9), (12, 19)]

    def test_comment_inside_string_ignored(self):
        assert _rocq_comment_ranges('"(* not a comment *)"') == []

    def test_string_inside_comment(self):
        # The string delimiter inside a comment doesn't start a string
        ranges = _rocq_comment_ranges('(* "hello" *)')
        assert ranges == [(0, 13)]

    def test_escaped_double_quote_in_string(self):
        # "" is an escaped quote, not end of string
        assert _rocq_comment_ranges('"a""b" (* c *)') == [(7, 14)]

    def test_empty_comment(self):
        assert _rocq_comment_ranges("(**) rest") == [(0, 4)]

    def test_unclosed_comment(self):
        # Unclosed comment is NOT reported (no closing range)
        assert _rocq_comment_ranges("(* unclosed") == []

    def test_dot_inside_comment(self):
        ranges = _rocq_comment_ranges("(* foo. bar *)")
        assert ranges == [(0, 14)]

    def test_string_with_fake_comment_open(self):
        """(* inside string inside comment must NOT increase depth."""
        # (* " (* " *) is ONE comment — the inner (* is inside a string
        assert _rocq_comment_ranges('(* " (* " *)') == [(0, 12)]

    def test_string_with_fake_comment_close(self):
        """*) inside string inside comment must NOT decrease depth."""
        # (* " *) " *) is ONE comment — the *) is inside a string
        assert _rocq_comment_ranges('(* " *) " *)') == [(0, 12)]

    def test_escaped_quote_in_string_inside_comment(self):
        """\"\" inside string inside comment must not end the string."""
        # (* "a""*)" *) — the "" is escape, *) is still inside string
        assert _rocq_comment_ranges('(* "a""*)" *)') == [(0, 13)]

    def test_multiple_strings_inside_comment(self):
        """Multiple strings inside one comment."""
        assert _rocq_comment_ranges('(* "a" and "b" *)') == [(0, 17)]

    def test_empty_input(self):
        assert _rocq_comment_ranges("") == []

    def test_adjacent_comments(self):
        """Adjacent comments (* a *)(* b *) are reported as one merged range."""
        assert _rocq_comment_ranges("(* a *)(* b *)") == [(0, 14)]

    def test_comment_at_end_with_leading_code(self):
        """Comment at end of text with preceding code exercises the end-of-text path."""
        assert _rocq_comment_ranges("x (* a *)") == [(2, 9)]


# ---------------------------------------------------------------------------
# _find_sentence_end
# ---------------------------------------------------------------------------


class TestFindSentenceEnd:
    """Direct unit tests for the Rocq sentence terminator finder."""

    def test_simple_dot(self):
        assert _find_sentence_end("Theorem t : True.") == 16

    def test_dot_followed_by_space(self):
        assert _find_sentence_end("exact I. Qed.") == 7

    def test_dot_followed_by_newline(self):
        assert _find_sentence_end("exact I.\n") == 7

    def test_no_terminating_dot(self):
        assert _find_sentence_end("Nat.add x y") is None

    def test_qualified_name_not_sentence(self):
        # Dot in Nat.add is not sentence-terminating
        assert _find_sentence_end("Check Nat.add.") == 13

    def test_dot_inside_comment(self):
        assert _find_sentence_end("(* foo. *) bar.") == 14

    def test_dot_inside_string(self):
        assert _find_sentence_end('"hello." world.') == 14

    def test_dot_inside_nested_comment(self):
        assert _find_sentence_end("(* (* inner. *) *) x.") == 20

    def test_dot_at_end_of_text(self):
        assert _find_sentence_end("exact I.") == 7

    def test_empty_text(self):
        assert _find_sentence_end("") is None

    def test_number_with_dot(self):
        # 1.5 has dot NOT followed by whitespace — not a sentence end
        assert _find_sentence_end("Definition x := 1.5.") == 19

    def test_dot_inside_string_inside_comment(self):
        # Dot inside a string inside a comment is not a sentence end
        assert _find_sentence_end('(* "." *) x.') == 11


# ---------------------------------------------------------------------------
# _parse_last_theorem
# ---------------------------------------------------------------------------


class TestAutoSolveParsing:
    """Test _parse_last_theorem with various input shapes."""

    def test_simple_theorem(self):
        source = (
            "From Stdlib Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = _parse_last_theorem(source)
        assert result is not None
        preamble, keyword, name, stmt = result
        assert keyword == "Theorem"
        assert name == "add_0_r"
        assert "forall n : nat, n + 0 = n." in stmt
        assert "Require Import Arith." in preamble

    def test_multiline_statement(self):
        source = (
            "Require Import Reals.\n"
            "Open Scope R_scope.\n\n"
            "Theorem foo :\n"
            "  forall x y : R,\n"
            "    x + y = y + x.\n"
            "Proof.\n"
            "Admitted.\n"
        )
        result = _parse_last_theorem(source)
        assert result is not None
        _, keyword, name, stmt = result
        assert keyword == "Theorem"
        assert name == "foo"
        assert stmt.endswith(".")

    def test_lemma_keyword(self):
        source = "Lemma trivial_lemma : True.\nAdmitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        _, keyword, name, _ = result
        assert keyword == "Lemma"
        assert name == "trivial_lemma"

    def test_corollary_keyword(self):
        source = "Corollary my_cor : 1 = 1.\nAdmitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        _, keyword, name, _ = result
        assert keyword == "Corollary"
        assert name == "my_cor"

    def test_all_theorem_keywords(self):
        """All theorem-like keywords should be recognized."""
        for kw in (
            "Theorem",
            "Lemma",
            "Proposition",
            "Corollary",
            "Example",
            "Fact",
            "Remark",
        ):
            source = f"{kw} test_kw : True.\nAdmitted.\n"
            result = _parse_last_theorem(source)
            assert result is not None, f"Failed to parse keyword: {kw}"
            assert result[1] == kw
            assert result[2] == "test_kw"

    def test_last_theorem_used(self):
        source = (
            "Lemma helper : True.\nProof. exact I. Qed.\n\n"
            "Theorem main : True.\nAdmitted.\n"
        )
        result = _parse_last_theorem(source)
        assert result is not None
        preamble, keyword, name, _ = result
        assert keyword == "Theorem"
        assert name == "main"
        # The helper should be in the preamble
        assert "Lemma helper" in preamble

    def test_no_theorem(self):
        source = "From Stdlib Require Import Arith.\nDefinition x := 42.\n"
        result = _parse_last_theorem(source)
        assert result is None

    def test_empty_source(self):
        result = _parse_last_theorem("")
        assert result is None

    def test_proof_admitted_stripped(self):
        """Proof. Admitted. after the theorem should NOT appear in the statement."""
        source = "Theorem foo : True.\n" "Proof.\n" "Admitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        preamble, _, _, stmt = result
        assert "Admitted" not in stmt
        assert "Proof" not in stmt

    def test_statement_with_comment(self):
        """Comments in the middle of a statement should not break parsing."""
        source = "Theorem bar (* a comment *) : True.\n" "Admitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        _, _, name, _ = result
        assert name == "bar"

    def test_name_with_prime(self):
        source = "Theorem foo' : True.\nAdmitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        assert result[2] == "foo'"

    def test_name_with_underscores_and_digits(self):
        source = "Lemma helper_123 : True.\nAdmitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        assert result[2] == "helper_123"

    def test_parametric_theorem_nat(self):
        """Theorem with explicit parameter: Theorem foo (n : nat) : n = n."""
        source = "Theorem foo (n : nat) : n = n.\nAdmitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        preamble, keyword, name, stmt = result
        assert keyword == "Theorem"
        assert name == "foo"
        assert "(n : nat)" in stmt
        assert stmt.endswith(".")

    def test_parametric_theorem_implicit(self):
        """Theorem with implicit parameter: Theorem foo {A : Type} : ..."""
        source = "Theorem foo {A : Type} (x : A) : x = x.\n" "Admitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        preamble, keyword, name, stmt = result
        assert keyword == "Theorem"
        assert name == "foo"
        assert "{A : Type}" in stmt
        assert "(x : A)" in stmt
        assert stmt.endswith(".")

    def test_parametric_lemma_multiple_params(self):
        """Lemma with multiple parameters of different kinds."""
        source = (
            "Lemma bar (n m : nat) {P : Prop} (H : P) : n + m = m + n.\n" "Admitted.\n"
        )
        result = _parse_last_theorem(source)
        assert result is not None
        _, keyword, name, stmt = result
        assert keyword == "Lemma"
        assert name == "bar"
        assert "(n m : nat)" in stmt
        assert "{P : Prop}" in stmt

    def test_commented_out_theorem_ignored(self):
        """A theorem inside (* ... *) should be ignored; the real one is picked."""
        source = "(* Theorem fake : False. *)\n" "Theorem real : True.\n" "Admitted.\n"
        result = _parse_last_theorem(source)
        assert result is not None
        _, keyword, name, stmt = result
        assert keyword == "Theorem"
        assert name == "real"
        assert "True" in stmt
        # The fake theorem must NOT be picked
        assert name != "fake"

    def test_commented_out_theorem_only(self):
        """If the only theorem keyword is inside a comment, return None."""
        source = "(* Theorem fake : False. *)\nDefinition x := 42.\n"
        result = _parse_last_theorem(source)
        assert result is None

    def test_commented_theorem_before_real_in_preamble(self):
        """Commented theorem in preamble, real theorem after it."""
        source = (
            "From Stdlib Require Import Arith.\n"
            "(* Theorem old_attempt : forall n, n = n. *)\n"
            "Lemma actual : 1 = 1.\n"
            "Admitted.\n"
        )
        result = _parse_last_theorem(source)
        assert result is not None
        preamble, keyword, name, _ = result
        assert keyword == "Lemma"
        assert name == "actual"
        # The preamble should contain the comment but the parser should
        # not have treated the commented keyword as a theorem.
        assert "(* Theorem old_attempt" in preamble


# ---------------------------------------------------------------------------
# _build_auto_solve_source
# ---------------------------------------------------------------------------


class TestBuildAutoSolveSource:
    """Test generation of the `first [tac1 | tac2 | ...]` source."""

    def test_basic_structure(self):
        source = _build_auto_solve_source(
            preamble="Require Import Arith.",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactics=["trivial", "auto"],
        )
        assert "Theorem foo : True." in source
        assert "Proof." in source
        assert "first [ solve [trivial] | solve [auto] ]." in source
        assert "Qed." in source
        assert "Require Import Arith." in source

    def test_with_preamble_tactics(self):
        source = _build_auto_solve_source(
            preamble="",
            full_statement="Theorem foo : forall n, n = n.",
            preamble_tactics="intros.",
            tactics=["reflexivity"],
        )
        assert "intros." in source
        assert "first [ solve [reflexivity] ]." in source

    def test_adds_lia_import_when_missing(self):
        """When Lia is not in preamble, it should be added."""
        source = _build_auto_solve_source(
            preamble="Require Import Arith.",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactics=["lia"],
        )
        assert "From Stdlib Require Import Lia Lra Ring Field." in source

    def test_always_adds_stdlib_imports(self):
        """Stdlib imports are always added (duplicates are harmless)."""
        source = _build_auto_solve_source(
            preamble="Require Import Lia.",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactics=["lia"],
        )
        assert "From Stdlib Require Import Lia Lra Ring Field." in source

    def test_all_auto_solve_tactics_present(self):
        """Verify the source includes all standard auto_solve tactics."""
        source = _build_auto_solve_source(
            preamble="",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactics=_AUTO_SOLVE_TACTICS,
        )
        for tactic in _AUTO_SOLVE_TACTICS:
            assert tactic in source

    def test_empty_preamble(self):
        """Empty preamble should still produce valid source."""
        source = _build_auto_solve_source(
            preamble="",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactics=["trivial"],
        )
        assert "Theorem foo : True." in source
        assert "Proof." in source


# ---------------------------------------------------------------------------
# _build_single_tactic_source
# ---------------------------------------------------------------------------


class TestBuildSingleTacticSource:
    """Test generation of single-tactic verification source."""

    def test_basic(self):
        source = _build_single_tactic_source(
            preamble="",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactic="exact I",
        )
        assert "exact I." in source
        assert "Qed." in source
        assert "first" not in source

    def test_with_preamble_tactics(self):
        source = _build_single_tactic_source(
            preamble="",
            full_statement="Theorem foo : forall n, n = n.",
            preamble_tactics="intros.",
            tactic="reflexivity",
        )
        assert "intros." in source
        assert "reflexivity." in source

    def test_adds_lia_import(self):
        source = _build_single_tactic_source(
            preamble="",
            full_statement="Theorem foo : True.",
            preamble_tactics="",
            tactic="lia",
        )
        assert "From Stdlib Require Import Lia Lra Ring Field." in source


# ---------------------------------------------------------------------------
# Input validation (no coqc needed for some)
# ---------------------------------------------------------------------------


class TestAutoSolveInputValidation:
    """Bad inputs should produce clear errors."""

    def test_no_theorem(self, workspace):
        problem = "From Stdlib Require Import Arith.\nDefinition x := 42.\n"
        result = rocq_auto_solve(problem=problem, workspace=str(workspace))
        assert result["solved"] is False
        assert "Could not find" in result["error"]

    def test_bad_workspace(self):
        problem = "Theorem foo : True.\nAdmitted.\n"
        result = rocq_auto_solve(problem=problem, workspace="/nonexistent/path/xyz")
        assert result["solved"] is False
        assert (
            "not exist" in result["error"].lower()
            or "does not exist" in result["error"].lower()
        )

    def test_oversized_problem(self, workspace):
        result = rocq_auto_solve(problem="x" * 2_000_000, workspace=str(workspace))
        assert result["solved"] is False
        assert "size" in result["error"].lower()

    def test_forbidden_command_in_problem(self, workspace):
        problem = 'Load "evil".\nTheorem foo : True.\nAdmitted.\n'
        result = rocq_auto_solve(problem=problem, workspace=str(workspace))
        assert result["solved"] is False
        assert "forbidden" in result["error"].lower()

    def test_forbidden_command_redirect(self, workspace):
        problem = 'Redirect "/tmp/evil" Print nat.\nTheorem t : True.\nAdmitted.'
        result = rocq_auto_solve(problem=problem, workspace=str(workspace))
        assert result["solved"] is False
        assert "forbidden" in result["error"].lower()

    def test_forbidden_preamble_tactics(self, workspace):
        problem = "Theorem foo : True.\nAdmitted.\n"
        result = rocq_auto_solve(
            problem=problem,
            preamble_tactics="Drop",
            workspace=str(workspace),
        )
        assert result["solved"] is False
        assert "forbidden" in result["error"].lower()

    def test_forbidden_preamble_tactics_extraction(self, workspace):
        problem = "Theorem foo : True.\nAdmitted.\n"
        result = rocq_auto_solve(
            problem=problem,
            preamble_tactics='Redirect "/tmp/evil" Print nat',
            workspace=str(workspace),
        )
        assert result["solved"] is False
        assert "forbidden" in result["error"].lower()


# =========================================================================
# PART B: Integration tests (require coqc)
# =========================================================================


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveTrivial:
    """Trivially true problems solved by trivial/exact I."""

    def test_true_exact_i(self, workspace):
        """Lemma foo : True should be solved by exact I or trivial."""
        result = rocq_auto_solve(
            problem="Lemma foo : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is True
        assert result["tactic"] in ("trivial", "exact I", "auto", "eauto", "tauto")
        assert "Proof." in result["proof"]
        assert "Qed." in result["proof"]

    def test_reflexivity_nat(self, workspace):
        """forall n, n = n should be solved by reflexivity."""
        result = rocq_auto_solve(
            problem="Theorem refl_test : forall n : nat, n = n.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is True
        assert result["tactic"] in ("trivial", "reflexivity", "auto", "eauto", "tauto")

    def test_reflexivity_literal(self, workspace):
        """1 = 1 solved by reflexivity."""
        result = rocq_auto_solve(
            problem="Theorem refl_lit : 1 = 1.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is True


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveLia:
    """Arithmetic problems solved by lia."""

    def test_lia_nat_add(self, workspace):
        """forall n, n + 0 = n should be solved by lia with intros."""
        result = rocq_auto_solve(
            problem=(
                "From Stdlib Require Import Lia.\n\n"
                "Theorem lia_test : forall n : nat, n + 0 = n.\n"
                "Admitted.\n"
            ),
            preamble_tactics="intros.",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_lia_without_import(self, workspace):
        """lia should work even without explicit Lia import (auto_solve adds it)."""
        result = rocq_auto_solve(
            problem=(
                "Theorem lia_noimport : forall n : nat, n + 0 = n.\n" "Admitted.\n"
            ),
            preamble_tactics="intros",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_lia_inequality(self, workspace):
        """Simple inequality: forall n, n >= 0."""
        result = rocq_auto_solve(
            problem=(
                "From Stdlib Require Import Lia.\n\n"
                "Theorem lia_ineq : forall n : nat, n >= 0.\n"
                "Admitted.\n"
            ),
            preamble_tactics="intros.",
            workspace=str(workspace),
        )
        assert result["solved"] is True


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveRing:
    """Ring/field arithmetic problems."""

    def test_ring_z_mul_identity(self, workspace):
        """forall x : Z, x * 1 = x should be solved by ring."""
        result = rocq_auto_solve(
            problem=(
                "From Stdlib Require Import ZArith.\n"
                "Open Scope Z_scope.\n\n"
                "Theorem ring_test : forall x : Z, x * 1 = x.\n"
                "Admitted.\n"
            ),
            workspace=str(workspace),
        )
        assert result["solved"] is True
        assert result["tactic"] in ("ring", "lia", "nia", "auto", "intuition")

    def test_ring_z_comm(self, workspace):
        """forall x y : Z, x + y = y + x should be solved by ring."""
        result = rocq_auto_solve(
            problem=(
                "From Stdlib Require Import ZArith.\n"
                "Open Scope Z_scope.\n\n"
                "Theorem ring_comm : forall x y : Z, x + y = y + x.\n"
                "Admitted.\n"
            ),
            workspace=str(workspace),
        )
        assert result["solved"] is True


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveWithPreamble:
    """Tests for problems that need preamble tactics before automation."""

    def test_intros_then_lia(self, workspace):
        """Problem needing intros before lia can solve it."""
        result = rocq_auto_solve(
            problem=(
                "From Stdlib Require Import Lia.\n\n"
                "Theorem preamble_test : forall n : nat, n >= 0.\n"
                "Admitted.\n"
            ),
            preamble_tactics="intros",
            workspace=str(workspace),
        )
        assert result["solved"] is True
        assert "intros" in result["proof"].lower()

    def test_intros_then_assumption(self, workspace):
        """P -> P with intros + assumption."""
        result = rocq_auto_solve(
            problem=("Theorem assume_test : forall P : Prop, P -> P.\n" "Admitted.\n"),
            preamble_tactics="intros.",
            workspace=str(workspace),
        )
        assert result["solved"] is True
        assert result["tactic"] in (
            "trivial",
            "assumption",
            "auto",
            "eauto",
            "tauto",
            "intuition",
            "exact I",
            "firstorder",
        )

    def test_preamble_no_trailing_dot(self, workspace):
        """Preamble_tactics without trailing dot should get one appended."""
        result = rocq_auto_solve(
            problem="Theorem dot_test : forall P : Prop, P -> P.\nAdmitted.\n",
            preamble_tactics="intros",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_preamble_with_trailing_dot(self, workspace):
        """Preamble_tactics with trailing dot should be used as-is."""
        result = rocq_auto_solve(
            problem="Theorem dot_test2 : forall P : Prop, P -> P.\nAdmitted.\n",
            preamble_tactics="intros.",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_proof_text_includes_preamble(self, workspace):
        """The returned proof text should include the preamble tactics."""
        result = rocq_auto_solve(
            problem="Theorem pt_test : forall n : nat, n = n.\nAdmitted.\n",
            preamble_tactics="intros.",
            workspace=str(workspace),
        )
        assert result["solved"] is True
        assert "intros." in result["proof"]


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveUnsolvable:
    """Problems that standard automation should NOT solve."""

    def test_induction_needed(self, workspace):
        """n + 0 = n without intros requires induction -- not automatable."""
        problem = (
            "From Stdlib Require Import Arith.\n\n"
            "Theorem ind_test : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        result = rocq_auto_solve(problem=problem, workspace=str(workspace))
        # Note: with `auto` hint database this *might* succeed in some
        # Coq versions. If it fails, verify error is sensible.
        if not result["solved"]:
            assert "error" in result

    def test_custom_fixpoint(self, workspace):
        """Custom recursive definition needs manual proof."""
        problem = (
            "Fixpoint double (n : nat) : nat :=\n"
            "  match n with\n"
            "  | 0 => 0\n"
            "  | S n' => S (S (double n'))\n"
            "  end.\n\n"
            "Theorem double_correct : forall n, double n = n + n.\n"
            "Admitted.\n"
        )
        result = rocq_auto_solve(problem=problem, workspace=str(workspace))
        assert result["solved"] is False
        assert "error" in result

    def test_returns_sensible_error(self, workspace):
        """Unsolvable problem should return solved:false with error."""
        problem = (
            "Fixpoint fib (n : nat) : nat :=\n"
            "  match n with\n"
            "  | 0 => 0\n"
            "  | S 0 => 1\n"
            "  | S (S n') => fib n' + fib (S n')\n"
            "  end.\n\n"
            "Theorem fib_pos : forall n, fib (S n) > 0.\n"
            "Admitted.\n"
        )
        result = rocq_auto_solve(problem=problem, workspace=str(workspace))
        assert result["solved"] is False
        assert "error" in result
        assert isinstance(result["error"], str)
        assert len(result["error"]) > 0


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveEdgeCases:
    """Edge cases for rocq_auto_solve."""

    def test_multiple_theorems_solves_last(self, workspace):
        """When multiple theorems exist, auto_solve solves the LAST one."""
        result = rocq_auto_solve(
            problem=(
                "Lemma helper : True.\n"
                "Proof. exact I. Qed.\n\n"
                "Theorem main : True.\n"
                "Admitted.\n"
            ),
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_proof_admitted_form(self, workspace):
        """Theorem with Proof. Admitted. form should be parsed correctly."""
        result = rocq_auto_solve(
            problem=("Theorem foo : True.\n" "Proof.\n" "  Admitted.\n"),
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_example_keyword(self, workspace):
        """Example keyword should be recognized as theorem-like."""
        result = rocq_auto_solve(
            problem="Example ex : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_fact_keyword(self, workspace):
        """Fact keyword should be recognized."""
        result = rocq_auto_solve(
            problem="Fact fct : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_proposition_keyword(self, workspace):
        """Proposition keyword should be recognized."""
        result = rocq_auto_solve(
            problem="Proposition prop : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_proof_text_format(self, workspace):
        """Verify the proof text is well-formed."""
        result = rocq_auto_solve(
            problem="Theorem fmt : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        if result["solved"]:
            assert result["proof"].startswith("Proof.")
            assert result["proof"].endswith("Qed.")
            # Should contain the winning tactic
            assert result["tactic"] in result["proof"]

    def test_coqc_not_on_path(self, workspace, monkeypatch):
        """When coqc binary is not found, report error."""
        monkeypatch.setattr(
            "rocq_mcp.server.ROCQ_COQC_BINARY", "nonexistent_coqc_binary_xyz"
        )
        result = rocq_auto_solve(
            problem="Theorem t : True.\nAdmitted.\n",
            workspace=str(workspace),
        )
        assert result["solved"] is False

    def test_tauto_propositional(self, workspace):
        """Propositional tautology solved by tauto/intuition."""
        result = rocq_auto_solve(
            problem=(
                "Theorem tauto_test : forall P Q : Prop, P /\\ Q -> Q /\\ P.\n"
                "Admitted.\n"
            ),
            workspace=str(workspace),
        )
        assert result["solved"] is True

    def test_decide_bool(self, workspace):
        """Decidable boolean equality."""
        result = rocq_auto_solve(
            problem=(
                "Require Import Bool.\n\n"
                "Theorem decide_test : true = true.\n"
                "Admitted.\n"
            ),
            workspace=str(workspace),
        )
        assert result["solved"] is True


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveTimeout:
    """Timeout handling for rocq_auto_solve."""

    def test_timeout_short(self, workspace):
        """A trivial problem with a short timeout should still solve successfully."""
        result = rocq_auto_solve(
            problem="Theorem t : True.\nAdmitted.\n",
            workspace=str(workspace),
            timeout=3,
        )
        # This trivial problem should solve even with a 3s timeout.
        assert result["solved"] is True
        assert "tactic" in result
        assert "proof" in result
        assert result["proof"].startswith("Proof.")
        assert result["proof"].endswith("Qed.")

    def test_diverging_preamble_timeout(self, workspace):
        """A problem whose preamble definitions are slow should not hang forever."""
        # Note: auto_solve replaces the proof, so a loop tactic in the original
        # Admitted body does not matter. But we can test with a short timeout.
        result = rocq_auto_solve(
            problem=("Ltac loop := idtac; loop.\n\n" "Theorem t : True.\nAdmitted.\n"),
            workspace=str(workspace),
            timeout=5,
        )
        # Should either solve (the loop tactic is not used) or timeout gracefully
        assert "solved" in result


# ---------------------------------------------------------------------------
# Cleanup
# ---------------------------------------------------------------------------


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestAutoSolveCleanup:
    """rocq_auto_solve should not leave temp files behind."""

    def test_no_artifacts_on_success(self, workspace):
        problem = "Theorem cleanup_test : True.\nAdmitted.\n"
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_auto_solve(problem=problem, workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_failure(self, workspace):
        problem = (
            "Fixpoint double (n : nat) : nat :=\n"
            "  match n with 0 => 0 | S n' => S (S (double n')) end.\n\n"
            "Theorem hard : forall n, double n = n + n.\n"
            "Admitted.\n"
        )
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_auto_solve(problem=problem, workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_validation_error(self, workspace):
        """Even on validation error (no theorem found), no leftover files."""
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_auto_solve(problem="Definition x := 42.\n", workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"
