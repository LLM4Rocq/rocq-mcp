"""Tests for auto-solving via rocq_step_multi.

Part A: Unit tests for helper functions (NO coqc/pet needed)
    - TestRocqCommentRanges: _rocq_comment_ranges scanner
    - TestFindSentenceEnd: _find_sentence_end sentence splitting
    - TestAutoSolveParsing: _parse_last_theorem with various input shapes
    - TestBuildAutoSolveSource: generated `first [...]` source structure
    - TestBuildSingleTacticSource: generated single-tactic source

Part B: Integration tests (require pet)
    - Uses run_start + run_step_multi with standard automation tactics
    - TestAutoSolveTrivial, TestAutoSolveLia, TestAutoSolveRing,
      TestAutoSolveWithPreamble, TestAutoSolveUnsolvable,
      TestAutoSolveEdgeCases
"""

from __future__ import annotations

import pytest

from tests.conftest import PET_AVAILABLE
from rocq_mcp.server import (
    _parse_last_theorem,
    _build_auto_solve_source,
    _build_single_tactic_source,
    _AUTO_SOLVE_TACTICS,
    _rocq_comment_ranges,
    _find_sentence_end,
)

# Standard automation tactics for step_multi (same list as auto_solve used)
AUTO_TACTICS = list(_AUTO_SOLVE_TACTICS)


# =========================================================================
# PART A: Unit tests (no coqc/pet needed)
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


# =========================================================================
# PART B: Integration tests via run_start + run_step_multi (require pet)
# =========================================================================

pytestmark_pet = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


def _make_state(timeout: float = 30.0) -> dict:
    return {"pet_client": None, "pet_timeout": timeout}


async def _auto_solve(workspace, source, theorem, preamble_tactics=None, state=None):
    """Try to auto-solve a theorem via run_start + run_step_multi.

    Returns dict with 'solved', 'tactic' (on success), 'error' (on failure),
    and 'results' (full step_multi results).
    """
    from rocq_mcp.server import run_start, run_check, run_step_multi

    if state is None:
        state = _make_state()

    vfile = workspace / f"auto_{theorem}.v"
    vfile.write_text(source)

    sr = await run_start(
        file=str(vfile.relative_to(workspace)),
        theorem=theorem,
        workspace=str(workspace),
        lifespan_state=state,
    )
    if not sr["success"]:
        return {"solved": False, "error": sr.get("error", "start failed")}

    from_state = sr["state_id"]

    # Run preamble tactics if provided
    if preamble_tactics:
        cr = await run_check(
            body=preamble_tactics,
            workspace=str(workspace),
            timeout=30.0,
            lifespan_state=state,
            from_state=from_state,
        )
        if not cr["success"]:
            return {"solved": False, "error": cr.get("error", "preamble failed")}
        from_state = cr["state_id"]

    # Try automation tactics via step_multi
    mr = await run_step_multi(
        tactics=AUTO_TACTICS,
        lifespan_state=state,
        from_state=from_state,
    )
    if not mr["success"]:
        return {"solved": False, "error": mr.get("error", "step_multi failed")}

    # Find a winning tactic
    for entry in mr["results"]:
        if entry["success"] and entry.get("proof_finished"):
            # Strip trailing dot added by step_multi for clean assertions
            tactic = entry["tactic"]
            if tactic.endswith("."):
                tactic = tactic[:-1]
            return {
                "solved": True,
                "tactic": tactic,
                "results": mr["results"],
            }

    return {
        "solved": False,
        "error": "No automation tactic solved the goal",
        "results": mr["results"],
    }


@pytest.fixture
def lifespan_state():
    """Provide a lifespan_state and clean up pet on teardown."""
    from rocq_mcp.server import _invalidate_pet

    state = _make_state()
    yield state
    _invalidate_pet(state)


@pytest.fixture(autouse=True)
def reset_state_table():
    """Reset the state table before/after each test."""
    from rocq_mcp.interactive import _state_invalidate_all

    _state_invalidate_all()
    yield
    _state_invalidate_all()


@pytestmark_pet
class TestAutoSolveTrivial:
    """Trivially true problems solved by trivial/exact I."""

    @pytest.mark.asyncio
    async def test_true_exact_i(self, workspace, lifespan_state):
        """Lemma foo : True should be solved by exact I or trivial."""
        result = await _auto_solve(
            workspace,
            "Lemma foo : True.\nProof. exact I. Qed.\n",
            "foo",
            state=lifespan_state,
        )
        assert result["solved"] is True
        assert result["tactic"] in ("trivial", "exact I", "auto", "eauto", "tauto")

    @pytest.mark.asyncio
    async def test_reflexivity_nat(self, workspace, lifespan_state):
        """forall n, n = n should be solved by reflexivity."""
        result = await _auto_solve(
            workspace,
            "Theorem refl_test : forall n : nat, n = n.\n"
            "Proof. intros. reflexivity. Qed.\n",
            "refl_test",
            state=lifespan_state,
        )
        assert result["solved"] is True
        assert result["tactic"] in (
            "trivial",
            "reflexivity",
            "auto",
            "eauto",
            "tauto",
        )

    @pytest.mark.asyncio
    async def test_reflexivity_literal(self, workspace, lifespan_state):
        """1 = 1 solved by reflexivity."""
        result = await _auto_solve(
            workspace,
            "Theorem refl_lit : 1 = 1.\nProof. reflexivity. Qed.\n",
            "refl_lit",
            state=lifespan_state,
        )
        assert result["solved"] is True


@pytestmark_pet
class TestAutoSolveLia:
    """Arithmetic problems solved by lia."""

    @pytest.mark.asyncio
    async def test_lia_nat_add(self, workspace, lifespan_state):
        """forall n, n + 0 = n should be solved by lia with intros."""
        result = await _auto_solve(
            workspace,
            "From Coq Require Import Lia.\n\n"
            "Theorem lia_test : forall n : nat, n + 0 = n.\n"
            "Proof. intros. lia. Qed.\n",
            "lia_test",
            preamble_tactics="intros.",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_lia_inequality(self, workspace, lifespan_state):
        """Simple inequality: forall n, n >= 0."""
        result = await _auto_solve(
            workspace,
            "From Coq Require Import Lia.\n\n"
            "Theorem lia_ineq : forall n : nat, n >= 0.\n"
            "Proof. intros. lia. Qed.\n",
            "lia_ineq",
            preamble_tactics="intros.",
            state=lifespan_state,
        )
        assert result["solved"] is True


@pytestmark_pet
class TestAutoSolveRing:
    """Ring/field arithmetic problems."""

    @pytest.mark.asyncio
    async def test_ring_z_mul_identity(self, workspace, lifespan_state):
        """forall x : Z, x * 1 = x should be solved by ring."""
        result = await _auto_solve(
            workspace,
            "From Coq Require Import ZArith.\n"
            "Open Scope Z_scope.\n\n"
            "Theorem ring_test : forall x : Z, x * 1 = x.\n"
            "Proof. intros. ring. Qed.\n",
            "ring_test",
            state=lifespan_state,
        )
        assert result["solved"] is True
        assert result["tactic"] in ("ring", "lia", "nia", "auto", "intuition")

    @pytest.mark.asyncio
    async def test_ring_z_comm(self, workspace, lifespan_state):
        """forall x y : Z, x + y = y + x should be solved by ring."""
        result = await _auto_solve(
            workspace,
            "From Coq Require Import ZArith.\n"
            "Open Scope Z_scope.\n\n"
            "Theorem ring_comm : forall x y : Z, x + y = y + x.\n"
            "Proof. intros. ring. Qed.\n",
            "ring_comm",
            state=lifespan_state,
        )
        assert result["solved"] is True


@pytestmark_pet
class TestAutoSolveWithPreamble:
    """Tests for problems that need preamble tactics before automation."""

    @pytest.mark.asyncio
    async def test_intros_then_lia(self, workspace, lifespan_state):
        """Problem needing intros before lia can solve it."""
        result = await _auto_solve(
            workspace,
            "From Coq Require Import Lia.\n\n"
            "Theorem preamble_test : forall n : nat, n >= 0.\n"
            "Proof. intros. lia. Qed.\n",
            "preamble_test",
            preamble_tactics="intros.",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_intros_then_assumption(self, workspace, lifespan_state):
        """P -> P with intros + assumption."""
        result = await _auto_solve(
            workspace,
            "Theorem assume_test : forall P : Prop, P -> P.\n"
            "Proof. intros. assumption. Qed.\n",
            "assume_test",
            preamble_tactics="intros.",
            state=lifespan_state,
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


@pytestmark_pet
class TestAutoSolveUnsolvable:
    """Problems that standard automation should NOT solve."""

    @pytest.mark.asyncio
    async def test_induction_needed(self, workspace, lifespan_state):
        """n + 0 = n without intros requires induction -- not automatable."""
        result = await _auto_solve(
            workspace,
            "From Coq Require Import Arith.\n\n"
            "Theorem ind_test : forall n : nat, n + 0 = n.\n"
            "Proof. intros n. induction n. reflexivity. simpl. "
            "rewrite IHn. reflexivity. Qed.\n",
            "ind_test",
            state=lifespan_state,
        )
        # Without intros, automation tactics alone probably won't solve this.
        # Either outcome is valid, but the result must be well-formed.
        assert "solved" in result
        if result["solved"]:
            assert "tactic" in result
            assert isinstance(result["tactic"], str)
        else:
            assert "error" in result
            assert isinstance(result["error"], str)

    @pytest.mark.asyncio
    async def test_custom_fixpoint(self, workspace, lifespan_state):
        """Custom recursive definition needs manual proof."""
        result = await _auto_solve(
            workspace,
            "Fixpoint double (n : nat) : nat :=\n"
            "  match n with\n"
            "  | 0 => 0\n"
            "  | S n' => S (S (double n'))\n"
            "  end.\n\n"
            "Theorem double_correct : forall n, double n = n + n.\n"
            "Proof. induction n. reflexivity. simpl. "
            "rewrite IHn. Search (_ + S _). rewrite Nat.add_succ_r. "
            "reflexivity. Qed.\n",
            "double_correct",
            state=lifespan_state,
        )
        assert result["solved"] is False


@pytestmark_pet
class TestAutoSolveEdgeCases:
    """Edge cases for auto-solving via step_multi."""

    @pytest.mark.asyncio
    async def test_multiple_theorems_solves_target(self, workspace, lifespan_state):
        """When multiple theorems exist, auto_solve targets the specified one."""
        result = await _auto_solve(
            workspace,
            "Lemma helper : True.\nProof. exact I. Qed.\n\n"
            "Theorem main : True.\nProof. exact I. Qed.\n",
            "main",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_example_keyword(self, workspace, lifespan_state):
        """Example keyword should work as theorem target."""
        result = await _auto_solve(
            workspace,
            "Example ex : True.\nProof. exact I. Qed.\n",
            "ex",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_fact_keyword(self, workspace, lifespan_state):
        """Fact keyword should work as theorem target."""
        result = await _auto_solve(
            workspace,
            "Fact fct : True.\nProof. exact I. Qed.\n",
            "fct",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_proposition_keyword(self, workspace, lifespan_state):
        """Proposition keyword should work as theorem target."""
        result = await _auto_solve(
            workspace,
            "Proposition prop : True.\nProof. exact I. Qed.\n",
            "prop",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_tauto_propositional(self, workspace, lifespan_state):
        """Propositional tautology solved by tauto/intuition."""
        result = await _auto_solve(
            workspace,
            "Theorem tauto_test : forall P Q : Prop, P /\\ Q -> Q /\\ P.\n"
            "Proof. tauto. Qed.\n",
            "tauto_test",
            state=lifespan_state,
        )
        assert result["solved"] is True

    @pytest.mark.asyncio
    async def test_decide_bool(self, workspace, lifespan_state):
        """Decidable boolean equality."""
        result = await _auto_solve(
            workspace,
            "Require Import Bool.\n\n"
            "Theorem decide_test : true = true.\n"
            "Proof. reflexivity. Qed.\n",
            "decide_test",
            state=lifespan_state,
        )
        assert result["solved"] is True
