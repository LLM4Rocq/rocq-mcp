"""End-to-end integration tests.

TestCompileVerifyWorkflow: compile then verify (require coqc)
TestSharedDefsVerifyWorkflow: Phase 2 shared-defs verify (require coqc + pet)
TestQueryStepWorkflow: query then start+check (require pet)
"""

from __future__ import annotations

import asyncio
import glob as glob_mod
import re
from pathlib import Path

import pytest

from tests.conftest import COQC_AVAILABLE, PET_AVAILABLE


def _call_rocq_compile(**kwargs):
    """Run the async server wrapper from synchronous tests."""
    from rocq_mcp.server import rocq_compile

    return asyncio.run(rocq_compile(**kwargs))


# =========================================================================
# Compile -> Verify workflow (Phase 0)
# =========================================================================


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestCompileVerifyWorkflow:
    """End-to-end: compile succeeds, then verify checks correctness."""

    async def test_compile_then_verify_good_proof(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """Full happy path: compile succeeds -> verify succeeds."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = await rocq_compile(
            source=simple_proof, workspace=str(workspace)
        )
        assert compile_result["success"] is True

        verify_result = await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True

    async def test_compile_then_verify_cheat(
        self, workspace, cheating_proof, simple_problem_statement
    ):
        """Cheat is rejected: either compilation fails or verify catches it."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = await rocq_compile(
            source=cheating_proof, workspace=str(workspace)
        )
        # The cheat may or may not compile (depends on exact Rocq version).
        # If compilation already rejects it, the cheat is caught — test passes.
        if not compile_result["success"]:
            return
        # If it compiles, verify must catch it.
        verify_result = await rocq_verify(
            proof=cheating_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is False

    async def test_classical_axiom_accepted(
        self, workspace, classical_proof, classical_problem
    ):
        """Proof using classical logic passes both compile and verify."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = await rocq_compile(
            source=classical_proof, workspace=str(workspace)
        )
        assert compile_result["success"] is True

        verify_result = await rocq_verify(
            proof=classical_proof,
            problem_name="lem_example",
            problem_statement=classical_problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True

    async def test_axiom_spoofing_rejected_end_to_end(
        self, workspace, axiom_spoofing_proof
    ):
        """CRITICAL: end-to-end test that axiom spoofing is caught.

        The proof declares ``Axiom classic : False`` (NOT from stdlib) and
        uses it to prove ``1 = 2``. Compile may succeed, but verify must
        reject it because ``M.classic`` is not a standard axiom.
        """
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = await rocq_compile(
            source=axiom_spoofing_proof, workspace=str(workspace)
        )
        if not compile_result["success"]:
            pytest.skip("axiom spoofing proof did not compile on this Rocq version")
        problem = "Theorem anything : 1 = 2.\nAdmitted.\n"
        verify_result = await rocq_verify(
            proof=axiom_spoofing_proof,
            problem_name="anything",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is False

    async def test_admitted_proof_rejected_end_to_end(
        self, workspace, admitted_proof, simple_problem_statement
    ):
        """Proof with an Admitted helper: compile passes, verify must reject."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = await rocq_compile(
            source=admitted_proof, workspace=str(workspace)
        )
        assert compile_result["success"] is True
        verify_result = await rocq_verify(
            proof=admitted_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is False

    async def test_print_assumptions_injection_rejected(self, workspace):
        """CRITICAL: Print Assumptions stdout injection must not bypass verification.

        The proof injects ``Print Assumptions clean.`` inside Module M,
        producing ``Closed under the global context`` on stdout before the
        template's real ``Print Assumptions`` output.  The parser must use
        the LAST output block and correctly detect the Admitted helper.
        """
        from rocq_mcp.server import rocq_compile, rocq_verify

        injection_proof = (
            "From Coq Require Import Arith.\n\n"
            "Lemma helper : forall n : nat, n + 0 = n. Admitted.\n"
            "Lemma clean : True. Proof. exact I. Qed.\n"
            "Print Assumptions clean.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Proof.\n"
            "  intros n. apply helper.\n"
            "Qed.\n"
        )
        problem = (
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        compile_result = await rocq_compile(
            source=injection_proof, workspace=str(workspace)
        )
        assert compile_result["success"] is True

        verify_result = await rocq_verify(
            proof=injection_proof,
            problem_name="add_0_r",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is False, (
            "Print Assumptions stdout injection bypassed verification! "
            f"Result: {verify_result}"
        )

    def test_compile_rejects_forbidden_redirect(self, workspace):
        """rocq_compile must reject source containing Redirect."""
        from rocq_mcp.server import rocq_compile

        result = _call_rocq_compile(
            source='Redirect "/tmp/evil" Print nat.\nTheorem t : True. Proof. exact I. Qed.',
            workspace=str(workspace),
        )
        assert result["success"] is False
        assert "forbidden" in result["error"].lower()

    def test_compile_rejects_forbidden_load(self, workspace):
        """rocq_compile must reject source containing Load."""
        from rocq_mcp.server import rocq_compile

        result = _call_rocq_compile(
            source='Load "evil".\nTheorem t : True. Proof. exact I. Qed.',
            workspace=str(workspace),
        )
        assert result["success"] is False
        assert "forbidden" in result["error"].lower()

    def test_compile_rejects_forbidden_drop(self, workspace):
        """rocq_compile must reject source containing Drop."""
        from rocq_mcp.server import rocq_compile

        result = _call_rocq_compile(
            source="Drop.\nTheorem t : True. Proof. exact I. Qed.",
            workspace=str(workspace),
        )
        assert result["success"] is False
        assert "forbidden" in result["error"].lower()

    def test_compile_with_coqproject(self, tmp_path):
        """rocq_compile resolves local imports via _CoqProject flags."""
        import subprocess

        from rocq_mcp.server import rocq_compile, ROCQ_COQC_BINARY

        # Set up a mini project with a helper module
        (tmp_path / "_CoqProject").write_text("-Q . TestProj\n")
        (tmp_path / "Helper.v").write_text("Definition my_const : nat := 42.\n")

        # Compile Helper.v directly with coqc to produce Helper.vo
        subprocess.run(
            [ROCQ_COQC_BINARY, "-Q", ".", "TestProj", "Helper.v"],
            cwd=str(tmp_path),
            check=True,
        )

        # Now compile source that imports Helper via rocq_compile
        result = _call_rocq_compile(
            source=(
                "From TestProj Require Import Helper.\n" "Definition x := my_const.\n"
            ),
            workspace=str(tmp_path),
        )
        assert result["success"] is True, f"Failed: {result.get('error', '')}"

    async def test_verify_with_coqproject(self, tmp_path):
        """rocq_verify works with local imports resolved via _CoqProject."""
        import subprocess

        from rocq_mcp.server import rocq_compile, rocq_verify, ROCQ_COQC_BINARY

        # Set up a mini project
        (tmp_path / "_CoqProject").write_text("-Q . TestProj\n")
        (tmp_path / "Helper.v").write_text("Definition my_const : nat := 42.\n")
        subprocess.run(
            [ROCQ_COQC_BINARY, "-Q", ".", "TestProj", "Helper.v"],
            cwd=str(tmp_path),
            check=True,
        )

        proof = (
            "From TestProj Require Import Helper.\n"
            "Theorem t : my_const = 42.\n"
            "Proof. reflexivity. Qed.\n"
        )
        problem = (
            "From TestProj Require Import Helper.\n"
            "Theorem t : my_const = 42.\n"
            "Admitted.\n"
        )

        compile_result = await rocq_compile(source=proof, workspace=str(tmp_path))
        assert compile_result["success"] is True

        verify_result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(tmp_path),
        )
        assert (
            verify_result["verified"] is True
        ), f"Verify failed: {verify_result.get('error', '')}"

    async def test_no_artifacts_after_workflow(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """No temp files should remain after a full compile+verify cycle."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        before = set(glob_mod.glob(str(workspace / "*")))
        await rocq_compile(source=simple_proof, workspace=str(workspace))
        await rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    async def test_multiline_import_compile_verify(
        self, workspace, multiline_import_proof
    ):
        """Multi-line From...Require Import works end-to-end."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = await rocq_compile(
            source=multiline_import_proof, workspace=str(workspace)
        )
        assert compile_result["success"] is True

        problem = (
            "From Coq Require Import\n"
            "  Arith\n"
            "  Lia.\n\n"
            "Theorem test : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        verify_result = await rocq_verify(
            proof=multiline_import_proof,
            problem_name="test",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True


# =========================================================================
# Shared-defs (Phase 2) verify workflow (require coqc + pet)
# =========================================================================


class _MockContext:
    """Minimal mock for FastMCP Context to inject lifespan_state."""

    def __init__(self, lifespan_state):
        self.lifespan_context = lifespan_state


@pytest.mark.skipif(
    not (COQC_AVAILABLE and PET_AVAILABLE),
    reason="coqc and pet required for compile error state capture",
)
class TestCompileErrorStateWorkflow:
    """End-to-end: compile errors should include the current proof state."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = {"pet_client": None, "pet_timeout": 30.0, "current_workspace": None}
        yield state
        _invalidate_pet(state)

    async def test_compile_includes_error_state(self, lifespan_state, workspace):
        """rocq_compile should attach a recoverable state at the error position."""
        from rocq_mcp.server import rocq_compile

        source = "Theorem bad : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n"
        ctx = _MockContext(lifespan_state)

        result = await rocq_compile(source=source, workspace=str(workspace), ctx=ctx)

        assert result["success"] is False
        assert isinstance(result["state_id"], int)
        assert "|-True" in result["goals"]
        assert result["file"] == "<proof>"
        # Position is on line 2 (0-indexed: the `exact 0.` line);
        # the column is set by coqc and may shift across Rocq versions.
        assert result["theorem"].startswith("@pos(2,")
        assert result["proof_finished"] is False

    async def test_compile_file_includes_error_state(self, lifespan_state, workspace):
        """rocq_compile_file should attach a recoverable state at the error position."""
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "error_state_test.v"
        path.write_text("Theorem bad : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")
        ctx = _MockContext(lifespan_state)

        result = await rocq_compile_file(
            file="error_state_test.v",
            workspace=str(workspace),
            ctx=ctx,
        )

        assert result["success"] is False
        assert isinstance(result["state_id"], int)
        assert "|-True" in result["goals"]
        assert result["file"] == "error_state_test.v"
        assert result["theorem"].startswith("@pos(2,")
        assert result["proof_finished"] is False

    async def test_compile_with_assumption_includes_goal_context(
        self, lifespan_state, workspace
    ):
        """Captured goals should include local assumptions from the proof state."""
        from rocq_mcp.server import rocq_compile

        source = "Lemma bad (n : nat) : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n"
        ctx = _MockContext(lifespan_state)

        result = await rocq_compile(source=source, workspace=str(workspace), ctx=ctx)

        assert result["success"] is False
        assert "n : nat" in result["goals"]
        assert "|-True" in result["goals"]
        assert result["file"] == "<proof>"
        assert result["theorem"].startswith("@pos(2,")
        assert result["proof_finished"] is False

    async def test_compile_multiple_tactics_same_line_uses_later_error_position(
        self, lifespan_state, workspace
    ):
        """Error-state capture should point after earlier successful tactics."""
        from rocq_mcp.server import rocq_compile

        source = (
            "Lemma bad (n : nat) : True.\n" "Proof.\n" "  idtac. exact 0.\n" "Qed.\n"
        )
        ctx = _MockContext(lifespan_state)

        result = await rocq_compile(source=source, workspace=str(workspace), ctx=ctx)

        assert result["success"] is False
        assert "n : nat" in result["goals"]
        assert "|-True" in result["goals"]
        assert result["file"] == "<proof>"
        # Capture must point on line 2 and *after* the prior `idtac.` so
        # the goal reflects the earlier successful tactic.  The exact
        # column is coqc-reported and may shift across Rocq versions.
        m = re.match(r"@pos\((\d+),(\d+)\)", result["theorem"])
        assert m, f"theorem should be @pos(line,col), got {result['theorem']!r}"
        line, col = int(m.group(1)), int(m.group(2))
        assert line == 2
        assert col > len("  idtac."), (
            f"position should be past 'idtac.' (col >{len('  idtac.')}), "
            f"got col={col}"
        )
        assert result["proof_finished"] is False


@pytest.mark.skipif(
    not (COQC_AVAILABLE and PET_AVAILABLE),
    reason="coqc and pet required for Phase 2 verification",
)
class TestSharedDefsVerifyWorkflow:
    """End-to-end: Phase 2 shared-defs verification via pytanque toc."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = {"pet_client": None, "pet_timeout": 30.0}
        yield state
        _invalidate_pet(state)

    async def test_phase2_verify_with_inductive(self, lifespan_state, workspace):
        """Inductive type in problem triggers Phase 2 and succeeds."""
        from rocq_mcp.server import rocq_verify

        problem = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_refl : forall c : color, c = c.\n"
            "Admitted.\n"
        )
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_refl : forall c : color, c = c.\n"
            "Proof. destruct c; reflexivity. Qed.\n"
        )

        ctx = _MockContext(lifespan_state)
        result = await rocq_verify(
            proof=proof,
            problem_name="color_refl",
            problem_statement=problem,
            workspace=str(workspace),
            ctx=ctx,
        )

        assert result["verified"] is True
        assert result["verification_method"] == "shared_defs"

    async def test_phase1_verify_no_fallback(self, lifespan_state, workspace):
        """Simple theorem without Inductive types should verify via Phase 1."""
        from rocq_mcp.server import rocq_verify

        problem = "Theorem t : True.\nAdmitted.\n"
        proof = "Theorem t : True.\nProof. exact I. Qed.\n"

        ctx = _MockContext(lifespan_state)
        result = await rocq_verify(
            proof=proof,
            problem_name="t",
            problem_statement=problem,
            workspace=str(workspace),
            ctx=ctx,
        )
        assert result["verified"] is True
        assert result["verification_method"] == "module_m"

    async def test_phase2_with_definition_and_inductive(
        self, lifespan_state, workspace
    ):
        """Definition + Inductive in problem triggers Phase 2 and succeeds."""
        from rocq_mcp.server import rocq_verify

        problem = (
            "Definition mynat := nat.\n"
            "Inductive mylist : Type := Nil | Cons : mynat -> mylist -> mylist.\n"
            "Theorem mylist_refl : forall l : mylist, l = l.\n"
            "Admitted.\n"
        )
        proof = (
            "Definition mynat := nat.\n"
            "Inductive mylist : Type := Nil | Cons : mynat -> mylist -> mylist.\n"
            "Theorem mylist_refl : forall l : mylist, l = l.\n"
            "Proof. destruct l; reflexivity. Qed.\n"
        )

        ctx = _MockContext(lifespan_state)
        result = await rocq_verify(
            proof=proof,
            problem_name="mylist_refl",
            problem_statement=problem,
            workspace=str(workspace),
            ctx=ctx,
        )

        assert result["verified"] is True
        assert result["verification_method"] == "shared_defs"

    async def test_phase2_rejects_admitted(self, lifespan_state, workspace):
        """Cheating proof with Admitted inside Phase 2 is rejected."""
        from rocq_mcp.server import rocq_verify

        problem = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_count : Red <> Blue.\n"
            "Admitted.\n"
        )
        proof = (
            "Inductive color := Red | Green | Blue.\n"
            "Theorem color_count : Red <> Blue.\n"
            "Proof. Admitted.\n"
        )

        ctx = _MockContext(lifespan_state)
        result = await rocq_verify(
            proof=proof,
            problem_name="color_count",
            problem_statement=problem,
            workspace=str(workspace),
            ctx=ctx,
        )

        assert result["verified"] is False

    async def test_phase2_with_require_import_no_defs(self, lifespan_state, workspace):
        """Require Import Znumtheory without Inductive/Def triggers Phase 2.

        Znumtheory's Require inside Module M is fragile and may cause
        failures on some Rocq versions.  Phase 2 extracts the preamble
        outside Module M, making verification succeed.
        """
        from rocq_mcp.server import rocq_verify

        problem = (
            "Require Import Nat.\n"
            "Require Import ZArith.\n"
            "From Coq Require Import Znumtheory.\n"
            "Require Import Lia.\n"
            "Open Scope Z_scope.\n\n"
            "Theorem simple_z : forall n : Z,\n"
            "  (0 <= n)%Z -> (0 <= n)%Z.\n"
            "Admitted.\n"
        )
        proof = (
            "Require Import Nat.\n"
            "Require Import ZArith.\n"
            "From Coq Require Import Znumtheory.\n"
            "Require Import Lia.\n"
            "Open Scope Z_scope.\n\n"
            "Theorem simple_z : forall n : Z,\n"
            "  (0 <= n)%Z -> (0 <= n)%Z.\n"
            "Proof. auto. Qed.\n"
        )

        ctx = _MockContext(lifespan_state)
        result = await rocq_verify(
            proof=proof,
            problem_name="simple_z",
            problem_statement=problem,
            workspace=str(workspace),
            ctx=ctx,
        )

        assert result["verified"] is True


# =========================================================================
# Query -> Start+Check workflow (require pet)
# =========================================================================


@pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")
class TestQueryStepWorkflow:
    """End-to-end: query to search, then start+check to prove a theorem."""

    @pytest.fixture(autouse=True)
    def _reset_state(self):
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        yield
        _state_invalidate_all()

    @staticmethod
    def _make_state(timeout: float = 30.0) -> dict:
        return {"pet_client": None, "pet_timeout": timeout}

    @pytest.mark.asyncio
    async def test_query_then_step(self, workspace):
        """Use query to find a lemma, then start+check to prove a theorem."""
        from rocq_mcp.interactive import run_query, run_start, run_check
        from rocq_mcp.server import _invalidate_pet

        state = self._make_state()
        try:
            # Query: search for addition lemmas
            qr = await run_query(
                command="Search (nat -> nat -> nat).",
                preamble="",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert qr["success"] is True
            assert "Nat.add" in qr["output"]

            # Start proof context
            vfile = workspace / "query_step_test.v"
            vfile.write_text(
                "Theorem t : forall n : nat, n = n.\n"
                "Proof. intros. reflexivity. Qed.\n"
            )

            r1 = await run_start(
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r1["success"] is True
            start_id = r1["state_id"]

            # Execute first tactic
            r2 = await run_check(
                body="intros.",
                timeout=30.0,
                lifespan_state=state,
                from_state=start_id,
            )
            assert r2["success"] is True
            assert r2["proof_finished"] is False
            intros_id = r2["state_id"]

            # Execute second tactic to finish proof
            r3 = await run_check(
                body="reflexivity.",
                timeout=30.0,
                lifespan_state=state,
                from_state=intros_id,
            )
            assert r3["success"] is True
            assert r3["proof_finished"] is True
        finally:
            _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_pet_respawns_after_kill(self, workspace):
        """Kill pet via timeout, verify next query call respawns it."""
        from rocq_mcp.interactive import run_start, run_check, run_query
        from rocq_mcp.server import _invalidate_pet

        vfile = workspace / "respawn_test.v"
        # Define the looping tactic but use a non-diverging proof body.
        # coq-lsp processes the full file during pet.start(), so the file
        # itself must not diverge. The loop is tested via run_check.
        vfile.write_text(
            "Ltac loop := idtac; loop.\n" "Theorem t : True. Proof. exact I. Qed.\n"
        )

        # Use a normal timeout for start (pet compilation takes time),
        # then pass a short timeout to run_check for the looping tactic.
        state = self._make_state(timeout=30.0)
        try:
            r0 = await run_start(
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r0["success"] is True
            start_id = r0["state_id"]

            # Trigger timeout via looping tactic -- kills pet
            r1 = await run_check(
                body="loop.",
                timeout=1.0,
                lifespan_state=state,
                from_state=start_id,
            )
            assert r1["success"] is False
            err_lower = r1.get("error", "").lower()
            assert (
                "timed out" in err_lower
                or "timeout" in err_lower
                or r1.get("pet_restarted") is True
            )

            # Increase timeout for recovery
            state["pet_timeout"] = 30.0

            # Query should respawn pet and work
            qr = await run_query(
                command="Check Nat.add.",
                preamble="",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert qr["success"] is True
            assert "nat" in qr["output"].lower()
        finally:
            _invalidate_pet(state)


# =========================================================================
# MiniF2F sample test (optional, runs only if workspace exists)
# =========================================================================


class TestMiniF2FSample:
    """Test with a real miniF2F problem if the workspace is available."""

    MINIF2F_WORKSPACE = "/Users/gbaudart/Project/llm4rocq/miniF2F-rocq/test"

    @pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
    def test_real_problem_compile(self):
        """Compile a real miniF2F problem statement (expect Admitted to fail)."""
        ws = Path(self.MINIF2F_WORKSPACE)
        if not ws.is_dir():
            pytest.skip("miniF2F workspace not available")

        from rocq_mcp.server import rocq_compile

        # Find any .v file in the workspace
        v_files = list(ws.glob("*.v"))
        if not v_files:
            pytest.skip("No .v files found in miniF2F workspace")

        problem_path = v_files[0]
        source = problem_path.read_text()

        # The problem file likely ends with Admitted, so compilation should
        # succeed (Admitted is accepted by coqc). We just verify no crash.
        result = _call_rocq_compile(source=source, workspace=str(ws))
        assert "success" in result
