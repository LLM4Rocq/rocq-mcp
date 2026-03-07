"""End-to-end integration tests.

TestCompileVerifyWorkflow: compile then verify (require coqc)
TestQueryStepWorkflow: query then step (require pet)
"""

from __future__ import annotations

import glob as glob_mod
from pathlib import Path

import pytest

from tests.conftest import COQC_AVAILABLE, PET_AVAILABLE

# =========================================================================
# Compile -> Verify workflow (Phase 0)
# =========================================================================


@pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
class TestCompileVerifyWorkflow:
    """End-to-end: compile succeeds, then verify checks correctness."""

    def test_compile_then_verify_good_proof(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """Full happy path: compile succeeds -> verify succeeds."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = rocq_compile(source=simple_proof, workspace=str(workspace))
        assert compile_result["success"] is True

        verify_result = rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True

    def test_compile_then_verify_cheat(
        self, workspace, cheating_proof, simple_problem_statement
    ):
        """Compile may succeed but verify catches the type-redefinition cheat."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = rocq_compile(source=cheating_proof, workspace=str(workspace))
        # The cheat may or may not compile (depends on exact Rocq version)
        # The critical assertion is that verify rejects it.
        if compile_result["success"]:
            verify_result = rocq_verify(
                proof=cheating_proof,
                problem_name="add_0_r",
                problem_statement=simple_problem_statement,
                workspace=str(workspace),
            )
            assert verify_result["verified"] is False

    def test_classical_axiom_accepted(
        self, workspace, classical_proof, classical_problem
    ):
        """Proof using classical logic passes both compile and verify."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = rocq_compile(source=classical_proof, workspace=str(workspace))
        assert compile_result["success"] is True

        verify_result = rocq_verify(
            proof=classical_proof,
            problem_name="lem_example",
            problem_statement=classical_problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True

    def test_axiom_spoofing_rejected_end_to_end(self, workspace, axiom_spoofing_proof):
        """CRITICAL: end-to-end test that axiom spoofing is caught.

        The proof declares ``Axiom classic : False`` (NOT from stdlib) and
        uses it to prove ``1 = 2``. Compile may succeed, but verify must
        reject it because ``M.classic`` is not a standard axiom.
        """
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = rocq_compile(
            source=axiom_spoofing_proof, workspace=str(workspace)
        )
        if compile_result["success"]:
            problem = "Theorem anything : 1 = 2.\nAdmitted.\n"
            verify_result = rocq_verify(
                proof=axiom_spoofing_proof,
                problem_name="anything",
                problem_statement=problem,
                workspace=str(workspace),
            )
            assert verify_result["verified"] is False

    def test_admitted_proof_rejected_end_to_end(
        self, workspace, admitted_proof, simple_problem_statement
    ):
        """Proof with an Admitted helper: compile may pass, verify must reject."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = rocq_compile(source=admitted_proof, workspace=str(workspace))
        if compile_result["success"]:
            verify_result = rocq_verify(
                proof=admitted_proof,
                problem_name="add_0_r",
                problem_statement=simple_problem_statement,
                workspace=str(workspace),
            )
            assert verify_result["verified"] is False

    def test_no_artifacts_after_workflow(
        self, workspace, simple_proof, simple_problem_statement
    ):
        """No temp files should remain after a full compile+verify cycle."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_compile(source=simple_proof, workspace=str(workspace))
        rocq_verify(
            proof=simple_proof,
            problem_name="add_0_r",
            problem_statement=simple_problem_statement,
            workspace=str(workspace),
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_multiline_import_compile_verify(self, workspace, multiline_import_proof):
        """Multi-line From...Require Import works end-to-end."""
        from rocq_mcp.server import rocq_compile, rocq_verify

        compile_result = rocq_compile(
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
        verify_result = rocq_verify(
            proof=multiline_import_proof,
            problem_name="test",
            problem_statement=problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True


# =========================================================================
# Query -> Step workflow (require pet)
# =========================================================================


@pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")
class TestQueryStepWorkflow:
    """End-to-end: query to search, then step to apply found lemma."""

    @pytest.fixture(autouse=True)
    def _reset_session(self):
        from rocq_mcp.server import _session

        _session.update({"state": None, "file": None, "theorem": None, "history": []})
        yield
        _session.update({"state": None, "file": None, "theorem": None, "history": []})

    @staticmethod
    def _make_state(timeout: float = 30.0) -> dict:
        return {"pet_client": None, "pet_timeout": timeout}

    @pytest.mark.asyncio
    async def test_query_then_step(self, workspace):
        """Use query to find a lemma, then step through a proof using it."""
        from rocq_mcp.server import run_query, run_step, _invalidate_pet

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

            # Step: prove a simple theorem using what we found
            vfile = workspace / "query_step_test.v"
            vfile.write_text(
                "Theorem t : forall n : nat, n = n.\n"
                "Proof. intros. reflexivity. Qed.\n"
            )

            r1 = await run_step(
                tactic="intros",
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r1["success"] is True
            assert r1["proof_finished"] is False

            r2 = await run_step(
                tactic="reflexivity",
                file="",
                theorem="",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r2["success"] is True
            assert r2["proof_finished"] is True
        finally:
            _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_pet_respawns_after_kill(self, workspace):
        """Kill pet via timeout, verify next query call respawns it."""
        from rocq_mcp.server import run_step, run_query, _invalidate_pet

        vfile = workspace / "respawn_test.v"
        vfile.write_text(
            "Ltac loop := idtac; loop.\n" "Theorem t : True. Proof. loop. Qed.\n"
        )

        state = self._make_state(timeout=1.0)
        try:
            # Trigger timeout — kills pet
            r1 = await run_step(
                tactic="loop",
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r1["success"] is False
            assert "timed out" in r1["error"].lower()

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
        result = rocq_compile(source=source, workspace=str(ws))
        assert "success" in result
