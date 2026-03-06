"""End-to-end integration tests.

TestCompileVerifyWorkflow: compile then verify (require coqc)
TestQueryStepWorkflow: query then step (require pet, placeholders)
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

        compile_result = rocq_compile(
            source=simple_proof, workspace=str(workspace)
        )
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

        compile_result = rocq_compile(
            source=cheating_proof, workspace=str(workspace)
        )
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

        compile_result = rocq_compile(
            source=classical_proof, workspace=str(workspace)
        )
        assert compile_result["success"] is True

        verify_result = rocq_verify(
            proof=classical_proof,
            problem_name="lem_example",
            problem_statement=classical_problem,
            workspace=str(workspace),
        )
        assert verify_result["verified"] is True

    def test_axiom_spoofing_rejected_end_to_end(
        self, workspace, axiom_spoofing_proof
    ):
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

        compile_result = rocq_compile(
            source=admitted_proof, workspace=str(workspace)
        )
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

    def test_multiline_import_compile_verify(
        self, workspace, multiline_import_proof
    ):
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
# Query -> Step workflow (Phase 1-2, placeholders)
# =========================================================================

@pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")
class TestQueryStepWorkflow:
    """End-to-end: query to search, then step to apply found lemma."""

    @pytest.mark.asyncio
    async def test_query_then_step(self):
        """Use query to search for a lemma, then step to apply it."""
        # Phase 1-2 placeholder: requires FastMCP test client for Context injection
        # 1. query: Search (nat -> nat -> nat).
        # 2. step: intros, apply Nat.add
        pass

    @pytest.mark.asyncio
    async def test_pet_respawns_after_kill(self):
        """Kill pet via timeout, verify next call respawns it."""
        # 1. Trigger timeout in rocq_step (repeat idtac)
        # 2. Make a rocq_query call -- pet should respawn
        # assert result["success"] is True
        pass


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
