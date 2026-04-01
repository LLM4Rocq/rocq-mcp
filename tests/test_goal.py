"""Tests for the rocq_goal tool.

Tests are grouped into:
- TestGoalPathValidation: path traversal and bounds validation
- TestGoalMocked: mock pet for basic goal retrieval
- TestGoalIntegration: real pet integration tests
- TestRocqGoalWrapper: MCP wrapper validation
"""

from __future__ import annotations

import asyncio
import os
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from rocq_mcp.interactive import run_goal
from tests.conftest import PET_AVAILABLE

_pet_only = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


# ---------------------------------------------------------------------------
# TestGoalPathValidation
# ---------------------------------------------------------------------------


class TestGoalPathValidation:
    """Test that path traversal and bounds are rejected."""

    def test_absolute_path_rejected(self, tmp_path):
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_goal(
                file="/etc/passwd",
                line=0,
                character=0,
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "workspace" in result["error"].lower()

    def test_dotdot_traversal_rejected(self, tmp_path):
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_goal(
                file="../../etc/passwd",
                line=0,
                character=0,
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "workspace" in result["error"].lower()

    def test_file_not_found(self, tmp_path):
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_goal(
                file="nonexistent.v",
                line=0,
                character=0,
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert (
            "not found" in result["error"].lower()
            or "no such" in result["error"].lower()
        )

    def test_line_out_of_range(self, tmp_path):
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_goal(
                file="test.v",
                line=-1,
                character=0,
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "range" in result["error"].lower()

    def test_character_out_of_range(self, tmp_path):
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_goal(
                file="test.v",
                line=0,
                character=200000,
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "range" in result["error"].lower()


# ---------------------------------------------------------------------------
# TestGoalMocked
# ---------------------------------------------------------------------------


class TestGoalMocked:
    """Mock pet tests for goal retrieval logic.

    Override module-level skip — this class uses mocks, not real pet.
    """

    pytestmark = []

    @pytest.fixture(autouse=True)
    def _reset_semaphore(self):
        import rocq_mcp.server as srv

        srv._pet_semaphore = None
        yield
        srv._pet_semaphore = None

    @pytest.fixture(autouse=True)
    def _mock_pytanque(self):
        """Ensure pytanque is importable even if not installed."""
        if "pytanque" in sys.modules:
            yield
            return

        mock_module = SimpleNamespace(
            PetanqueError=type("PetanqueError", (Exception,), {"message": ""}),
            Pytanque=MagicMock,
            PytanqueMode=SimpleNamespace(STDIO="stdio"),
        )
        sys.modules["pytanque"] = mock_module
        yield
        sys.modules.pop("pytanque", None)

    @pytest.mark.asyncio
    async def test_basic_goal_retrieval(self):
        """run_goal returns goals from pet.get_state_at_pos + complete_goals."""
        import rocq_mcp.server

        mock_state = SimpleNamespace(proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.get_state_at_pos.return_value = mock_state

        mock_goal = SimpleNamespace(
            ty="nat -> nat",
            hyps=[SimpleNamespace(names=["n"], ty="nat", def_=None)],
        )
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[mock_goal], stack=[], shelf=[], given_up=[]
        )

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : nat -> nat. Proof. intro n.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await run_goal(
                    file="test.v",
                    line=0,
                    character=35,
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )

        assert result["success"] is True
        assert result["goals"]  # non-empty
        assert result["file"] == "test.v"
        assert result["line"] == 0
        assert result["character"] == 35
        assert result["proof_finished"] is False

    @pytest.mark.asyncio
    async def test_no_goals_at_position(self):
        """run_goal returns empty goals when no proof state at position."""
        import rocq_mcp.server

        mock_state = SimpleNamespace(proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.get_state_at_pos.return_value = mock_state
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Definition x := 1.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await run_goal(
                    file="test.v",
                    line=0,
                    character=0,
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )

        assert result["success"] is True
        assert result["goals"] == ""

    @pytest.mark.asyncio
    async def test_proof_finished_flag(self):
        """run_goal returns proof_finished=True when proof is complete."""
        import rocq_mcp.server

        mock_state = SimpleNamespace(proof_finished=True, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.get_state_at_pos.return_value = mock_state
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True. Proof. exact I. Qed.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await run_goal(
                    file="test.v",
                    line=0,
                    character=38,
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )

        assert result["success"] is True
        assert result["proof_finished"] is True

    @pytest.mark.asyncio
    async def test_force_reindex(self):
        """run_goal resets current_workspace to force re-indexing."""
        import rocq_mcp.server

        mock_state = SimpleNamespace(proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.get_state_at_pos.return_value = mock_state
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        with tempfile.TemporaryDirectory() as ws:
            lifespan_state = {
                "pet_client": mock_pet,
                "pet_timeout": 30.0,
                "current_workspace": str(Path(ws).resolve()),
            }

            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Definition x := 1.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                await run_goal(
                    file="test.v",
                    line=0,
                    character=0,
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )

        # set_workspace should have been called despite current_workspace matching
        mock_pet.set_workspace.assert_called_once()


# ---------------------------------------------------------------------------
# TestGoalIntegration
# ---------------------------------------------------------------------------


@_pet_only
class TestGoalIntegration:
    """Integration tests using real pet subprocess."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = {
            "pet_client": None,
            "pet_timeout": 30.0,
        }
        yield state
        _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_goal_inside_proof(self, workspace, lifespan_state):
        """Goal retrieval inside a proof returns non-empty goals."""
        test_file = workspace / "test_goal_inside.v"
        test_file.write_text(
            "Theorem foo : forall n : nat, n = n.\n" "Proof.\n" "  intros n.\n"
        )

        result = await run_goal(
            file="test_goal_inside.v",
            line=2,
            character=0,
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )

        assert result["success"] is True
        assert result["goals"]  # should have a goal

    @pytest.mark.asyncio
    async def test_goal_at_top_of_file(self, workspace, lifespan_state):
        """Goal at top of file (outside proof) returns empty goals."""
        test_file = workspace / "test_goal_top.v"
        test_file.write_text("Definition x := 1.\n")

        result = await run_goal(
            file="test_goal_top.v",
            line=0,
            character=0,
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )

        assert result["success"] is True
        # Outside a proof, goals should be empty
        assert result["goals"] == ""

    @pytest.mark.asyncio
    async def test_goal_after_qed(self, workspace, lifespan_state):
        """Goal after Qed returns empty goals."""
        test_file = workspace / "test_goal_qed.v"
        test_file.write_text(
            "Theorem foo : True.\nProof. exact I. Qed.\n" "Definition bar := 1.\n"
        )

        result = await run_goal(
            file="test_goal_qed.v",
            line=2,
            character=0,
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )

        assert result["success"] is True
        assert result["goals"] == ""


# ---------------------------------------------------------------------------
# TestRocqGoalWrapper
# ---------------------------------------------------------------------------


class TestRocqGoalWrapper:
    """Test the MCP wrapper for rocq_goal."""

    @pytest.mark.asyncio
    async def test_ctx_none_error(self):
        """rocq_goal with ctx=None returns error."""
        from rocq_mcp.server import rocq_goal

        result = await rocq_goal(
            file="test.v",
            line=0,
            character=0,
            workspace="/tmp",
            ctx=None,
        )
        assert result["success"] is False
        assert (
            "context" in result["error"].lower()
            or "internal" in result["error"].lower()
        )

    @pytest.mark.asyncio
    async def test_invalid_workspace(self):
        """rocq_goal with empty workspace and no env var returns error."""
        from rocq_mcp.server import rocq_goal

        # Temporarily unset ROCQ_WORKSPACE
        import os

        old = os.environ.get("ROCQ_WORKSPACE", "")
        os.environ["ROCQ_WORKSPACE"] = ""
        try:
            result = await rocq_goal(
                file="test.v",
                line=0,
                character=0,
                workspace="",
                ctx=None,
            )
            assert result["success"] is False
        finally:
            if old:
                os.environ["ROCQ_WORKSPACE"] = old
            else:
                os.environ.pop("ROCQ_WORKSPACE", None)

    @pytest.mark.asyncio
    async def test_parameter_forwarding(self, tmp_path):
        """rocq_goal forwards parameters to run_goal correctly."""
        from unittest.mock import AsyncMock

        import rocq_mcp.server as srv

        ws = str(tmp_path)
        mock_ctx = MagicMock()
        mock_ctx.lifespan_context = {"pet_client": None, "pet_timeout": 10}

        expected = {
            "success": True,
            "goals": "",
            "proof_finished": False,
            "file": "test.v",
            "line": 5,
            "character": 3,
        }

        with patch.object(
            srv, "run_goal", new_callable=AsyncMock, return_value=expected
        ) as mock_run:
            result = await srv.rocq_goal(
                file="test.v",
                line=5,
                character=3,
                workspace=ws,
                ctx=mock_ctx,
            )

        mock_run.assert_called_once_with(
            file="test.v",
            line=5,
            character=3,
            workspace=ws,
            lifespan_state=mock_ctx.lifespan_context,
        )
        assert result == expected
