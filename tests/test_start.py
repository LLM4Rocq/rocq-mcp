"""Tests for run_start() — the new unified session-start function.

run_start() opens a proof context and returns a state_id.  Three modes:
1. By theorem: file + theorem -> pet.start()
2. By position: file + line + character -> pet.get_state_at_pos()
3. From imports: preamble -> _get_or_create_import_state()

These tests replace the session-start portions of test_step.py and
the position-based tests from test_step_at_pos.py.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
        "current_workspace": None,
    }


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture(autouse=True)
def reset_state_table():
    """Reset the state table before and after each test."""
    from rocq_mcp.interactive import _state_invalidate_all

    _state_invalidate_all()
    yield
    _state_invalidate_all()


@pytest.fixture
def lifespan_state():
    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    yield state
    _invalidate_pet(state)


@pytest.fixture
def simple_vfile(workspace):
    """Create a .v file with a simple theorem for starting a proof."""
    vfile = workspace / "start_test.v"
    vfile.write_text(
        "Theorem my_thm : forall n : nat, n = n.\n"
        "Proof.\n"
        "  intros. reflexivity.\n"
        "Qed.\n"
    )
    return str(vfile)


@pytest.fixture
def true_vfile(workspace):
    """Create a .v file with a trivial True theorem (has a goal)."""
    vfile = workspace / "start_true.v"
    vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")
    return str(vfile)


# ---------------------------------------------------------------------------
# TestStartByTheorem
# ---------------------------------------------------------------------------


class TestStartByTheorem:
    """Tests for starting a proof session by theorem name."""

    @pytest.mark.asyncio
    async def test_start_returns_state_id(
        self, workspace, lifespan_state, simple_vfile
    ):
        """Start by theorem returns success=True and an integer state_id."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file=simple_vfile,
            theorem="my_thm",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert isinstance(result["state_id"], int)
        assert result["file"] == simple_vfile
        assert result["theorem"] == "my_thm"

    @pytest.mark.asyncio
    async def test_start_returns_goals(self, workspace, lifespan_state, true_vfile):
        """Start a theorem that has goals -- goals field should be non-empty."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file=true_vfile,
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert result["goals"]  # non-empty string

    @pytest.mark.asyncio
    async def test_start_nonexistent_theorem(
        self, workspace, lifespan_state, simple_vfile
    ):
        """Starting with a nonexistent theorem returns success=False."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file=simple_vfile,
            theorem="no_such_theorem_xyz",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False

    @pytest.mark.asyncio
    async def test_start_nonexistent_file(self, workspace, lifespan_state):
        """Starting with a nonexistent file returns success=False."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file=str(workspace / "does_not_exist.v"),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False


# ---------------------------------------------------------------------------
# TestStartByPosition
# ---------------------------------------------------------------------------


class TestStartByPosition:
    """Tests for starting a proof session by file position."""

    @pytest.mark.asyncio
    async def test_start_by_position(self, workspace, lifespan_state):
        """Start at a position inside a proof, verify success and state_id."""
        from rocq_mcp.server import run_start

        vfile = workspace / "pos_start.v"
        vfile.write_text(
            "Theorem pos_thm : forall n : nat, n = n.\n"
            "Proof.\n"
            "  intros.\n"
            "  reflexivity.\n"
            "Qed.\n"
        )
        # Position (1, 0) is at the start of "Proof." line -- state after
        # the theorem statement should have the initial goal.
        result = await run_start(
            file=str(vfile),
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            line=1,
            character=0,
        )
        assert result["success"] is True
        assert isinstance(result["state_id"], int)

    @pytest.mark.asyncio
    async def test_start_position_bounds(self, workspace, lifespan_state):
        """Out-of-range line/character returns an error."""
        from rocq_mcp.server import run_start

        vfile = workspace / "bounds_start.v"
        vfile.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        result = await run_start(
            file=str(vfile),
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            line=200000,
            character=0,
        )
        assert result["success"] is False


# ---------------------------------------------------------------------------
# TestStartByPreamble
# ---------------------------------------------------------------------------


class TestStartByPreamble:
    """Tests for starting from a preamble (import cache mode)."""

    @pytest.mark.asyncio
    async def test_start_preamble(self, workspace, lifespan_state):
        """Start with a preamble returns success=True, state_id, and empty goals."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="Require Import Lia.",
        )
        assert result["success"] is True
        assert isinstance(result["state_id"], int)
        # Preamble mode has no open proof, so goals should be empty
        assert result["goals"] == ""
        assert result["file"] == "<preamble>"
        assert result["theorem"] == "<preamble>"

    @pytest.mark.asyncio
    async def test_start_empty_preamble(self, workspace, lifespan_state):
        """Start with empty preamble and no file/theorem returns an error."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="",
        )
        assert result["success"] is False


# ---------------------------------------------------------------------------
# TestStartEdgeCases
# ---------------------------------------------------------------------------


class TestStartEdgeCases:
    """Edge cases: path traversal, forbidden preamble commands, etc."""

    @pytest.mark.asyncio
    async def test_path_traversal(self, workspace, lifespan_state):
        """File path escaping workspace returns success=False with path error."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file="../../../etc/passwd",
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False
        # The error should mention path containment / workspace
        error_lower = result["error"].lower()
        assert "path" in error_lower or "workspace" in error_lower

    @pytest.mark.asyncio
    async def test_forbidden_preamble(self, workspace, lifespan_state):
        """Preamble containing a forbidden command (e.g., Drop) is rejected."""
        from rocq_mcp.server import run_start

        result = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="Drop.",
        )
        assert result["success"] is False
        assert "forbidden" in result["error"].lower() or "Drop" in result["error"]
