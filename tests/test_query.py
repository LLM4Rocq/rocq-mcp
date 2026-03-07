"""Tests for rocq_query via the run_query function.

These tests call run_query directly with a lifespan_state dict,
bypassing FastMCP Context injection.
"""

from __future__ import annotations

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
    }


@pytest.fixture
def lifespan_state():
    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    yield state
    _invalidate_pet(state)


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------


class TestQuerySuccess:
    """Queries that should return valid output."""

    @pytest.mark.asyncio
    async def test_search_nat(self, workspace, lifespan_state):
        from rocq_mcp.server import run_query

        result = await run_query(
            command="Search nat.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert "nat" in result["output"].lower()

    @pytest.mark.asyncio
    async def test_check_type(self, workspace, lifespan_state):
        from rocq_mcp.server import run_query

        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert "nat" in result["output"].lower()

    @pytest.mark.asyncio
    async def test_with_preamble(self, workspace, lifespan_state):
        """Query with preamble for imports."""
        from rocq_mcp.server import run_query

        result = await run_query(
            command="Check Rplus.",
            preamble="From Coq Require Import Reals.\nOpen Scope R_scope.",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert "R" in result["output"]


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------


class TestQueryEdgeCases:
    """Edge cases for query input handling."""

    @pytest.mark.asyncio
    async def test_auto_append_dot(self, workspace, lifespan_state):
        """Command without trailing dot should get one appended automatically."""
        from rocq_mcp.server import run_query

        result = await run_query(
            command="Check Nat.add",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True

    @pytest.mark.asyncio
    async def test_no_double_dot(self, workspace, lifespan_state):
        """Command already ending with dot should not get another one."""
        from rocq_mcp.server import run_query

        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------


class TestQueryErrors:
    """Queries that should fail gracefully."""

    @pytest.mark.asyncio
    async def test_timeout(self, workspace):
        """A query that exceeds the timeout should return a timeout error."""
        from rocq_mcp.server import run_query

        # Use an extremely short timeout to trigger it
        state = _make_lifespan_state(pet_timeout=0.001)
        result = await run_query(
            command="Search _.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=state,
        )
        assert result["success"] is False
        assert "timed out" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_invalid_command(self, workspace, lifespan_state):
        """An invalid Rocq command should return an error."""
        from rocq_mcp.server import run_query

        result = await run_query(
            command="InvalidXYZCommand.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False
        assert "not found" in result["error"].lower()
