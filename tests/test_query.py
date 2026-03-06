"""Tests for the rocq_query tool (Phase 1, requires pet binary).

These tests require the ``pet`` binary (from coq-lsp) to be available on PATH.
Phase 1 tests are placeholders until a real FastMCP test client is used.
"""

from __future__ import annotations

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(
    not PET_AVAILABLE, reason="pet not available"
)


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------

class TestQuerySuccess:
    """Queries that should return valid output."""

    @pytest.mark.asyncio
    async def test_search_nat(self, workspace):
        """Search for nat-related lemmas should return results."""
        # Phase 1 placeholder: requires FastMCP test client to inject Context
        # In practice: result = await rocq_query(command="Search nat.", ...)
        # assert result["success"] is True
        # assert "nat" in result["output"].lower()
        pass

    @pytest.mark.asyncio
    async def test_check_type(self, workspace):
        """Check Nat.add should return its type signature."""
        # result = await rocq_query(command="Check Nat.add.", ...)
        # assert result["success"] is True
        # assert "nat" in result["output"].lower()
        pass

    @pytest.mark.asyncio
    async def test_with_preamble(self, workspace):
        """Query with Require Import in preamble for context."""
        # result = await rocq_query(
        #     command="Check Rplus.",
        #     preamble="Require Import Reals.\nOpen Scope R_scope.",
        #     ...
        # )
        # assert result["success"] is True
        pass


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

class TestQueryEdgeCases:
    """Edge cases for query input handling."""

    @pytest.mark.asyncio
    async def test_auto_append_dot(self):
        """Command without trailing dot should get one appended automatically."""
        # The server code does: if not cmd.endswith("."): cmd += "."
        # result = await rocq_query(command="Search nat", ...)
        # assert result["success"] is True
        pass

    @pytest.mark.asyncio
    async def test_no_double_dot(self):
        """Command already ending with dot should not get another one."""
        # result = await rocq_query(command="Search nat.", ...)
        # assert result["success"] is True
        pass

    @pytest.mark.asyncio
    async def test_output_truncation(self):
        """Very large Search result should be truncated to MAX_OUTPUT chars."""
        # result = await rocq_query(command="Search _.", ...)
        # if len(result.get("output", "")) > 8000:
        #     assert "truncated" in result["output"]
        pass

    @pytest.mark.asyncio
    async def test_empty_feedback(self):
        """Query with no output returns '(no output)' sentinel."""
        # Some queries may produce no feedback lines.
        # result = await rocq_query(command="idtac.", ...)
        # In Phase 1 this may not be reachable; placeholder for now.
        pass


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------

class TestQueryErrors:
    """Queries that should fail gracefully."""

    @pytest.mark.asyncio
    async def test_timeout(self):
        """A query that exceeds the timeout should return a timeout error."""
        # result = await rocq_query(command="<long running>", ...)
        # assert result["success"] is False
        # assert "timed out" in result["error"].lower()
        pass

    @pytest.mark.asyncio
    async def test_pet_not_on_path(self):
        """When pet binary is missing, return a clear error."""
        # This would need monkeypatching to hide pet from PATH.
        # result = await rocq_query(command="Search nat.", ...)
        # assert result["success"] is False
        # assert "not found" in result["error"].lower()
        pass

    @pytest.mark.asyncio
    async def test_invalid_command(self):
        """An invalid Rocq command should return a PetanqueError."""
        # result = await rocq_query(command="InvalidCommand.", ...)
        # assert result["success"] is False
        pass
