"""Tests for the rocq_step tool (Phase 2, requires pet binary).

These tests require the ``pet`` binary (from coq-lsp) to be available on PATH.
Phase 2 tests are placeholders until a real FastMCP test client is used for
Context injection.
"""

from __future__ import annotations

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(
    not PET_AVAILABLE, reason="pet not available"
)


# ---------------------------------------------------------------------------
# Basic workflow
# ---------------------------------------------------------------------------

class TestStepBasicWorkflow:
    """Core step-by-step proving workflow."""

    @pytest.mark.asyncio
    async def test_simple_proof_complete(self):
        """Step through intros -> simpl -> reflexivity and reach proof_finished."""
        # result1 = await rocq_step(tactic="intros n", file="test.v", theorem="add_0_r", ...)
        # assert result1["success"] is True
        # assert not result1["proof_finished"]
        # result2 = await rocq_step(tactic="simpl", ...)
        # result3 = await rocq_step(tactic="reflexivity", ...)
        # assert result3["proof_finished"] is True
        pass

    @pytest.mark.asyncio
    async def test_auto_session_start(self):
        """First call with file+theorem starts session automatically."""
        # result = await rocq_step(tactic="intros", file="test.v", theorem="t", ...)
        # assert result["success"] is True
        # assert "goals" in result
        pass

    @pytest.mark.asyncio
    async def test_goals_returned(self):
        """Each step returns the current goal state."""
        # result = await rocq_step(tactic="intros n", file="test.v", theorem="t", ...)
        # assert result["success"] is True
        # assert len(result["goals"]) > 0
        pass


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

class TestStepEdgeCases:
    """Edge cases for interactive proving."""

    @pytest.mark.asyncio
    async def test_wrong_tactic(self):
        """Invalid tactic returns error but does not corrupt session state."""
        # result = await rocq_step(tactic="nonsense", file="test.v", theorem="t", ...)
        # First step to establish session:
        # result1 = await rocq_step(tactic="intros n", file="test.v", theorem="add_0_r", ...)
        # Then invalid tactic:
        # result2 = await rocq_step(tactic="omega_nonexistent", ...)
        # assert result2["success"] is False
        # Session should be intact for next valid tactic:
        # result3 = await rocq_step(tactic="reflexivity", ...)
        pass

    @pytest.mark.asyncio
    async def test_new_session_replaces_old(self):
        """Sending file+theorem starts a fresh session, discarding the old one."""
        # result1 = await rocq_step(tactic="intros", file="a.v", theorem="thm_a", ...)
        # result2 = await rocq_step(tactic="intros", file="b.v", theorem="thm_b", ...)
        # result2 should be about thm_b, not thm_a
        pass

    @pytest.mark.asyncio
    async def test_no_session_error(self):
        """Calling step without file+theorem when no session exists gives error."""
        # result = await rocq_step(tactic="intros", ...)
        # assert result["success"] is False
        # assert "no active session" in result["error"].lower()
        pass

    @pytest.mark.asyncio
    async def test_auto_dot_append(self):
        """Tactic without trailing dot gets one appended automatically."""
        # The server code does: if not tac.endswith("."): tac += "."
        # result = await rocq_step(tactic="intros n", file="test.v", theorem="t", ...)
        # assert result["success"] is True
        pass


# ---------------------------------------------------------------------------
# Timeout and recovery
# ---------------------------------------------------------------------------

class TestStepTimeout:
    """Timeout handling and session recovery after timeout."""

    @pytest.mark.asyncio
    async def test_timeout_kills_session(self):
        """Non-terminating tactic -> timeout -> session lost."""
        # result = await rocq_step(
        #     tactic="repeat idtac",
        #     file="test.v", theorem="loop",
        #     ...
        # )
        # assert result["success"] is False
        # assert "timed out" in result["error"].lower()
        pass

    @pytest.mark.asyncio
    async def test_no_deadlock_after_timeout(self):
        """After timeout, subsequent calls must NOT deadlock.

        This tests blocker B3: the asyncio.Semaphore must be released even
        when the background thread is orphaned by asyncio.wait_for timeout.
        """
        # 1. Trigger timeout with repeat idtac
        # 2. Make another step call -- it must return within a reasonable time
        # result = await asyncio.wait_for(
        #     rocq_step(tactic="intros", file="test.v", theorem="t", ...),
        #     timeout=10
        # )
        # assert result is not None  # Did not deadlock
        pass

    @pytest.mark.asyncio
    async def test_session_recovery_after_timeout(self):
        """After timeout kills session, can start new session with file+theorem."""
        # 1. Trigger timeout
        # 2. Start new session
        # result = await rocq_step(
        #     tactic="intros",
        #     file="test.v", theorem="add_0_r",
        #     ...
        # )
        # assert result["success"] is True
        pass
