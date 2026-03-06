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

PLACEHOLDER = pytest.mark.skip(reason="Phase 2 placeholder: requires FastMCP test client for Context injection")


# ---------------------------------------------------------------------------
# Basic workflow
# ---------------------------------------------------------------------------

class TestStepBasicWorkflow:
    """Core step-by-step proving workflow."""

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_simple_proof_complete(self):
        """Step through intros -> simpl -> reflexivity and reach proof_finished."""
        # result1 = await rocq_step(tactic="intros n", file="test.v", theorem="add_0_r", ...)
        # assert result1["success"] is True
        # assert not result1["proof_finished"]
        # result3 = await rocq_step(tactic="reflexivity", ...)
        # assert result3["proof_finished"] is True

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_auto_session_start(self):
        """First call with file+theorem starts session automatically."""
        # result = await rocq_step(tactic="intros", file="test.v", theorem="t", ...)
        # assert result["success"] is True

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_goals_returned(self):
        """Each step returns the current goal state."""
        # result = await rocq_step(tactic="intros n", file="test.v", theorem="t", ...)
        # assert result["success"] is True
        # assert len(result["goals"]) > 0


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

class TestStepEdgeCases:
    """Edge cases for interactive proving."""

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_wrong_tactic(self):
        """Invalid tactic returns error but does not corrupt session state."""
        # result2 = await rocq_step(tactic="omega_nonexistent", ...)
        # assert result2["success"] is False

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_new_session_replaces_old(self):
        """Sending file+theorem starts a fresh session, discarding the old one."""

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_no_session_error(self):
        """Calling step without file+theorem when no session exists gives error."""
        # result = await rocq_step(tactic="intros", ...)
        # assert result["success"] is False
        # assert "no active session" in result["error"].lower()

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_auto_dot_append(self):
        """Tactic without trailing dot gets one appended automatically."""
        # result = await rocq_step(tactic="intros n", file="test.v", theorem="t", ...)
        # assert result["success"] is True


# ---------------------------------------------------------------------------
# Timeout and recovery
# ---------------------------------------------------------------------------

class TestStepTimeout:
    """Timeout handling and session recovery after timeout."""

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_timeout_kills_session(self):
        """Non-terminating tactic -> timeout -> session lost."""
        # assert result["success"] is False
        # assert "timed out" in result["error"].lower()

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_no_deadlock_after_timeout(self):
        """After timeout, subsequent calls must NOT deadlock.

        This tests blocker B3: the asyncio.Semaphore must be released even
        when the background thread is orphaned by asyncio.wait_for timeout.
        """

    @PLACEHOLDER
    @pytest.mark.asyncio
    async def test_session_recovery_after_timeout(self):
        """After timeout kills session, can start new session with file+theorem."""
        # result = await rocq_step(
        #     tactic="intros",
        #     file="test.v", theorem="add_0_r",
        #     ...
        # )
        # assert result["success"] is True
