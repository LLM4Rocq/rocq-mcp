"""Tests for rocq_step via the run_step function.

These tests call run_step directly with a lifespan_state dict,
bypassing FastMCP Context injection.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
    }


@pytest.fixture(autouse=True)
def reset_session():
    """Reset the module-level _session dict before each test."""
    from rocq_mcp.server import _session

    _session.update({"state": None, "file": None, "theorem": None, "history": []})
    yield
    _session.update({"state": None, "file": None, "theorem": None, "history": []})


@pytest.fixture
def lifespan_state():
    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    yield state
    _invalidate_pet(state)


@pytest.fixture
def step_file(workspace):
    """Create a .v file with a simple theorem for interactive proving."""
    vfile = workspace / "step_test.v"
    vfile.write_text(
        "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
    )
    return str(vfile)


# ---------------------------------------------------------------------------
# Basic workflow
# ---------------------------------------------------------------------------


class TestStepBasicWorkflow:
    """Core step-by-step proving workflow."""

    @pytest.mark.asyncio
    async def test_simple_proof_complete(self, workspace, lifespan_state, step_file):
        """Step through intros -> reflexivity and reach proof_finished."""
        from rocq_mcp.server import run_step

        r1 = await run_step(
            tactic="intros",
            file=step_file,
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r1["success"] is True
        assert r1["proof_finished"] is False
        assert "n" in r1["goals"]  # should see hypothesis n : nat

        r2 = await run_step(
            tactic="reflexivity",
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r2["success"] is True
        assert r2["proof_finished"] is True

    @pytest.mark.asyncio
    async def test_goals_returned(self, workspace, lifespan_state, step_file):
        """First step returns the current goal state."""
        from rocq_mcp.server import run_step

        r = await run_step(
            tactic="intros n",
            file=step_file,
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r["success"] is True
        assert "n = n" in r["goals"]
        assert r["step"] == 1


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------


class TestStepEdgeCases:
    """Edge cases for interactive proving."""

    @pytest.mark.asyncio
    async def test_wrong_tactic(self, workspace, lifespan_state, step_file):
        """Invalid tactic returns error but does not corrupt session state."""
        from rocq_mcp.server import run_step

        # Start session
        r1 = await run_step(
            tactic="intros n",
            file=step_file,
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r1["success"] is True

        # Invalid tactic
        r2 = await run_step(
            tactic="omega_nonexistent",
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r2["success"] is False

        # Session should still work with valid tactic
        r3 = await run_step(
            tactic="reflexivity",
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r3["success"] is True
        assert r3["proof_finished"] is True

    @pytest.mark.asyncio
    async def test_no_session_error(self, workspace, lifespan_state):
        """Calling step without file+theorem when no session exists gives error."""
        from rocq_mcp.server import run_step

        r = await run_step(
            tactic="intros",
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r["success"] is False
        assert "no active session" in r["error"].lower()

    @pytest.mark.asyncio
    async def test_auto_dot_append(self, workspace, lifespan_state, step_file):
        """Tactic without trailing dot gets one appended automatically."""
        from rocq_mcp.server import run_step

        r = await run_step(
            tactic="intros n",
            file=step_file,
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r["success"] is True

    @pytest.mark.asyncio
    async def test_new_session_replaces_old(self, workspace, lifespan_state):
        """Sending file+theorem starts a fresh session, discarding the old one."""
        from rocq_mcp.server import run_step

        file1 = workspace / "a.v"
        file1.write_text("Theorem thm_a : True. Proof. exact I. Qed.\n")
        file2 = workspace / "b.v"
        file2.write_text("Theorem thm_b : 1 = 1. Proof. reflexivity. Qed.\n")

        r1 = await run_step(
            tactic="exact I",
            file=str(file1),
            theorem="thm_a",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r1["success"] is True

        # Start new session — should reset
        r2 = await run_step(
            tactic="reflexivity",
            file=str(file2),
            theorem="thm_b",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert r2["success"] is True
        assert r2["step"] == 1  # reset to 1, not 2


# ---------------------------------------------------------------------------
# Timeout
# ---------------------------------------------------------------------------


class TestStepTimeout:
    """Timeout handling and session recovery after timeout."""

    @pytest.mark.asyncio
    async def test_timeout_kills_session(self, workspace):
        """A very short timeout triggers a timeout error."""
        from rocq_mcp.server import run_step, _invalidate_pet

        vfile = workspace / "timeout_test.v"
        vfile.write_text(
            "Ltac loop := idtac; loop.\n" "Theorem t : True. Proof. loop. Qed.\n"
        )

        state = _make_lifespan_state(pet_timeout=1.0)
        try:
            r = await run_step(
                tactic="loop",
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r["success"] is False
            assert "timed out" in r["error"].lower()
        finally:
            _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_session_recovery_after_timeout(self, workspace):
        """After timeout, can start a new session."""
        from rocq_mcp.server import run_step, _invalidate_pet

        vfile_bad = workspace / "timeout_test2.v"
        vfile_bad.write_text(
            "Ltac loop := idtac; loop.\n" "Theorem t : True. Proof. loop. Qed.\n"
        )
        vfile_good = workspace / "good.v"
        vfile_good.write_text("Theorem t2 : True. Proof. exact I. Qed.\n")

        state = _make_lifespan_state(pet_timeout=1.0)
        try:
            # Trigger timeout
            r1 = await run_step(
                tactic="loop",
                file=str(vfile_bad),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r1["success"] is False

            # Increase timeout for recovery
            state["pet_timeout"] = 30.0

            # Start new session — should work
            r2 = await run_step(
                tactic="exact I",
                file=str(vfile_good),
                theorem="t2",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r2["success"] is True
            assert r2["proof_finished"] is True
        finally:
            _invalidate_pet(state)
