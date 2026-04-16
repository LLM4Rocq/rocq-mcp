"""Tests for run_check() -- sequential tactic execution from a state.

run_check() executes commands sequentially from a state established by
a prior run_start() call.  It replaces the old run_step() for single-
tactic execution and run_fast_check() for batch execution.

Tests are grouped into:
- TestCheckSingleTactic: one tactic at a time
- TestCheckBatch: multiple commands in one body
- TestCheckFromState: branching via from_state
- TestCheckEdgeCases: edge cases (no state, empty body, auto-dot, timing)
- TestCheckTimeout: timeout handling
"""

from __future__ import annotations

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    """Create a minimal lifespan_state dict for testing."""
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
        "current_workspace": None,
    }


@pytest.fixture
def lifespan_state():
    """Provide a lifespan_state and clean up pet on teardown."""
    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    yield state
    _invalidate_pet(state)


@pytest.fixture(autouse=True)
def reset_state_table():
    """Reset the state table and current state before/after each test."""
    from rocq_mcp.interactive import _state_invalidate_all

    _state_invalidate_all()
    yield
    _state_invalidate_all()


# ---------------------------------------------------------------------------
# TestCheckSingleTactic
# ---------------------------------------------------------------------------


class TestCheckSingleTactic:
    """Single-tactic execution via run_check."""

    @pytest.mark.asyncio
    async def test_single_tactic(self, workspace, lifespan_state):
        """Start a theorem, run one tactic, verify success and goals."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_single.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True
        start_state_id = sr["state_id"]

        cr = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=start_state_id,
        )
        assert cr["success"] is True
        assert "goals" in cr
        # After intros, we should see the hypothesis n and goal n = n
        assert "n" in cr["goals"]
        assert "state_id" in cr
        assert cr["commands_run"] == 1
        assert cr["proof_finished"] is False

    @pytest.mark.asyncio
    async def test_proof_finished(self, workspace, lifespan_state):
        """Run a tactic that finishes the proof, verify proof_finished=True."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_finished.v"
        vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="exact I.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is True

    @pytest.mark.asyncio
    async def test_wrong_tactic(self, workspace, lifespan_state):
        """Run an invalid tactic, verify error response."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_wrong.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="omega_nonexistent_tactic.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is False
        assert "error" in cr


# ---------------------------------------------------------------------------
# TestCheckBatch
# ---------------------------------------------------------------------------


class TestCheckBatch:
    """Batch (multi-command) execution via run_check."""

    @pytest.mark.asyncio
    async def test_batch_execution(self, workspace, lifespan_state):
        """Run multiple tactics as one body, verify commands_run and proof_finished."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_batch.v"
        vfile.write_text(
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Proof.\n"
            "  intros n. induction n as [| n' IH].\n"
            "  - reflexivity.\n"
            "  - simpl. rewrite IH. reflexivity.\n"
            "Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="add_0_r",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        body = (
            "intros n. induction n as [| n' IH]. "
            "- reflexivity. "
            "- simpl. rewrite IH. reflexivity."
        )
        cr = await run_check(
            body=body,
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is True
        # The body contains multiple sentences; commands_run should match
        assert cr["commands_run"] >= 2

    @pytest.mark.asyncio
    async def test_batch_error_mid_proof(self, workspace, lifespan_state):
        """Run a batch where the 2nd command fails, verify error details."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_batch_err.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        # First tactic (intros) should succeed, second (omega_bad) should fail
        cr = await run_check(
            body="intros. omega_bad_tactic.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is False
        assert "error" in cr
        assert "failed_command" in cr
        assert cr["command_index"] == 1
        assert cr["commands_run"] == 1
        assert "last_valid_state_id" in cr
        assert cr["last_valid_state_id"] is not None


# ---------------------------------------------------------------------------
# TestCheckFromState
# ---------------------------------------------------------------------------


class TestCheckFromState:
    """Branching via from_state parameter."""

    @pytest.mark.asyncio
    async def test_from_state_branching(self, workspace, lifespan_state):
        """Start a theorem, run tactic A, then run tactic B from the same start state."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_branch.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True
        start_id = sr["state_id"]

        # Branch A: run intros from start state
        cr_a = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=start_id,
        )
        assert cr_a["success"] is True
        state_a = cr_a["state_id"]

        # Branch B: run intros n from the SAME start state (not from state_a)
        cr_b = await run_check(
            body="intros n.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=start_id,
        )
        assert cr_b["success"] is True
        state_b = cr_b["state_id"]

        # The two branches should produce different state IDs
        assert state_a != state_b

        # Both should record the start state as their parent
        assert cr_a["parent_state_id"] == start_id
        assert cr_b["parent_state_id"] == start_id


# ---------------------------------------------------------------------------
# TestCheckEdgeCases
# ---------------------------------------------------------------------------


class TestCheckEdgeCases:
    """Edge cases for run_check."""

    @pytest.mark.asyncio
    async def test_no_active_state(self, workspace, lifespan_state):
        """Call run_check with no prior run_start and from_state=None, expect error."""
        from rocq_mcp.interactive import run_check

        cr = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=None,
        )
        assert cr["success"] is False
        assert "error" in cr
        # Should indicate there is no active state
        err_lower = cr["error"].lower()
        assert "no active" in err_lower or "state" in err_lower

    @pytest.mark.asyncio
    async def test_empty_body(self, workspace, lifespan_state):
        """Call run_check with empty body, verify success with commands_run=0."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_empty.v"
        vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["commands_run"] == 0

    @pytest.mark.asyncio
    async def test_auto_dot_append(self, workspace, lifespan_state):
        """Run a tactic without trailing dot, verify it still works."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_autodot.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        # "intros" without trailing dot -- should still succeed
        cr = await run_check(
            body="intros",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True

    @pytest.mark.asyncio
    async def test_check_time_ms(self, workspace, lifespan_state):
        """Verify check_time_ms is present and is a non-negative int on success."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_timing.v"
        vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="exact I.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert "check_time_ms" in cr
        assert isinstance(cr["check_time_ms"], int)
        assert cr["check_time_ms"] >= 0


# ---------------------------------------------------------------------------
# TestCheckTimeout
# ---------------------------------------------------------------------------


class TestCheckTimeout:
    """Timeout handling for run_check."""

    @pytest.mark.asyncio
    async def test_timeout_single_tactic(self, workspace):
        """Use a looping tactic with a short timeout, verify timeout error."""
        from rocq_mcp.interactive import run_start, run_check
        from rocq_mcp.server import _invalidate_pet

        vfile = workspace / "check_timeout.v"
        vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")

        # Use a normal timeout for start (pet compilation takes time),
        # then pass a short timeout explicitly to run_check.
        state = _make_lifespan_state(pet_timeout=30.0)
        try:
            sr = await run_start(
                file=str(vfile.relative_to(workspace)),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert sr["success"] is True

            cr = await run_check(
                body="repeat eapply proj1.",
                timeout=2.0,
                lifespan_state=state,
                from_state=sr["state_id"],
            )
            assert cr["success"] is False
            assert "error" in cr
            # The error should mention timeout
            err_lower = cr["error"].lower()
            assert "timed out" in err_lower or "timeout" in err_lower
        finally:
            _invalidate_pet(state)


# ---------------------------------------------------------------------------
# TestCheckProofTactics
# ---------------------------------------------------------------------------


class TestCheckProofTactics:
    """Verify proof_tactics and proof_hint are returned when proof_finished."""

    @pytest.mark.asyncio
    async def test_single_tactic_proof(self, workspace, lifespan_state):
        """A one-tactic proof returns proof_tactics with that tactic."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_pt_single.v"
        vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="exact I.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is True
        assert "proof_tactics" in cr
        assert cr["proof_tactics"] == ["exact I."]
        assert "proof_hint" in cr
        assert "Proof complete" in cr["proof_hint"]

    @pytest.mark.asyncio
    async def test_multi_step_proof(self, workspace, lifespan_state):
        """A multi-step proof returns all tactics in order."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_pt_multi.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        # Step 1
        cr1 = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr1["success"] is True
        assert cr1["proof_finished"] is False
        assert "proof_tactics" not in cr1

        # Step 2 — finishes the proof
        cr2 = await run_check(
            body="reflexivity.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=cr1["state_id"],
        )
        assert cr2["success"] is True
        assert cr2["proof_finished"] is True
        assert cr2["proof_tactics"] == ["intros.", "reflexivity."]

    @pytest.mark.asyncio
    async def test_batch_proof(self, workspace, lifespan_state):
        """A batch body that finishes the proof returns all tactics."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_pt_batch.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="intros. reflexivity.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is True
        assert cr["proof_tactics"] == ["intros.", "reflexivity."]

    @pytest.mark.asyncio
    async def test_no_proof_tactics_when_not_finished(self, workspace, lifespan_state):
        """proof_tactics and proof_hint are absent when proof is not finished."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_pt_notfinished.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is False
        assert "proof_tactics" not in cr
        assert "proof_hint" not in cr

    @pytest.mark.asyncio
    async def test_branching_returns_committed_path(self, workspace, lifespan_state):
        """After branching, proof_tactics reflects only the committed path."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_pt_branch.v"
        vfile.write_text(
            "From Coq Require Import Arith.\n\n"
            "Theorem t : forall n : nat, n + 0 = n.\n"
            "Proof.\n"
            "  intros n. induction n as [| n' IH].\n"
            "  - reflexivity.\n"
            "  - simpl. rewrite IH. reflexivity.\n"
            "Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True
        root = sr["state_id"]

        # Path A: start with intros
        cr_a = await run_check(
            body="intros n.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root,
        )
        assert cr_a["success"] is True

        # Path B (abandoned): also from root, different tactic
        cr_b = await run_check(
            body="intro.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root,
        )
        assert cr_b["success"] is True

        # Continue path A to completion
        cr_finish = await run_check(
            body="induction n as [| n' IH]. - reflexivity. - simpl. rewrite IH. reflexivity.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=cr_a["state_id"],
        )
        assert cr_finish["success"] is True
        assert cr_finish["proof_finished"] is True
        # Path B's "intro." must NOT appear in the tactics
        tactics = cr_finish["proof_tactics"]
        assert tactics[0] == "intros n."
        assert "intro." not in tactics

    @pytest.mark.asyncio
    async def test_proof_tactics_completeness_flag(self, workspace, lifespan_state):
        """When chain is complete, proof_tactics_complete should NOT be present.

        proof_tactics_complete is only set to False when the chain is broken.
        A complete proof with a full chain from root omits the key entirely.
        """
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_pt_complete_flag.v"
        vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        cr = await run_check(
            body="exact I.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is True
        assert "proof_tactics" in cr
        # proof_tactics_complete should NOT be present when chain is complete
        # (it is only set to False when the chain is broken)
        assert "proof_tactics_complete" not in cr


# ---------------------------------------------------------------------------
# TestCheckMultiCommandTimeout: per-command Rocq timeout (TL-2)
# ---------------------------------------------------------------------------


class TestCheckMultiCommandTimeout:
    """Test per-command Rocq timeout in multi-command run_check.

    This is a mock-based test that does not require pet, so we override
    the module-level pytestmark skip.
    """

    # Override module-level skip — this class uses mocks, not real pet
    pytestmark = []

    @pytest.fixture(autouse=True)
    def _reset_state_and_semaphore(self):
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        srv._pet_semaphore = None
        yield
        _state_invalidate_all()
        srv._pet_semaphore = None

    @pytest.fixture(autouse=True)
    def _mock_pytanque(self):
        """Ensure pytanque is importable even if not installed."""
        import sys
        from types import SimpleNamespace
        from unittest.mock import MagicMock

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
    async def test_multi_command_divides_timeout(self):
        """Multi-command run_check should divide timeout among commands."""
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        # Set up state
        _interactive._state_table.clear()
        _interactive._state_next_id = 1
        _interactive._state_current_id = None

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        sid = _interactive._state_add(
            state=mock_state,
            file="test.v",
            theorem="test",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )

        # Track timeouts passed to pet.run()
        recorded_timeouts = []

        new_state = SimpleNamespace(st=43, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None

        def fake_run(state, cmd, timeout=None):
            recorded_timeouts.append(timeout)
            return new_state

        mock_pet.run = fake_run

        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="intros. simpl. reflexivity.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        # 3 commands with 30s timeout -> each gets max(1, 30/3) = 10s
        assert len(recorded_timeouts) == 3
        for t in recorded_timeouts:
            assert t == 10, f"Expected per-command timeout of 10, got {t}"
