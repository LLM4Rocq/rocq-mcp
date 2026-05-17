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


from tests.conftest import make_lifespan_state as _make_lifespan_state  # noqa: E402


@pytest.fixture
def lifespan_state():
    """Provide a lifespan_state and clean up pet on teardown."""
    from collections import deque

    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    # Add the recent_errors buffer that production app_lifespan
    # sets up — tests of recording behaviour depend on it.
    state["recent_errors"] = deque(maxlen=10)
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
    @pytest.mark.parametrize(
        "bad_tactic",
        [
            # Undefined tactic identifier (Ltac lookup failure).
            "omega_bad_tactic.",
            # Type mismatch — `apply` against an irrelevant lemma.
            "apply Nat.add_comm.",
            # Unsolved subgoal at Qed (try to finish without proof).
            "exact 0.",
        ],
    )
    async def test_batch_error_mid_proof(self, workspace, lifespan_state, bad_tactic):
        """Mid-batch failures across structurally distinct error modes
        all hit the same code path and must produce identical envelope
        shape (reason="tactic_failed", failed_command, command_index,
        last_valid_state_id, recent_errors round-trip)."""
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

        # First tactic (intros) succeeds; second varies by parameter.
        cr = await run_check(
            body=f"intros. {bad_tactic}",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr["success"] is False
        # Mid-batch tactic rejection must tag reason="tactic_failed" so the
        # agent can distinguish it from a transport-level "crashed" or
        # "timeout".
        assert cr["reason"] == "tactic_failed"
        assert "error" in cr
        assert "failed_command" in cr
        assert cr["command_index"] == 1
        assert cr["commands_run"] == 1
        assert "last_valid_state_id" in cr
        assert cr["last_valid_state_id"] is not None
        # The same reason must reach recent_errors so rocq_diag surfaces
        # the failure with consistent attribution.
        recorded = [
            e
            for e in lifespan_state["recent_errors"]
            if e.get("tool") == "rocq_check" and e.get("reason") == "tactic_failed"
        ]
        assert len(recorded) == 1


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
        assert cr_a["from_state_id"] == start_id
        assert cr_b["from_state_id"] == start_id


# ---------------------------------------------------------------------------
# TestCheckEdgeCases
# ---------------------------------------------------------------------------


class TestCheckEdgeCases:
    """Edge cases for run_check."""

    @pytest.mark.asyncio
    async def test_unknown_state_id(self, workspace, lifespan_state):
        """Call run_check with a state ID that has never existed; expect a
        clear 'does not exist' error.  Replaces the previous 'no active
        state' test from when ``from_state`` was optional."""
        from rocq_mcp.interactive import run_check

        cr = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=999999,
        )
        assert cr["success"] is False
        assert "error" in cr
        assert "does not exist" in cr["error"].lower()

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
    async def test_proof_tactics_status_omitted_on_complete_chain(
        self, workspace, lifespan_state
    ):
        """On a complete walk, proof_tactics is present and no status keys appear.

        The status / broken_at / hint envelope is reserved for the
        broken-walk paths; the happy path carries only proof_tactics and
        proof_hint, with no status field at all.
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
        assert "proof_hint" in cr
        # None of the broken-walk envelope keys should appear, including
        # the now-removed legacy proof_tactics_complete.
        assert "proof_tactics_status" not in cr
        assert "proof_tactics_broken_at" not in cr
        assert "proof_tactics_hint" not in cr
        assert "proof_tactics_complete" not in cr

    @pytest.mark.asyncio
    async def test_proof_tactics_status_ancestor_evicted(
        self, workspace, lifespan_state
    ):
        """When an ancestor is evicted before the leaf finishes the proof,
        the result drops proof_tactics and reports ancestor_evicted at the
        first missing id.
        """
        from rocq_mcp.interactive import run_start, run_check, _state_remove

        vfile = workspace / "check_pt_evicted.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\nProof. intros. reflexivity. Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True
        root_id = sr["state_id"]

        cr_mid = await run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root_id,
        )
        assert cr_mid["success"] is True
        mid_id = cr_mid["state_id"]

        # Evict the *root* state. The leaf state (created next) and the
        # mid state both stay alive, so resolution succeeds and the
        # proof_finished branch runs — but the parent walk dies at root.
        _state_remove(root_id)

        cr = await run_check(
            body="reflexivity.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=mid_id,
        )
        assert cr["success"] is True
        assert cr["proof_finished"] is True
        assert "proof_tactics" not in cr
        assert cr["proof_tactics_status"] == "ancestor_evicted"
        assert cr["proof_tactics_broken_at"] == root_id
        assert "proof_tactics_hint" in cr
        assert "proof_hint" not in cr


# ---------------------------------------------------------------------------
# TestCheckBulletFocusPayload
# ---------------------------------------------------------------------------


class TestCheckBulletFocusPayload:
    """Bullet / focus-management commands return enriched payload.

    A body consisting of exactly
    ``{``, ``}``, or a ``-``/``+``/``*`` run should add ``focus_command``,
    ``goals_before``, ``goals_after``, ``focus_depth_before``,
    ``focus_depth_after`` to the response so the agent can see the
    focus transition.
    """

    @pytest.mark.asyncio
    async def test_open_brace_focuses_first_subgoal(self, workspace, lifespan_state):
        """``{`` after a ``destruct`` should push a focus frame and
        narrow the focused goals from 2 to 1."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_bullet_focus.v"
        vfile.write_text(
            "Theorem t : forall b : bool, b = b.\n"
            "Proof. intros b. destruct b. { reflexivity. } { reflexivity. } Qed.\n"
        )

        sr = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert sr["success"] is True

        # Advance to a 2-subgoal state.
        cr1 = await run_check(
            body="intros b. destruct b.",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=sr["state_id"],
        )
        assert cr1["success"] is True
        assert cr1["proof_finished"] is False

        # Now execute the bullet/focus command ``{`` on its own.
        cr2 = await run_check(
            body="{",
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=cr1["state_id"],
        )
        assert cr2["success"] is True
        # focus payload — additive keys.
        assert cr2["focus_command"] == "{"
        assert cr2["goals_before"] == 2
        assert cr2["goals_after"] == 1
        # Opening a brace pushes a frame onto the focus stack.
        assert cr2["focus_depth_after"] == cr2["focus_depth_before"] + 1

    @pytest.mark.asyncio
    async def test_non_bullet_body_unaffected(self, workspace, lifespan_state):
        """Plain tactics must NOT gain the focus-payload keys."""
        from rocq_mcp.interactive import run_start, run_check

        vfile = workspace / "check_no_bullet.v"
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
        for k in (
            "focus_command",
            "goals_before",
            "goals_after",
            "focus_depth_before",
            "focus_depth_after",
        ):
            assert k not in cr


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

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

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


# ---------------------------------------------------------------------------
# TestCheckClamp: mock-based clamp test (no pet required)
# ---------------------------------------------------------------------------


class TestCheckClamp:
    """Mock-based test for the rocq_check wrapper's timeout-clamping path."""

    # Override module-level skip — this class uses mocks, not real pet.
    pytestmark = []

    @pytest.mark.asyncio
    async def test_rocq_check_clamps_timeout(self, monkeypatch):
        """Wrapper clamps an over-cap timeout and echoes ``clamped_timeout``."""
        from rocq_mcp.server import rocq_check
        from tests.conftest import _MockContext
        import rocq_mcp.server as _server

        captured: dict = {}

        async def mock_run_check(**kwargs):
            captured.update(kwargs)
            return {"success": True, "state_id": 1, "goals": ""}

        monkeypatch.setattr(_server, "run_check", mock_run_check)

        mock_ctx = _MockContext({"pet_client": None})

        result = await rocq_check(
            body="intros.",
            from_state=1,
            timeout=5000,
            ctx=mock_ctx,
        )

        assert result["clamped_timeout"] == _server.ROCQ_QUERY_TIMEOUT_CAP
        assert captured["timeout"] == float(_server.ROCQ_QUERY_TIMEOUT_CAP)
