"""Tests for the rocq_step_multi tool.

rocq_step_multi tries N tactics against the current proof state and returns
all results WITHOUT advancing the session. Since it requires pytanque, most
tests use mocks.

Tests are grouped into:
- TestStepMultiForbidden: tactic with forbidden command rejected (calls _check_forbidden_commands)
- TestStepMultiReal: tests that call the real run_step_multi with mocked pet
- TestStepMultiIntegration: integration tests (require pet)
"""

from __future__ import annotations

import asyncio
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from tests.conftest import PET_AVAILABLE

# ---------------------------------------------------------------------------
# Helpers to build mock states and goals
# ---------------------------------------------------------------------------


def _make_mock_state(proof_finished=False):
    """Create a mock pytanque state."""
    return SimpleNamespace(
        st=42,
        proof_finished=proof_finished,
        feedback=[],
    )


def _make_mock_hyp(names, ty, def_=None):
    """Create a mock hypothesis object for _format_goals."""
    return SimpleNamespace(names=names, ty=ty, def_=def_)


def _make_structured_goal(hyps, ty):
    """Create a goal with hyps and ty attributes for _format_goals."""
    return SimpleNamespace(hyps=hyps, ty=ty, pp="")


def _make_complete_goals(goals=None, shelf=None, given_up=None):
    """Create a mock GoalsResponse from complete_goals()."""
    return SimpleNamespace(
        goals=goals or [],
        stack=[],
        shelf=shelf or [],
        given_up=given_up or [],
    )


def _ensure_pytanque_importable():
    """Ensure 'pytanque' is importable (mock it if not installed).

    Returns a cleanup function to remove the mock from sys.modules.
    """
    if "pytanque" in sys.modules:
        return lambda: None  # already available, no cleanup needed

    mock_module = SimpleNamespace(
        PetanqueError=type("PetanqueError", (Exception,), {"message": ""}),
        Pytanque=MagicMock,
        PytanqueMode=SimpleNamespace(STDIO="stdio"),
    )
    sys.modules["pytanque"] = mock_module
    return lambda: sys.modules.pop("pytanque", None)


# ---------------------------------------------------------------------------
# TestStepMultiForbidden: tactic with forbidden command -> rejected
# ---------------------------------------------------------------------------


class TestStepMultiForbidden:
    """Tactics containing forbidden commands should be rejected."""

    def test_forbidden_redirect(self):
        """Tactic with Redirect should be rejected."""
        from rocq_mcp.verify import _check_forbidden_commands

        result = _check_forbidden_commands('Redirect "/tmp/evil" Print nat.')
        assert result is not None
        assert "Redirect" in result

    def test_forbidden_drop(self):
        """Tactic with Drop should be rejected."""
        from rocq_mcp.verify import _check_forbidden_commands

        result = _check_forbidden_commands("Drop.")
        assert result is not None
        assert "Drop" in result

    def test_forbidden_load(self):
        """Tactic with Load should be rejected."""
        from rocq_mcp.verify import _check_forbidden_commands

        result = _check_forbidden_commands('Load "evil".')
        assert result is not None
        assert "Load" in result

    def test_normal_tactic_ok(self):
        """Normal tactics should pass forbidden check."""
        from rocq_mcp.verify import _check_forbidden_commands

        assert _check_forbidden_commands("auto.") is None
        assert _check_forbidden_commands("lia.") is None
        assert _check_forbidden_commands("intros n.") is None
        assert _check_forbidden_commands("apply Nat.add_comm.") is None

    def test_forbidden_in_any_tactic(self):
        """If ANY tactic in the list is forbidden, it should be caught."""
        from rocq_mcp.verify import _check_forbidden_commands

        tactics = ["auto.", 'Load "evil".', "lia."]
        forbidden_found = False
        for tactic in tactics:
            if _check_forbidden_commands(tactic) is not None:
                forbidden_found = True
                break
        assert forbidden_found


# ---------------------------------------------------------------------------
# TestStepMultiReal: tests that call the real run_step_multi
# ---------------------------------------------------------------------------


class TestStepMultiReal:
    """Tests that call the actual run_step_multi function (with mocked pet)."""

    @pytest.fixture(autouse=True)
    def _reset_session_and_semaphore(self):
        import rocq_mcp.server as srv

        srv._session.update(
            {"state": None, "file": None, "theorem": None, "history": []}
        )
        srv._pet_semaphore = None  # reset so each asyncio.run() gets a fresh one
        yield
        srv._session.update(
            {"state": None, "file": None, "theorem": None, "history": []}
        )
        srv._pet_semaphore = None

    @pytest.fixture(autouse=True)
    def _mock_pytanque(self):
        """Ensure pytanque is importable even if not installed."""
        cleanup = _ensure_pytanque_importable()
        yield
        cleanup()

    def test_too_many_tactics_rejected(self):
        """run_step_multi rejects >20 tactics with success:False."""
        from rocq_mcp.server import run_step_multi

        lifespan_state = {"pet_client": None, "pet_timeout": 30.0}
        result = asyncio.run(
            run_step_multi(tactics=["auto"] * 25, lifespan_state=lifespan_state)
        )
        assert result["success"] is False
        assert "25" in result["error"]
        assert "20" in result["error"]

    def test_forbidden_command_rejected(self):
        """run_step_multi rejects tactics with forbidden commands."""
        from rocq_mcp.server import run_step_multi

        lifespan_state = {"pet_client": None, "pet_timeout": 30.0}
        result = asyncio.run(
            run_step_multi(
                tactics=["auto.", 'Load "evil".', "lia."],
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "Forbidden" in result["error"] or "Load" in result["error"]

    def test_valid_tactics_with_mocked_pet(self):
        """run_step_multi with valid tactics returns structured results."""
        from rocq_mcp.server import run_step_multi, _session

        # Set up a mock session state (simulating an active session)
        parent_state = _make_mock_state(proof_finished=False)
        _session["state"] = parent_state

        # Build a mock pet that returns structured goals
        mock_pet = MagicMock()
        new_state = _make_mock_state(proof_finished=True)
        mock_pet.run = MagicMock(return_value=new_state)
        mock_pet.complete_goals = MagicMock(
            return_value=_make_complete_goals(
                goals=[
                    _make_structured_goal(
                        hyps=[_make_mock_hyp(["n"], "nat")],
                        ty="n = n",
                    )
                ],
            )
        )

        lifespan_state = {"pet_client": None, "pet_timeout": 30.0}

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = asyncio.run(
                run_step_multi(
                    tactics=["auto", "lia", "ring"],
                    lifespan_state=lifespan_state,
                )
            )

        assert result["success"] is True
        assert "results" in result
        assert len(result["results"]) == 3

        # Each result should have the expected structure
        for entry in result["results"]:
            assert "tactic" in entry
            assert "success" in entry
            assert entry["success"] is True
            assert "goals" in entry
            assert "proof_finished" in entry

        # Session state should NOT have been advanced
        assert _session["state"] is parent_state

    def test_no_session_error(self):
        """run_step_multi with no active session returns error."""
        from rocq_mcp.server import run_step_multi

        lifespan_state = {"pet_client": None, "pet_timeout": 30.0}

        mock_pet = MagicMock()
        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = asyncio.run(
                run_step_multi(tactics=["auto"], lifespan_state=lifespan_state)
            )

        assert result["success"] is False
        assert "no active session" in result["error"].lower()


# ---------------------------------------------------------------------------
# TestStepMultiIntegration: integration tests (require pet)
# ---------------------------------------------------------------------------


@pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")
class TestStepMultiIntegration:
    """Integration tests for rocq_step_multi (require pet subprocess)."""

    @pytest.fixture(autouse=True)
    def _reset_session(self):
        from rocq_mcp.server import _session

        _session.update({"state": None, "file": None, "theorem": None, "history": []})
        yield
        _session.update({"state": None, "file": None, "theorem": None, "history": []})

    @staticmethod
    def _make_state(timeout: float = 30.0) -> dict:
        return {"pet_client": None, "pet_timeout": timeout}

    @pytest.mark.asyncio
    async def test_step_multi_concept(self, workspace):
        """Verify the concept: try tactics, session state unchanged.

        This test starts a session with rocq_step, then manually tries
        multiple tactics against the same state (simulating step_multi
        behavior) and verifies the session state is not corrupted.
        """
        from rocq_mcp.server import run_step, _session, _invalidate_pet

        vfile = workspace / "step_multi_test.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        state = self._make_state()
        try:
            # Start session
            r1 = await run_step(
                tactic="intros",
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r1["success"] is True

            # Record the session state before exploration
            saved_state = _session["state"]
            saved_history_len = len(_session["history"])

            # Now try a wrong tactic (simulating step_multi exploration)
            r2 = await run_step(
                tactic="omega_nonexistent",
                file="",
                theorem="",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r2["success"] is False

            # Session state should NOT have advanced (failed tactic)
            assert len(_session["history"]) == saved_history_len

            # Now try the correct tactic
            r3 = await run_step(
                tactic="reflexivity",
                file="",
                theorem="",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r3["success"] is True
            assert r3["proof_finished"] is True
        finally:
            _invalidate_pet(state)
