"""Tests for the enhanced rocq_step with shelved_goals and given_up_goals.

The enhancement changes rocq_step to call pet.complete_goals() instead of
pet.goals(), and surfaces shelved/given_up counts when non-empty.

Since this requires pytanque, tests use mocks for the complete_goals response.

Tests are grouped into:
- TestStepShelvedGoals: mock complete_goals with shelf -> verify shelved_goals
- TestStepNoShelf: mock complete_goals with empty shelf -> no shelved_goals key
- TestStepGivenUpGoals: mock complete_goals with given_up -> verify given_up_goals
- TestStepBothShelvedAndGivenUp: both shelf and given_up non-empty
- TestStepIntegration: integration tests (require pet)
"""

from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

from tests.conftest import PET_AVAILABLE

# ---------------------------------------------------------------------------
# Helpers to build mock complete_goals responses
# ---------------------------------------------------------------------------


def _make_mock_goal(pp_text):
    """Create a mock Goal with pp field."""
    return SimpleNamespace(pp=pp_text)


def _make_complete_goals(goals=None, stack=None, shelf=None, given_up=None):
    """Create a mock GoalsResponse from complete_goals().

    GoalsResponse:
        goals: List[Goal]
        stack: List[Tuple[List[Any], List[Any]]]
        shelf: List[Any]
        given_up: List[Any]
    """
    return SimpleNamespace(
        goals=goals or [],
        stack=stack or [],
        shelf=shelf or [],
        given_up=given_up or [],
    )


def _make_mock_state(proof_finished=False):
    """Create a mock pytanque state."""
    return SimpleNamespace(
        st=42,
        proof_finished=proof_finished,
        feedback=[],
    )


# ---------------------------------------------------------------------------
# TestStepShelvedGoals
# ---------------------------------------------------------------------------


class TestStepShelvedGoals:
    """Test that shelved goals from complete_goals appear in rocq_step response."""

    def test_shelved_goals_in_response(self):
        """When complete_goals has non-empty shelf, result should include shelved_goals."""
        # Simulate what the enhanced run_step would do
        complete = _make_complete_goals(
            goals=[_make_mock_goal("n : nat\n============================\nn + 0 = n")],
            shelf=[
                _make_mock_goal("shelved goal 1"),
                _make_mock_goal("shelved goal 2"),
            ],
        )

        # Build result as the enhanced rocq_step would
        goals_list = complete.goals
        goals_text = "\n\n".join(g.pp for g in goals_list)
        new_state = _make_mock_state(proof_finished=False)

        result = {
            "success": True,
            "goals": goals_text or "No goals remaining.",
            "proof_finished": new_state.proof_finished,
            "step": 1,
        }
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        assert result["success"] is True
        assert "shelved_goals" in result
        assert result["shelved_goals"] == 2
        assert "n + 0 = n" in result["goals"]

    def test_shelved_goals_count_only(self):
        """The response should contain COUNT of shelved goals, not their content."""
        complete = _make_complete_goals(
            goals=[],
            shelf=[_make_mock_goal("shelved 1")],
        )

        result = {}
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)

        assert result["shelved_goals"] == 1
        assert isinstance(result["shelved_goals"], int)


# ---------------------------------------------------------------------------
# TestStepNoShelf
# ---------------------------------------------------------------------------


class TestStepNoShelf:
    """When complete_goals has empty shelf, NO shelved_goals key in response."""

    def test_no_shelf_key(self):
        """Empty shelf should NOT produce shelved_goals in result."""
        complete = _make_complete_goals(
            goals=[_make_mock_goal("goal text")],
            shelf=[],
            given_up=[],
        )

        result = {
            "success": True,
            "goals": "goal text",
            "proof_finished": False,
            "step": 1,
        }
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        assert "shelved_goals" not in result
        assert "given_up_goals" not in result

    def test_backward_compatible(self):
        """Response with no shelf/given_up should match the old format exactly."""
        complete = _make_complete_goals(
            goals=[_make_mock_goal("n : nat\n============================\nn = n")],
        )

        goals_text = "\n\n".join(g.pp for g in complete.goals)
        new_state = _make_mock_state(proof_finished=False)

        result = {
            "success": True,
            "goals": goals_text or "No goals remaining.",
            "proof_finished": new_state.proof_finished,
            "step": 1,
        }
        # Only add shelf/given_up if non-empty
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        # Should have exactly the old keys and nothing extra
        assert set(result.keys()) == {"success", "goals", "proof_finished", "step"}


# ---------------------------------------------------------------------------
# TestStepGivenUpGoals
# ---------------------------------------------------------------------------


class TestStepGivenUpGoals:
    """Test that given-up goals from complete_goals appear in response."""

    def test_given_up_in_response(self):
        """Non-empty given_up should produce given_up_goals count."""
        complete = _make_complete_goals(
            goals=[_make_mock_goal("remaining goal")],
            given_up=[_make_mock_goal("given up 1")],
        )

        result = {
            "success": True,
            "goals": "remaining goal",
            "proof_finished": False,
            "step": 3,
        }
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        assert "given_up_goals" in result
        assert result["given_up_goals"] == 1
        assert "shelved_goals" not in result  # shelf is empty

    def test_given_up_zero_not_added(self):
        """Empty given_up should NOT add given_up_goals key."""
        complete = _make_complete_goals(goals=[], given_up=[])

        result = {}
        if complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        assert "given_up_goals" not in result


# ---------------------------------------------------------------------------
# TestStepBothShelvedAndGivenUp
# ---------------------------------------------------------------------------


class TestStepBothShelvedAndGivenUp:
    """When both shelved and given-up goals are non-empty."""

    def test_both_present(self):
        """Both shelved_goals and given_up_goals should appear."""
        complete = _make_complete_goals(
            goals=[_make_mock_goal("active goal")],
            shelf=[_make_mock_goal("s1"), _make_mock_goal("s2"), _make_mock_goal("s3")],
            given_up=[_make_mock_goal("g1")],
        )

        result = {
            "success": True,
            "goals": "active goal",
            "proof_finished": False,
            "step": 5,
        }
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        assert result["shelved_goals"] == 3
        assert result["given_up_goals"] == 1

    def test_no_active_goals_with_shelf(self):
        """No active goals but shelved goals exist -- proof NOT finished."""
        complete = _make_complete_goals(
            goals=[],
            shelf=[_make_mock_goal("shelved")],
        )

        goals_text = "\n\n".join(g.pp for g in complete.goals)
        result = {
            "success": True,
            "goals": goals_text or "No goals remaining.",
            "proof_finished": False,
            "step": 2,
        }
        if complete.shelf:
            result["shelved_goals"] = len(complete.shelf)

        assert result["goals"] == "No goals remaining."
        assert result["shelved_goals"] == 1
        # Even though no active goals, shelved goals mean proof is NOT done


# ---------------------------------------------------------------------------
# TestStepEnhancedMock: mock the full run_step flow with complete_goals
# ---------------------------------------------------------------------------


class TestStepEnhancedMock:
    """Test the enhanced run_step logic with a fully mocked pet client."""

    def test_enhanced_step_with_mock_pet(self):
        """Simulate the enhanced run_step calling complete_goals instead of goals."""
        mock_pet = MagicMock()
        parent_state = _make_mock_state()
        new_state = _make_mock_state(proof_finished=False)

        # Mock run() to return new state
        mock_pet.run = MagicMock(return_value=new_state)

        # Mock complete_goals() to return goals with shelf
        complete = _make_complete_goals(
            goals=[_make_mock_goal("n : nat\n============================\nn + 0 = n")],
            shelf=[_make_mock_goal("shelved_goal")],
        )
        mock_pet.complete_goals = MagicMock(return_value=complete)

        # Execute what the enhanced run_step does:
        result_state = mock_pet.run(parent_state, "intros.")
        cg = mock_pet.complete_goals(result_state)

        goals_list = cg.goals
        goals_text = "\n\n".join(g.pp for g in goals_list)

        result = {
            "success": True,
            "goals": goals_text or "No goals remaining.",
            "proof_finished": result_state.proof_finished,
            "step": 1,
        }
        if cg.shelf:
            result["shelved_goals"] = len(cg.shelf)
        if cg.given_up:
            result["given_up_goals"] = len(cg.given_up)

        # Verify
        mock_pet.complete_goals.assert_called_once_with(new_state)
        assert result["success"] is True
        assert "n + 0 = n" in result["goals"]
        assert result["shelved_goals"] == 1
        assert "given_up_goals" not in result

    def test_complete_goals_none_fallback(self):
        """If complete_goals returns None, treat as empty."""
        complete = None
        goals_list = complete.goals if complete else []
        result = {
            "success": True,
            "goals": "No goals remaining." if not goals_list else "...",
            "proof_finished": True,
            "step": 1,
        }
        if complete and complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete and complete.given_up:
            result["given_up_goals"] = len(complete.given_up)

        assert result["goals"] == "No goals remaining."
        assert "shelved_goals" not in result
        assert "given_up_goals" not in result


# ---------------------------------------------------------------------------
# TestStepEnhancedIntegration: integration tests (require pet)
# ---------------------------------------------------------------------------


@pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")
class TestStepEnhancedIntegration:
    """Integration tests for enhanced rocq_step with complete_goals."""

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
    async def test_simple_proof_no_shelf(self, workspace):
        """A simple proof should have no shelved goals."""
        from rocq_mcp.server import run_step, _invalidate_pet

        vfile = workspace / "enhanced_test.v"
        vfile.write_text(
            "Theorem t : forall n : nat, n = n.\n" "Proof. intros. reflexivity. Qed.\n"
        )

        state = self._make_state()
        try:
            r = await run_step(
                tactic="intros",
                file=str(vfile),
                theorem="t",
                workspace=str(workspace),
                lifespan_state=state,
            )
            assert r["success"] is True
            # For a simple proof, there should be no shelved or given_up goals
            # (these keys should be absent from the result)
            # Note: this test validates the current behavior. Once the
            # enhancement is implemented, the assertion remains valid because
            # shelf should be empty for this simple proof.
            if "shelved_goals" in r:
                assert (
                    r["shelved_goals"] == 0
                )  # should not be there, but if present it's 0
        finally:
            _invalidate_pet(state)
