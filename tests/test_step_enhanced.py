"""Tests for the enhanced rocq_step with shelved_goals and given_up_goals.

The enhancement changes rocq_step to call pet.complete_goals() instead of
pet.goals(), and surfaces shelved/given_up counts when non-empty.

Since this requires pytanque, tests use mocks for the complete_goals response.

Tests are grouped into:
- TestStepEnhancedReal: tests that call the real run_step with mocked pet
- TestStepEnhancedIntegration: integration tests (require pet)
"""

from __future__ import annotations

import asyncio
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

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


def _make_mock_hyp(names, ty, def_=None):
    """Create a mock hypothesis object for _format_goals."""
    return SimpleNamespace(names=names, ty=ty, def_=def_)


def _make_structured_goal(hyps, ty):
    """Create a goal with hyps and ty attributes for _format_goals."""
    return SimpleNamespace(hyps=hyps, ty=ty, pp="")


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
# TestStepEnhancedReal: tests that call the real run_step with mocked pet
# ---------------------------------------------------------------------------


class TestStepEnhancedReal:
    """Tests that call the actual run_step function with a mocked pet client."""

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

    def test_run_step_with_shelved_goals(self, tmp_path):
        """Real run_step with mocked pet that returns shelved goals."""
        from rocq_mcp.server import run_step, _session

        # Set up active session so run_step doesn't try to start a new one
        parent_state = _make_mock_state(proof_finished=False)
        _session.update(
            {
                "state": parent_state,
                "file": "test.v",
                "theorem": "t",
                "history": ["intros."],
            }
        )

        # Build a mock pet that returns complete_goals with shelved goals
        mock_pet = MagicMock()
        new_state = _make_mock_state(proof_finished=False)
        mock_pet.run = MagicMock(return_value=new_state)
        mock_pet.complete_goals = MagicMock(
            return_value=_make_complete_goals(
                goals=[
                    _make_structured_goal(
                        hyps=[_make_mock_hyp(["n"], "nat")],
                        ty="n + 0 = n",
                    )
                ],
                shelf=[
                    _make_mock_goal("shelved goal 1"),
                    _make_mock_goal("shelved goal 2"),
                ],
            )
        )

        lifespan_state = {"pet_client": None, "pet_timeout": 30.0}

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = asyncio.run(
                run_step(
                    tactic="simpl",
                    file="",
                    theorem="",
                    workspace=str(tmp_path),
                    lifespan_state=lifespan_state,
                )
            )

        assert result["success"] is True
        assert "shelved_goals" in result
        assert result["shelved_goals"] == 2
        assert "n + 0 = n" in result["goals"]
        assert result["step"] == 2  # history had 1, now 2

    def test_run_step_no_shelf_omits_key(self, tmp_path):
        """Real run_step with mocked pet that returns empty shelf omits shelved_goals."""
        from rocq_mcp.server import run_step, _session

        parent_state = _make_mock_state(proof_finished=False)
        _session.update(
            {
                "state": parent_state,
                "file": "test.v",
                "theorem": "t",
                "history": [],
            }
        )

        mock_pet = MagicMock()
        new_state = _make_mock_state(proof_finished=True)
        mock_pet.run = MagicMock(return_value=new_state)
        mock_pet.complete_goals = MagicMock(
            return_value=_make_complete_goals(
                goals=[],
                shelf=[],
                given_up=[],
            )
        )

        lifespan_state = {"pet_client": None, "pet_timeout": 30.0}

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = asyncio.run(
                run_step(
                    tactic="reflexivity",
                    file="",
                    theorem="",
                    workspace=str(tmp_path),
                    lifespan_state=lifespan_state,
                )
            )

        assert result["success"] is True
        assert result["proof_finished"] is True
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
            # For a simple proof, shelved_goals should NOT be present.
            # The key is only added when the shelf is non-empty.
            assert "shelved_goals" not in r
        finally:
            _invalidate_pet(state)
