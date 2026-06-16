"""Tests for ``focus_depth`` on interactive responses.

``focus_depth`` = ``len(complete_goals(state).stack)`` — how many ``{...}`` /
bullet focus frames are open above the currently focused goal.  It rides on
every ``rocq_check`` / ``rocq_step_multi`` / ``rocq_start`` success response so
an agent stepping through nested bullets can see how deep it is.

These are mock-based and run without ``pet``; real-pet behaviour (depth rises
after ``{`` / a bullet, falls after ``}``) is exercised by the pet-gated
integration test in ``test_check.py``.
"""

from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from tests.conftest import _MockPetBase


def _fake_goals(stack_depth: int, n_goals: int = 1) -> SimpleNamespace:
    """A fake ``complete_goals`` result with *stack_depth* focus frames."""
    return SimpleNamespace(
        goals=[SimpleNamespace(hyps=[], ty="G") for _ in range(n_goals)],
        stack=[([], []) for _ in range(stack_depth)],
        shelf=[],
        given_up=[],
    )


class TestFocusDepthHelper:
    """Unit tests for the ``_focus_depth`` pure helper."""

    pytestmark = []

    def test_none_complete_returns_none(self):
        from rocq_mcp.interactive import _focus_depth

        assert _focus_depth(None) is None

    def test_flat_context_is_zero(self):
        from rocq_mcp.interactive import _focus_depth

        assert _focus_depth(_fake_goals(0)) == 0

    def test_counts_stack_frames(self):
        from rocq_mcp.interactive import _focus_depth

        assert _focus_depth(_fake_goals(3)) == 3

    def test_missing_stack_attr_is_zero(self):
        from rocq_mcp.interactive import _focus_depth

        assert _focus_depth(SimpleNamespace(stack=None)) == 0


class TestGoalsWithDepth:
    """``_try_get_goals_with_depth`` backs the rocq_start builders."""

    pytestmark = []

    def test_returns_depth_alongside_goals(self):
        from rocq_mcp.interactive import _try_get_goals_with_depth

        mock_pet = MagicMock()
        mock_pet.complete_goals.return_value = _fake_goals(2)
        _text, depth = _try_get_goals_with_depth(mock_pet, object())
        assert depth == 2

    def test_failure_returns_none_none(self):
        from rocq_mcp.interactive import _try_get_goals_with_depth

        mock_pet = MagicMock()
        mock_pet.complete_goals.side_effect = RuntimeError("boom")
        assert _try_get_goals_with_depth(mock_pet, object()) == (None, None)


class TestFocusDepthCheck(_MockPetBase):
    """``focus_depth`` on the ``run_check`` success envelope."""

    @pytest.mark.asyncio
    async def test_check_reports_focus_depth(self):
        import rocq_mcp.server as srv
        import rocq_mcp.interactive as _interactive

        new_state = SimpleNamespace(st=43, proof_finished=False, feedback=[])

        def fake_run(state, cmd, timeout=None):
            return new_state

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)
        mock_pet.complete_goals.return_value = _fake_goals(2)

        with patch.object(srv, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="intros.",
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert result["focus_depth"] == 2


class TestFocusDepthStepMulti(_MockPetBase):
    """``focus_depth`` on each ``run_step_multi`` per-tactic entry."""

    @pytest.mark.asyncio
    async def test_step_multi_reports_focus_depth_per_entry(self):
        import rocq_mcp.server as srv
        import rocq_mcp.interactive as _interactive

        new_state = SimpleNamespace(st=43, proof_finished=False, feedback=[])

        def fake_run(state, cmd, timeout=None):
            return new_state

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)
        mock_pet.complete_goals.return_value = _fake_goals(1)

        with patch.object(srv, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_step_multi(
                tactics=["intros.", "auto."],
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert len(result["results"]) == 2
        for entry in result["results"]:
            assert entry["success"] is True
            assert entry["focus_depth"] == 1
