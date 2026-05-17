"""Tests for the bullet / focus-management payload of ``rocq_check``.

When ``rocq_check`` is invoked with a body that is a single bullet or
focus-management command (``{``, ``}``, or a run of ``-``/``+``/``*``),
the response is enriched with extra keys so the agent can see the
focus transition rather than an empty ``goals`` string.

These tests use mocks rather than a real pet so they run in any
environment.  ``test_check.py`` carries a real-pet variant
(``TestCheckBulletFocusPayload``) that is skipped when pet is not
available.
"""

from __future__ import annotations

import sys
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

# ---------------------------------------------------------------------------
# Detector: pure unit tests, no pet, no mocks needed.
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "body,expected",
    [
        ("{", "{"),
        ("}", "}"),
        ("{.", "{"),
        ("  } .  ", "}"),
        ("-", "-"),
        ("--", "--"),
        ("+++", "+++"),
        ("**", "**"),
        ("- .", "-"),
        # Negative cases
        ("intros.", None),
        ("- intros.", None),
        ("-+", None),
        ("{ reflexivity. }", None),
        ("", None),
        ("   ", None),
        ("..", None),
    ],
)
def test_detect_bullet_focus_token(body, expected):
    from rocq_mcp.interactive import _detect_bullet_focus_token

    assert _detect_bullet_focus_token(body) == expected


# ---------------------------------------------------------------------------
# Mock-based integration of the payload via ``run_check``.
# ---------------------------------------------------------------------------


@pytest.fixture
def mock_pytanque():
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


@pytest.fixture
def reset_state():
    import rocq_mcp.server as srv
    from rocq_mcp.interactive import _state_invalidate_all

    _state_invalidate_all()
    srv._pet_semaphore = None
    yield
    _state_invalidate_all()
    srv._pet_semaphore = None


def _make_lifespan(pet):
    return {
        "pet_client": pet,
        "pet_timeout": 30.0,
        "current_workspace": "/tmp",
    }


@pytest.mark.asyncio
async def test_open_brace_adds_focus_payload(mock_pytanque, reset_state):
    """``{`` after a 2-subgoal state focuses to 1 goal and pushes one
    focus frame onto the stack.  All five payload keys must appear with
    the expected values."""
    import rocq_mcp.server
    import rocq_mcp.interactive as _interactive

    before_state = SimpleNamespace(st=10, proof_finished=False, feedback=[])
    sid = _interactive._state_add(
        state=before_state,
        file="test.v",
        theorem="test",
        workspace="/tmp",
        parent_id=None,
        tactic=None,
        step=0,
    )

    after_state = SimpleNamespace(st=11, proof_finished=False, feedback=[])

    mock_pet = MagicMock()
    mock_pet.process = MagicMock()
    mock_pet.process.poll.return_value = None
    mock_pet.run = MagicMock(return_value=after_state)

    g1 = SimpleNamespace(hyps=[], ty="b = b")
    g2 = SimpleNamespace(hyps=[], ty="false = false")

    # before: 2 goals, empty stack.  after: 1 focused goal, 1 stack frame.
    before_resp = SimpleNamespace(goals=[g1, g2], stack=[], shelf=[], given_up=[])
    after_resp = SimpleNamespace(goals=[g1], stack=[([], [g2])], shelf=[], given_up=[])
    mock_pet.complete_goals = MagicMock(side_effect=[before_resp, after_resp])

    with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
        result = await _interactive.run_check(
            body="{",
            timeout=30.0,
            lifespan_state=_make_lifespan(mock_pet),
            from_state=sid,
        )

    assert result["success"] is True
    assert result["focus_command"] == "{"
    assert result["goals_before"] == 2
    assert result["goals_after"] == 1
    assert result["focus_depth_before"] == 0
    assert result["focus_depth_after"] == 1
    # The existing ``goals`` key is preserved (additive contract).
    assert "goals" in result
    # pet must receive the BARE brace: Coq rejects a trailing '.' after
    # '{'/'}', so the command sent must be "{" and not "{.".
    assert mock_pet.run.call_args.args[1] == "{"


@pytest.mark.asyncio
async def test_dash_bullet_payload(mock_pytanque, reset_state):
    """A ``-`` bullet should also get the focus payload (no stack change,
    just a focus shift between subgoals)."""
    import rocq_mcp.server
    import rocq_mcp.interactive as _interactive

    before_state = SimpleNamespace(st=30, proof_finished=False, feedback=[])
    sid = _interactive._state_add(
        state=before_state,
        file="test.v",
        theorem="test",
        workspace="/tmp",
        parent_id=None,
        tactic=None,
        step=0,
    )
    after_state = SimpleNamespace(st=31, proof_finished=False, feedback=[])

    mock_pet = MagicMock()
    mock_pet.process = MagicMock()
    mock_pet.process.poll.return_value = None
    mock_pet.run = MagicMock(return_value=after_state)

    g = SimpleNamespace(hyps=[], ty="P")
    before_resp = SimpleNamespace(goals=[g, g], stack=[], shelf=[], given_up=[])
    after_resp = SimpleNamespace(goals=[g], stack=[], shelf=[], given_up=[])
    mock_pet.complete_goals = MagicMock(side_effect=[before_resp, after_resp])

    with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
        result = await _interactive.run_check(
            body="-",
            timeout=30.0,
            lifespan_state=_make_lifespan(mock_pet),
            from_state=sid,
        )

    assert result["success"] is True
    assert result["focus_command"] == "-"
    assert result["goals_before"] == 2
    assert result["goals_after"] == 1


@pytest.mark.asyncio
async def test_non_bullet_body_unaffected(mock_pytanque, reset_state):
    """Plain tactic bodies must NOT gain any focus-payload keys."""
    import rocq_mcp.server
    import rocq_mcp.interactive as _interactive

    before_state = SimpleNamespace(st=20, proof_finished=False, feedback=[])
    sid = _interactive._state_add(
        state=before_state,
        file="test.v",
        theorem="test",
        workspace="/tmp",
        parent_id=None,
        tactic=None,
        step=0,
    )
    after_state = SimpleNamespace(st=21, proof_finished=False, feedback=[])

    mock_pet = MagicMock()
    mock_pet.process = MagicMock()
    mock_pet.process.poll.return_value = None
    mock_pet.run = MagicMock(return_value=after_state)
    mock_pet.complete_goals = MagicMock(
        return_value=SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
    )

    with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
        result = await _interactive.run_check(
            body="intros.",
            timeout=30.0,
            lifespan_state=_make_lifespan(mock_pet),
            from_state=sid,
        )

    assert result["success"] is True
    for k in (
        "focus_command",
        "goals_before",
        "goals_after",
        "focus_depth_before",
        "focus_depth_after",
    ):
        assert k not in result
