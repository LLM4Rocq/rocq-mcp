"""Tests for run_start() — the new unified session-start function.

run_start() opens a proof context and returns a state_id.  Three modes:
1. By theorem: file + theorem -> pet.start()
2. By position: file + line + character -> pet.get_state_at_pos()
3. From imports: preamble -> _get_or_create_import_state()

These tests replace the session-start portions of test_step.py and
the position-based tests from test_step_at_pos.py.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.conftest import PET_AVAILABLE, _MockPetBase

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


from tests.conftest import make_lifespan_state as _make_lifespan_state  # noqa: E402

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture(autouse=True)
def reset_state_table():
    """Reset the state table before and after each test."""
    from rocq_mcp.interactive import _state_invalidate_all

    _state_invalidate_all()
    yield
    _state_invalidate_all()


@pytest.fixture
def lifespan_state():
    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    yield state
    _invalidate_pet(state)


@pytest.fixture
def simple_vfile(workspace):
    """Create a .v file with a simple theorem for starting a proof."""
    vfile = workspace / "start_test.v"
    vfile.write_text(
        "Theorem my_thm : forall n : nat, n = n.\n"
        "Proof.\n"
        "  intros. reflexivity.\n"
        "Qed.\n"
    )
    return str(vfile)


@pytest.fixture
def true_vfile(workspace):
    """Create a .v file with a trivial True theorem (has a goal)."""
    vfile = workspace / "start_true.v"
    vfile.write_text("Theorem t : True.\nProof. exact I. Qed.\n")
    return str(vfile)


# ---------------------------------------------------------------------------
# TestStartByTheorem
# ---------------------------------------------------------------------------


class TestStartByTheorem:
    """Tests for starting a proof session by theorem name."""

    @pytest.mark.asyncio
    async def test_start_returns_state_id(
        self, workspace, lifespan_state, simple_vfile
    ):
        """Start by theorem returns success=True and an integer state_id."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file=simple_vfile,
            theorem="my_thm",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert isinstance(result["state_id"], int)
        assert result["file"] == simple_vfile
        assert result["theorem"] == "my_thm"

    @pytest.mark.asyncio
    async def test_start_returns_goals(self, workspace, lifespan_state, true_vfile):
        """Start a theorem that has goals -- goals field should be non-empty."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file=true_vfile,
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert result["goals"]  # non-empty string

    @pytest.mark.asyncio
    async def test_start_nonexistent_theorem(
        self, workspace, lifespan_state, simple_vfile
    ):
        """Starting with a nonexistent theorem returns success=False."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file=simple_vfile,
            theorem="no_such_theorem_xyz",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False

    @pytest.mark.asyncio
    async def test_start_nonexistent_file(self, workspace, lifespan_state):
        """Starting with a nonexistent file returns success=False."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file=str(workspace / "does_not_exist.v"),
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False


# ---------------------------------------------------------------------------
# TestStartByPosition
# ---------------------------------------------------------------------------


class TestStartByPosition:
    """Tests for starting a proof session by file position."""

    @pytest.mark.asyncio
    async def test_start_by_position(self, workspace, lifespan_state):
        """Start at a position inside a proof, verify success and state_id."""
        from rocq_mcp.interactive import run_start

        vfile = workspace / "pos_start.v"
        vfile.write_text(
            "Theorem pos_thm : forall n : nat, n = n.\n"
            "Proof.\n"
            "  intros.\n"
            "  reflexivity.\n"
            "Qed.\n"
        )
        # Position (1, 0) is at the start of "Proof." line -- state after
        # the theorem statement should have the initial goal.
        result = await run_start(
            file=str(vfile),
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            line=1,
            character=0,
        )
        assert result["success"] is True
        assert isinstance(result["state_id"], int)

    @pytest.mark.asyncio
    async def test_start_position_bounds(self, workspace, lifespan_state):
        """Out-of-range line/character returns an error."""
        from rocq_mcp.interactive import run_start

        vfile = workspace / "bounds_start.v"
        vfile.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        result = await run_start(
            file=str(vfile),
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            line=200000,
            character=0,
        )
        assert result["success"] is False

    @pytest.mark.asyncio
    async def test_position_rounds_forward_through_sentence(
        self, workspace, lifespan_state
    ):
        """Pin the position semantics documented in ``rocq_start``.

        Petanque's ``get_state_at_pos`` rounds the cursor *forward*
        through the sentence containing it.  This test probes every
        category of cursor placement against a known file and asserts
        which sentence has executed:

            Line 0: Theorem foo : forall n : nat, n = n.
            Line 1: Proof. intros n. reflexivity. Qed.
                    0123456789012345678901234567890123
                          ^      ^       ^   ^   ^
                          space  i.intros .   space-after-.
                                         period

        Distinguishing signals:
        - Before ``intros n.``: goal still contains ``forall``.
        - After  ``intros n.``: goal lacks ``forall`` and an ``n :
          nat`` hypothesis is in scope.
        - After  ``reflexivity.``: ``proof_finished`` flips to True.

        Each of these is what the docstring promises will be reachable
        from the corresponding cursor position; if petanque ever
        changes the rounding rule, this test will catch it before the
        docstring goes stale.
        """
        from rocq_mcp.interactive import run_start

        vfile = workspace / "pos_semantics.v"
        vfile.write_text(
            "Theorem foo : forall n : nat, n = n.\n"
            "Proof. intros n. reflexivity. Qed.\n"
        )

        async def probe(character: int) -> dict:
            return await run_start(
                file=str(vfile),
                theorem="",
                workspace=str(workspace),
                lifespan_state=lifespan_state,
                line=1,
                character=character,
            )

        # Sentence layout on line 1: "Proof. intros n. reflexivity. Qed."
        # period positions: 5, 15, 28, 33
        # whitespace gaps:  6, 16, 29

        # --- BEFORE `intros n.` -------------------------------------------------
        # char 6 is the space immediately preceding `intros` -- whitespace
        # before a sentence yields the state BEFORE that sentence.  The
        # `Proof.` keyword is a no-op here, so the goal is the bare theorem
        # statement.
        r6 = await probe(6)
        assert r6["success"] is True
        assert r6["proof_finished"] is False
        assert "forall" in r6["goals"], (
            "Cursor at whitespace before `intros n.` should yield state BEFORE "
            f"intros (goal should still contain forall). Got: {r6['goals']!r}"
        )

        # --- AFTER `intros n.` (three equivalent cursor placements) ------------
        # Per the docstring, all of these resolve to the SAME state: after
        # `intros n.` has executed.  Once `intros n.` runs, `n : nat` is in
        # scope and `forall` is gone from the goal.
        after_intros_positions = {
            7: "first letter of `intros`",
            10: "middle of `intros`",
            15: "the period terminating `intros n.`",
            16: "whitespace immediately after the period",
        }
        for ch, label in after_intros_positions.items():
            r = await probe(ch)
            assert r["success"] is True, f"probe at char {ch} ({label}) failed"
            assert r["proof_finished"] is False, (
                f"char {ch} ({label}): proof should still be open "
                f"(reflexivity not yet run)"
            )
            assert "forall" not in r["goals"], (
                f"char {ch} ({label}): goal should no longer contain forall "
                f"after `intros n.`. Got: {r['goals']!r}"
            )
            assert "n : nat" in r["goals"] or "n: nat" in r["goals"], (
                f"char {ch} ({label}): expected `n : nat` hypothesis after "
                f"`intros n.`. Got: {r['goals']!r}"
            )

        # --- AFTER `reflexivity.` ----------------------------------------------
        # char 17 is the first letter of `reflexivity` -- rounding forward
        # through that sentence runs it, which closes the only goal.
        r17 = await probe(17)
        assert r17["success"] is True
        assert r17["proof_finished"] is True, (
            "Cursor on first letter of `reflexivity` should yield state AFTER "
            "reflexivity, with proof finished."
        )
        # And the period of `reflexivity.` plus the whitespace after it agree.
        r28 = await probe(28)
        assert r28["proof_finished"] is True
        r29 = await probe(29)
        assert r29["proof_finished"] is True


# ---------------------------------------------------------------------------
# TestStartByPreamble
# ---------------------------------------------------------------------------


class TestStartByPreamble:
    """Tests for starting from a preamble (import cache mode)."""

    @pytest.mark.asyncio
    async def test_start_preamble(self, workspace, lifespan_state):
        """Start with a preamble returns success=True, state_id, and empty goals."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="Require Import Lia.",
        )
        assert result["success"] is True
        assert isinstance(result["state_id"], int)
        # Preamble mode has no open proof, so goals should be empty
        assert result["goals"] == ""
        assert result["file"] == "<preamble>"
        assert result["theorem"] == "<preamble>"

    @pytest.mark.asyncio
    async def test_start_empty_preamble(self, workspace, lifespan_state):
        """Start with empty preamble and no file/theorem returns an error."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="",
        )
        assert result["success"] is False


# ---------------------------------------------------------------------------
# TestStartEdgeCases
# ---------------------------------------------------------------------------


class TestStartEdgeCases:
    """Edge cases: path traversal, forbidden preamble commands, etc."""

    @pytest.mark.asyncio
    async def test_path_traversal(self, workspace, lifespan_state):
        """File path escaping workspace returns success=False with path error."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file="../../../etc/passwd",
            theorem="t",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False
        # The error should mention path containment / workspace
        error_lower = result["error"].lower()
        assert "path" in error_lower or "workspace" in error_lower

    @pytest.mark.asyncio
    async def test_forbidden_preamble(self, workspace, lifespan_state):
        """Preamble containing a forbidden command (e.g., Drop) is rejected."""
        from rocq_mcp.interactive import run_start

        result = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="Drop.",
        )
        assert result["success"] is False
        assert "forbidden" in result["error"].lower() or "Drop" in result["error"]


# ---------------------------------------------------------------------------
# TestStartProofFinished: proof_finished in rocq_start response (MCP-5)
# ---------------------------------------------------------------------------


class TestStartProofFinished(_MockPetBase):
    """Test that rocq_start includes proof_finished in response.

    This is a mock-based test that does not require pet, so we override
    the module-level pytestmark skip.
    """

    @pytest.mark.asyncio
    async def test_start_theorem_proof_not_finished(self):
        """rocq_start in theorem mode: proof_finished=False when proof is open."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.start.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True. Proof. exact I. Qed.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="foo",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )

        assert result["success"] is True
        assert result["proof_finished"] is False

    @pytest.mark.asyncio
    async def test_start_theorem_proof_finished(self):
        """rocq_start in theorem mode: proof_finished=True after Qed."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=True, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.start.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True. Proof. exact I. Qed.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="foo",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )

        assert result["success"] is True
        assert result["proof_finished"] is True

    @pytest.mark.asyncio
    async def test_start_position_proof_not_finished(self):
        """rocq_start in position mode: proof_finished=False mid-proof."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.get_state_at_pos.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True.\nProof. exact I. Qed.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                    line=1,
                    character=0,
                )

        assert result["success"] is True
        assert result["proof_finished"] is False

    @pytest.mark.asyncio
    async def test_start_position_proof_finished(self):
        """rocq_start in position mode: proof_finished=True after Qed."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=True, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.get_state_at_pos.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True.\nProof. exact I. Qed.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                    line=1,
                    character=15,
                )

        assert result["success"] is True
        assert result["proof_finished"] is True

    @pytest.mark.asyncio
    async def test_start_preamble_includes_proof_finished(self):
        """rocq_start in preamble mode should include proof_finished."""
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.get_state_at_pos.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="",
                    theorem="",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                    preamble="Require Import Lia.",
                )

        assert result["success"] is True
        assert "proof_finished" in result
        assert result["proof_finished"] is False


# ---------------------------------------------------------------------------
# TestForceRestart: force_restart parameter
# ---------------------------------------------------------------------------


class TestForceRestart(_MockPetBase):
    """Test that force_restart=True kills PET and clears state before starting."""

    @pytest.mark.asyncio
    async def test_force_restart_calls_invalidate_pet(self):
        """force_restart=True should call _invalidate_pet before _run_with_pet."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.start.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True. Proof. exact I. Qed.\n")

            with (
                patch.object(rocq_mcp.server, "_invalidate_pet") as mock_invalidate,
                patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet),
            ):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="foo",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                    force_restart=True,
                )

        assert result["success"] is True
        mock_invalidate.assert_called_once_with(lifespan_state)

    @pytest.mark.asyncio
    async def test_no_force_restart_skips_invalidate(self):
        """force_restart=False (default) should NOT call _invalidate_pet."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.start.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True. Proof. exact I. Qed.\n")

            with (
                patch.object(rocq_mcp.server, "_invalidate_pet") as mock_invalidate,
                patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet),
            ):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="foo",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                    force_restart=False,
                )

        assert result["success"] is True
        mock_invalidate.assert_not_called()

    @pytest.mark.asyncio
    async def test_force_restart_clears_state_table(self):
        """force_restart=True should invalidate all existing state IDs."""
        import os
        import tempfile
        from types import SimpleNamespace
        from unittest.mock import MagicMock, patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive
        from rocq_mcp.interactive import _state_table

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False
        mock_pet.start.return_value = mock_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = _make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"

        with tempfile.TemporaryDirectory() as ws:
            test_file = os.path.join(ws, "test.v")
            with open(test_file, "w") as f:
                f.write("Theorem foo : True. Proof. exact I. Qed.\n")

            # First start — creates a state entry
            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result1 = await _interactive.run_start(
                    file="test.v",
                    theorem="foo",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                )
            old_id = result1["state_id"]
            assert old_id in _state_table

            # Second start with force_restart — old state should be gone
            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result2 = await _interactive.run_start(
                    file="test.v",
                    theorem="foo",
                    workspace=ws,
                    lifespan_state=lifespan_state,
                    force_restart=True,
                )
            assert result2["success"] is True
            # Old state ID should have been cleared by _invalidate_pet hooks
            assert old_id not in _state_table


# ---------------------------------------------------------------------------
# TestStartNotFoundEnrichment: ``available_in_file`` on theorem-not-found
# ---------------------------------------------------------------------------


def _make_toc_elem(name: str, detail: str = "Theorem", line: int = 0):
    """Mimic pytanque's TocElement for tests."""
    from types import SimpleNamespace

    return SimpleNamespace(
        name=SimpleNamespace(v=name),
        detail=detail,
        kind=0,
        range=SimpleNamespace(
            start=SimpleNamespace(line=line, character=0),
            end=SimpleNamespace(line=line + 1, character=0),
        ),
        children=None,
    )


def _make_failing_pet(toc_return):
    """Build a MagicMock pet whose ``start`` raises ``PetanqueError`` and
    whose ``toc`` returns *toc_return*.
    """
    from unittest.mock import MagicMock
    from pytanque import PetanqueError

    mock_pet = MagicMock()
    mock_pet.process = MagicMock()
    mock_pet.process.poll.return_value = None
    mock_pet._own_pgrp = False
    mock_pet.start.side_effect = PetanqueError(1, "Reference not found.")
    mock_pet.toc.return_value = toc_return
    return mock_pet


@pytest.fixture
def failing_pet_workspace(tmp_path):
    """Yield ``(tmp_path, test_file_path, lifespan_state_template)``.

    Tests build a mock pet with ``_make_failing_pet`` and inject it into
    ``lifespan_state`` plus ``patch.object(server, '_ensure_pet', ...)``.
    """
    test_file = tmp_path / "test.v"
    test_file.write_text("Theorem t : True. Proof. exact I. Qed.\n")
    return tmp_path, test_file


class TestStartNotFoundAvailableInFile(_MockPetBase):
    """rocq_start: when pet.start raises (theorem not found), attach
    ``available_in_file`` populated from pet.toc.
    """

    @pytest.fixture(autouse=True)
    def _reset_toc_cache(self):
        from rocq_mcp.interactive import _TOC_CACHE

        _TOC_CACHE.clear()
        yield
        _TOC_CACHE.clear()

    @staticmethod
    def _lifespan_state(mock_pet):
        return {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

    @pytest.mark.asyncio
    async def test_not_found_attaches_available_in_file(self, failing_pet_workspace):
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, _ = failing_pet_workspace
        mock_pet = _make_failing_pet(
            [
                (
                    "main",
                    [
                        _make_toc_elem("alpha"),
                        _make_toc_elem("my_thm"),
                        _make_toc_elem("zeta"),
                    ],
                )
            ]
        )

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_start(
                file="test.v",
                theorem="my_thm_typoed",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        assert result["success"] is False
        assert result["reason"] == "not_found"
        assert result["available_in_file"] == ["alpha", "my_thm", "zeta"]
        assert "available_in_file_truncated" not in result
        assert "available_in_file_total" not in result

    @pytest.mark.asyncio
    async def test_available_in_file_is_sorted(self, failing_pet_workspace):
        """The returned ``available_in_file`` list must be sorted."""
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, _ = failing_pet_workspace
        # Insert names out-of-order so the only way the result is sorted
        # is if the cache helper sorts.
        mock_pet = _make_failing_pet(
            [
                (
                    "main",
                    [
                        _make_toc_elem("zeta"),
                        _make_toc_elem("alpha"),
                        _make_toc_elem("my_thm"),
                        _make_toc_elem("beta"),
                    ],
                )
            ]
        )

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_start(
                file="test.v",
                theorem="missing",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        names = result["available_in_file"]
        assert names == sorted(names)
        assert names == ["alpha", "beta", "my_thm", "zeta"]

    @pytest.mark.asyncio
    async def test_truncation_marker_when_over_limit(self, failing_pet_workspace):
        """File with > 500 names → ``available_in_file_truncated`` set,
        ``available_in_file_total`` reports the actual count, list capped
        at 500.
        """
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, _ = failing_pet_workspace
        names = [f"name_{i:04d}" for i in range(750)]
        mock_pet = _make_failing_pet([("main", [_make_toc_elem(n) for n in names])])

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_start(
                file="test.v",
                theorem="missing",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        from rocq_mcp.interactive import _DEFAULT_TOC_LIMIT

        assert result["success"] is False
        assert result["available_in_file_truncated"] is True
        assert result["available_in_file_total"] == 750
        assert len(result["available_in_file"]) == 500
        # The active cap surfaces in the response so the agent doesn't
        # have to guess it.
        assert result["available_in_file_limit"] == _DEFAULT_TOC_LIMIT
        assert result["available_in_file_limit"] == 500
        # Capped to the first 500 *sorted* names.
        assert result["available_in_file"][0] == "name_0000"
        assert result["available_in_file"][-1] == "name_0499"

    @pytest.mark.asyncio
    async def test_truncation_marker_absent_when_under_limit(
        self, failing_pet_workspace
    ):
        """File with ≤ 500 names → no truncation marker fields, including
        no ``available_in_file_limit`` (the cap is only reported when it
        actually fired).
        """
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, _ = failing_pet_workspace
        names = [f"name_{i:03d}" for i in range(200)]
        mock_pet = _make_failing_pet([("main", [_make_toc_elem(n) for n in names])])

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_start(
                file="test.v",
                theorem="missing",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        assert result["success"] is False
        assert "available_in_file_truncated" not in result
        assert "available_in_file_total" not in result
        assert "available_in_file_limit" not in result
        assert len(result["available_in_file"]) == 200

    @pytest.mark.asyncio
    async def test_not_found_reason_is_not_found(self, failing_pet_workspace):
        """The ``reason`` for theorem-not-found must be ``"not_found"``,
        not ``"crashed"`` (which conflates pet death with name lookup)."""
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, _ = failing_pet_workspace
        mock_pet = _make_failing_pet([("main", [_make_toc_elem("a")])])

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_start(
                file="test.v",
                theorem="missing",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        assert result["success"] is False
        assert result["reason"] == "not_found"

    @pytest.mark.asyncio
    async def test_toc_cache_hit_avoids_re_call(self, failing_pet_workspace):
        """Two failures against the same file (same mtime) → pet.toc once."""
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, _ = failing_pet_workspace
        mock_pet = _make_failing_pet(
            [("main", [_make_toc_elem("a"), _make_toc_elem("b")])]
        )

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            await _interactive.run_start(
                file="test.v",
                theorem="missing1",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )
            await _interactive.run_start(
                file="test.v",
                theorem="missing2",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        assert mock_pet.toc.call_count == 1

    @pytest.mark.asyncio
    async def test_toc_cache_invalidation_on_mtime_change(self, failing_pet_workspace):
        """Mtime change → cache miss → pet.toc called again."""
        import os
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        ws, test_file = failing_pet_workspace
        mock_pet = _make_failing_pet([("main", [_make_toc_elem("a")])])

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            await _interactive.run_start(
                file="test.v",
                theorem="missing1",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

            # Bump mtime far enough that the new value is distinguishable
            # from the original on filesystems with low mtime resolution.
            stat = os.stat(test_file)
            os.utime(str(test_file), (stat.st_atime + 5, stat.st_mtime + 5))

            await _interactive.run_start(
                file="test.v",
                theorem="missing2",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        assert mock_pet.toc.call_count == 2

    @pytest.mark.asyncio
    async def test_toc_pet_raises_returns_empty(self, failing_pet_workspace):
        """When ``pet.toc`` raises, ``_toc_names_cached`` returns ``[]``
        and no entry is cached (so a later retry can succeed).
        """
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive
        from rocq_mcp.interactive import _TOC_CACHE

        ws, _ = failing_pet_workspace
        mock_pet = _make_failing_pet([])
        # Override toc to raise.
        mock_pet.toc.side_effect = RuntimeError("boom")

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_start(
                file="test.v",
                theorem="missing",
                workspace=str(ws),
                lifespan_state=self._lifespan_state(mock_pet),
            )

        assert result["success"] is False
        assert "available_in_file" not in result
        # Failure must not be cached — retries should be possible.
        assert _TOC_CACHE == {}

    def test_toc_cache_eviction_at_max(self):
        """Insert ``_TOC_CACHE_MAX + 1`` entries; oldest must be evicted."""
        from rocq_mcp.interactive import (
            _TOC_CACHE,
            _TOC_CACHE_MAX,
            _toc_names_cached,
        )
        import os
        import tempfile
        from unittest.mock import MagicMock

        _TOC_CACHE.clear()
        try:
            tmpdir = tempfile.mkdtemp()
            paths = []
            try:
                # Create _TOC_CACHE_MAX + 1 distinct files so each gets a
                # distinct (file, mtime) cache key.
                for i in range(_TOC_CACHE_MAX + 1):
                    p = os.path.join(tmpdir, f"f{i:03d}.v")
                    with open(p, "w") as fh:
                        fh.write("(* test *)\n")
                    paths.append(p)

                # The first file's key is what should be evicted after the
                # 51st insertion.
                first_path = paths[0]
                first_mtime = os.path.getmtime(first_path)
                first_key = (first_path, first_mtime)

                pet = MagicMock()
                pet.toc.return_value = []

                for p in paths:
                    _toc_names_cached(pet, p)

                assert len(_TOC_CACHE) == _TOC_CACHE_MAX
                assert first_key not in _TOC_CACHE
            finally:
                for p in paths:
                    try:
                        os.unlink(p)
                    except OSError:
                        pass
                try:
                    os.rmdir(tmpdir)
                except OSError:
                    pass
        finally:
            _TOC_CACHE.clear()


# ---------------------------------------------------------------------------
# TestTruncateNames: pure helper unit tests
# ---------------------------------------------------------------------------


class TestTruncateNames:
    """Unit tests for the _truncate_names helper (pure, no pet)."""

    def test_returns_all_when_under_limit(self):
        from rocq_mcp.interactive import _truncate_names

        names = ["a", "b", "c", "d"]
        capped, truncated = _truncate_names(names)
        assert capped == names
        assert truncated is False

    def test_returns_all_when_exactly_at_limit(self):
        from rocq_mcp.interactive import _truncate_names

        names = [f"n{i:04d}" for i in range(500)]
        capped, truncated = _truncate_names(names)
        assert capped == names
        assert truncated is False

    def test_truncates_when_over_limit(self):
        from rocq_mcp.interactive import _truncate_names

        names = [f"n{i:04d}" for i in range(750)]
        capped, truncated = _truncate_names(names)
        assert len(capped) == 500
        assert capped == names[:500]
        assert truncated is True

    def test_custom_limit(self):
        from rocq_mcp.interactive import _truncate_names

        names = ["a", "b", "c", "d", "e"]
        capped, truncated = _truncate_names(names, limit=3)
        assert capped == ["a", "b", "c"]
        assert truncated is True


# ---------------------------------------------------------------------------
# TestStartTimeoutForwarding: per-call timeout reaches _run_with_pet (no pet)
# ---------------------------------------------------------------------------


class TestStartTimeoutForwarding:
    """Per-call ``timeout`` is plumbed from rocq_start to _run_with_pet.

    Uses a mock-based test that doesn't require pet so it runs in CI
    without coq-lsp. Verifies the contract that callers can override
    the session-wide ROCQ_PET_TIMEOUT on a per-call basis.
    """

    pytestmark = []  # override module-level pet skip

    @pytest.mark.asyncio
    async def test_run_start_forwards_timeout(self, monkeypatch, tmp_path):
        """run_start(timeout=X) forwards X to _run_with_pet."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_start

        vfile = tmp_path / "t.v"
        vfile.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        captured: dict = {}

        async def fake_run_with_pet(fn, lifespan_state, tool, **kw):
            captured.update(kw)
            captured["tool"] = tool
            return {"success": True, "state_id": 1}

        monkeypatch.setattr(srv, "_run_with_pet", fake_run_with_pet)

        lifespan_state = _make_lifespan_state()
        await run_start(
            file=str(vfile),
            theorem="t",
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
            timeout=120.0,
        )
        assert captured["tool"] == "rocq_start"
        assert captured["timeout"] == 120.0

    @pytest.mark.asyncio
    async def test_run_start_default_timeout_is_none(self, monkeypatch, tmp_path):
        """Without explicit timeout, run_start forwards None (server default)."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_start

        vfile = tmp_path / "t.v"
        vfile.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        captured: dict = {}

        async def fake_run_with_pet(fn, lifespan_state, tool, **kw):
            captured.update(kw)
            return {"success": True, "state_id": 1}

        monkeypatch.setattr(srv, "_run_with_pet", fake_run_with_pet)

        lifespan_state = _make_lifespan_state()
        await run_start(
            file=str(vfile),
            theorem="t",
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
        )
        assert captured.get("timeout") is None

    @pytest.mark.asyncio
    async def test_wrapper_clamps_to_pet_timeout_cap(self, monkeypatch, tmp_path):
        """rocq_start clamps timeout to ROCQ_QUERY_TIMEOUT_CAP and echoes it."""
        from types import SimpleNamespace

        import rocq_mcp.server as srv

        monkeypatch.setattr(srv, "ROCQ_QUERY_TIMEOUT_CAP", 60)
        monkeypatch.setattr(srv, "_validate_workspace", lambda ws: None)

        captured: dict = {}

        async def fake_run_start(**kw):
            captured.update(kw)
            return {"success": True, "state_id": 1}

        monkeypatch.setattr(srv, "run_start", fake_run_start)

        ctx = SimpleNamespace(lifespan_context={"pet_timeout": 30.0})
        result = await srv.rocq_start(
            file="t.v",
            theorem="t",
            workspace=str(tmp_path),
            timeout=600,
            ctx=ctx,
        )
        assert captured["timeout"] == 60.0
        assert result["clamped_timeout"] == 60

    @pytest.mark.asyncio
    async def test_wrapper_does_not_clamp_below_cap(self, monkeypatch, tmp_path):
        """A timeout under the cap is forwarded unchanged with no clamped_timeout."""
        from types import SimpleNamespace

        import rocq_mcp.server as srv

        monkeypatch.setattr(srv, "ROCQ_QUERY_TIMEOUT_CAP", 300)
        monkeypatch.setattr(srv, "_validate_workspace", lambda ws: None)

        captured: dict = {}

        async def fake_run_start(**kw):
            captured.update(kw)
            return {"success": True, "state_id": 1}

        monkeypatch.setattr(srv, "run_start", fake_run_start)

        ctx = SimpleNamespace(lifespan_context={"pet_timeout": 30.0})
        result = await srv.rocq_start(
            file="t.v",
            theorem="t",
            workspace=str(tmp_path),
            timeout=120,
            ctx=ctx,
        )
        assert captured["timeout"] == 120.0
        assert "clamped_timeout" not in result
