"""Tests for session staleness detection.

Unit tests exercise _check_staleness directly.
Integration tests mock pet to verify stale_warning propagates through
run_check and run_step_multi results.
"""

from __future__ import annotations

import os
import sys
import time
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from rocq_mcp.interactive import _check_staleness, _StateEntry


class TestCheckStaleness:
    """Unit tests for _check_staleness."""

    def test_no_warning_for_unchanged_file(self, tmp_path):
        """No warning when file hasn't been modified since session start."""
        f = tmp_path / "test.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        mtime = os.path.getmtime(str(f))

        entry = _StateEntry(
            state=None,
            file="test.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=mtime,
            resolved_file=str(f),
        )
        assert _check_staleness(entry) is None

    def test_warning_on_modified_file(self, tmp_path):
        """Warning when file has been modified since session start."""
        f = tmp_path / "test.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        old_mtime = os.path.getmtime(str(f))

        entry = _StateEntry(
            state=None,
            file="test.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=old_mtime,
            resolved_file=str(f),
        )

        # Modify the file (ensure mtime changes)
        time.sleep(0.05)
        f.write_text("Theorem t : False. Admitted.\n")
        os.utime(str(f), (time.time() + 1, time.time() + 1))

        warning = _check_staleness(entry)
        assert warning is not None
        assert "modified" in warning.lower()
        assert "stale" in warning.lower()

    def test_warning_on_deleted_file(self, tmp_path):
        """Warning when file has been deleted since session start."""
        f = tmp_path / "test.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        mtime = os.path.getmtime(str(f))

        entry = _StateEntry(
            state=None,
            file="test.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=mtime,
            resolved_file=str(f),
        )

        f.unlink()
        warning = _check_staleness(entry)
        assert warning is not None
        assert "no longer accessible" in warning.lower()

    def test_no_warning_for_preamble_mode(self):
        """No warning for preamble-mode states (no backing file)."""
        entry = _StateEntry(
            state=None,
            file="<preamble>",
            theorem="<preamble>",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=None,
            resolved_file=None,
        )
        assert _check_staleness(entry) is None

    def test_no_warning_when_mtime_is_none(self, tmp_path):
        """No warning when file_mtime is None (OSError during capture)."""
        f = tmp_path / "test.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        entry = _StateEntry(
            state=None,
            file="test.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=None,
            resolved_file=str(f),
        )
        assert _check_staleness(entry) is None


# ---------------------------------------------------------------------------
# Integration: stale_warning in run_check results (mock-based, no pet)
# ---------------------------------------------------------------------------


class TestStalenessInRunCheck:
    """Verify stale_warning appears in run_check success/error results."""

    @pytest.fixture(autouse=True)
    def _setup_mock_state(self, tmp_path):
        """Set up a state entry with a stale file, mock pet."""
        import rocq_mcp.interactive as _int
        import rocq_mcp.server as _srv

        # Reset state table
        _int._state_invalidate_all()
        _srv._pet_semaphore = None

        # Create a file and record its mtime
        f = tmp_path / "test.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        old_mtime = os.path.getmtime(str(f))

        # Modify file so mtime changes
        time.sleep(0.05)
        f.write_text("Theorem t : True. Proof. exact I. Qed. (* changed *)\n")
        os.utime(str(f), (time.time() + 1, time.time() + 1))

        # Create a mock state with the OLD mtime (stale)
        mock_state = SimpleNamespace(st=1, proof_finished=False, feedback=[])
        self._state_id = _int._state_add(
            state=mock_state,
            file="test.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=old_mtime,
            resolved_file=str(f),
        )

        yield
        _int._state_invalidate_all()
        _srv._pet_semaphore = None

    @pytest.fixture(autouse=True)
    def _mock_pytanque(self):
        """Ensure pytanque is importable even if not installed."""
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
    async def test_stale_warning_in_success_response(self):
        """run_check success result should include stale_warning."""
        import rocq_mcp.server as _srv
        import rocq_mcp.interactive as _int

        new_state = SimpleNamespace(st=2, proof_finished=True, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.run.return_value = new_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with patch.object(_srv, "_ensure_pet", return_value=mock_pet):
            result = await _int.run_check(
                body="exact I.",
                workspace="/tmp",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=self._state_id,
            )

        assert result["success"] is True
        assert "stale_warning" in result
        assert "modified" in result["stale_warning"].lower()

    @pytest.mark.asyncio
    async def test_stale_warning_in_error_response(self):
        """run_check error result should also include stale_warning."""
        import rocq_mcp.server as _srv
        import rocq_mcp.interactive as _int
        from pytanque import PetanqueError

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        try:
            err = PetanqueError(0, "No such tactic.")
        except TypeError:
            err = PetanqueError()
            err.message = "No such tactic."
        mock_pet.run.side_effect = err
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with patch.object(_srv, "_ensure_pet", return_value=mock_pet):
            result = await _int.run_check(
                body="bad_tactic.",
                workspace="/tmp",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=self._state_id,
            )

        assert result["success"] is False
        assert "stale_warning" in result
        assert "modified" in result["stale_warning"].lower()

    @pytest.mark.asyncio
    async def test_no_stale_warning_for_fresh_state(self, tmp_path):
        """run_check should NOT include stale_warning when file is unchanged."""
        import rocq_mcp.server as _srv
        import rocq_mcp.interactive as _int

        # Create a fresh (non-stale) state
        f = tmp_path / "fresh.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        current_mtime = os.path.getmtime(str(f))

        mock_state = SimpleNamespace(st=10, proof_finished=False, feedback=[])
        fresh_id = _int._state_add(
            state=mock_state,
            file="fresh.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            file_mtime=current_mtime,
            resolved_file=str(f),
        )

        new_state = SimpleNamespace(st=11, proof_finished=True, feedback=[])
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.run.return_value = new_state
        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": str(tmp_path),
        }

        with patch.object(_srv, "_ensure_pet", return_value=mock_pet):
            result = await _int.run_check(
                body="exact I.",
                workspace=str(tmp_path),
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=fresh_id,
            )

        assert result["success"] is True
        assert "stale_warning" not in result
