"""Tests for rocq_query via the run_query function.

These tests call run_query directly with a lifespan_state dict,
bypassing FastMCP Context injection.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from rocq_mcp.interactive import run_query
from tests.conftest import PET_AVAILABLE

_pet_only = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


from tests.conftest import make_lifespan_state as _make_lifespan_state  # noqa: E402


@pytest.fixture
def lifespan_state():
    from rocq_mcp.server import _invalidate_pet

    state = _make_lifespan_state()
    yield state
    _invalidate_pet(state)


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------


@_pet_only
class TestQuerySuccess:
    """Queries that should return valid output."""

    @pytest.mark.asyncio
    async def test_search_nat(self, workspace, lifespan_state):
        result = await run_query(
            command="Search nat.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert "nat" in result["output"].lower()

    @pytest.mark.asyncio
    async def test_check_type(self, workspace, lifespan_state):
        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert "nat" in result["output"].lower()

    @pytest.mark.asyncio
    async def test_with_preamble(self, workspace, lifespan_state):
        """Query with preamble for imports."""
        result = await run_query(
            command="Check Rplus.",
            preamble="From Coq Require Import Reals.\nOpen Scope R_scope.",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert "R" in result["output"]


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------


@_pet_only
class TestQueryEdgeCases:
    """Edge cases for query input handling."""

    @pytest.mark.asyncio
    async def test_auto_append_dot(self, workspace, lifespan_state):
        """Command without trailing dot should get one appended automatically."""
        result = await run_query(
            command="Check Nat.add",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True

    @pytest.mark.asyncio
    async def test_no_double_dot(self, workspace, lifespan_state):
        """Command already ending with dot should not get another one."""
        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------


@_pet_only
class TestQueryErrors:
    """Queries that should fail gracefully."""

    @pytest.mark.asyncio
    async def test_timeout(self, workspace):
        """A query that exceeds the timeout should return a timeout error."""
        # Use an extremely short timeout to trigger it
        state = _make_lifespan_state(pet_timeout=0.001)
        result = await run_query(
            command="Search _.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=state,
        )
        assert result["success"] is False
        assert "timed out" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_invalid_command(self, workspace, lifespan_state):
        """An invalid Rocq command should return an error."""
        result = await run_query(
            command="InvalidXYZCommand.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False
        assert result["error"]  # some error message returned


# ---------------------------------------------------------------------------
# max_results (integration tests, require pet)
# ---------------------------------------------------------------------------


@_pet_only
class TestQueryMaxResults:
    """Test the max_results parameter for result limiting."""

    @pytest.mark.asyncio
    async def test_max_results_limits_output(self, workspace, lifespan_state):
        """max_results should limit the number of Search results shown."""
        # First, get unlimited results
        unlimited = await run_query(
            command="Search nat.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert unlimited["success"] is True

        # Now get limited results
        limited = await run_query(
            command="Search nat.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            max_results=3,
        )
        assert limited["success"] is True
        # Limited output should be shorter than unlimited
        assert len(limited["output"]) <= len(unlimited["output"])
        # Should show truncation notice
        assert "more results" in limited["output"]

    @pytest.mark.asyncio
    async def test_max_results_none_shows_all(self, workspace, lifespan_state):
        """max_results=None should show all results (no truncation notice)."""
        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            max_results=None,
        )
        assert result["success"] is True
        assert "more results" not in result["output"]


# ---------------------------------------------------------------------------
# File-mode tests (unit tests, no pet required)
# ---------------------------------------------------------------------------


class TestQueryFileMode:
    """Tests for the file-based query mode (mutually exclusive with preamble)."""

    @pytest.mark.asyncio
    async def test_file_and_preamble_mutually_exclusive(self):
        """Providing both file and non-empty preamble should return error."""
        result = await run_query(
            command="Check nat.",
            preamble="Require Import Arith.",
            workspace="/tmp",
            lifespan_state={},
            file="test.v",
        )
        assert result["success"] is False
        assert "not both" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_file_with_empty_preamble_is_ok(self, tmp_path, monkeypatch):
        """file + empty preamble should not trigger the mutual exclusivity error."""
        # Create a .v file
        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")

        # Mock _run_with_pet to avoid needing actual pet
        import rocq_mcp.server as _server

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            # We just want to verify no mutual-exclusivity error was returned
            # before reaching pet. Return a fake success.
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Check x.",
            preamble="",
            workspace=str(tmp_path),
            lifespan_state={},
            file="test.v",
        )
        assert result["success"] is True

    @pytest.mark.asyncio
    async def test_file_with_whitespace_preamble_is_ok(self, tmp_path, monkeypatch):
        """file + whitespace-only preamble should be allowed."""
        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")

        import rocq_mcp.server as _server

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Check x.",
            preamble="   ",
            workspace=str(tmp_path),
            lifespan_state={},
            file="test.v",
        )
        assert result["success"] is True

    @pytest.mark.asyncio
    async def test_file_path_traversal_rejected(self, tmp_path, monkeypatch):
        """Path traversal via file parameter should be rejected."""
        import rocq_mcp.server as _server

        # Mock _run_with_pet to exercise the _do_query inner function
        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            # Call fn with a mock pet to trigger the path validation
            from unittest.mock import MagicMock

            mock_pet = MagicMock()
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Check nat.",
            preamble="",
            workspace=str(tmp_path),
            lifespan_state={"current_workspace": None},
            file="../../../etc/passwd",
        )
        assert result["success"] is False
        assert "within workspace" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_file_not_found(self, tmp_path, monkeypatch):
        """Non-existent file should return error."""
        import rocq_mcp.server as _server

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            from unittest.mock import MagicMock

            mock_pet = MagicMock()
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Check nat.",
            preamble="",
            workspace=str(tmp_path),
            lifespan_state={"current_workspace": None},
            file="nonexistent.v",
        )
        assert result["success"] is False
        assert "not found" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_absolute_path_rejected(self, tmp_path, monkeypatch):
        """Absolute file path should be rejected by containment check."""
        import rocq_mcp.server as _server

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            from unittest.mock import MagicMock

            mock_pet = MagicMock()
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Check nat.",
            preamble="",
            workspace=str(tmp_path),
            lifespan_state={"current_workspace": None},
            file="/etc/passwd",
        )
        assert result["success"] is False
        assert "within workspace" in result["error"].lower()


# ---------------------------------------------------------------------------
# _resolve_file_in_workspace unit tests
# ---------------------------------------------------------------------------


class TestResolveFileInWorkspace:
    """Unit tests for the shared path validation helper."""

    def test_valid_relative_path(self, tmp_path):
        from rocq_mcp.server import _resolve_file_in_workspace

        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")
        result = _resolve_file_in_workspace("test.v", str(tmp_path))
        assert result == str(vfile.resolve())

    def test_relative_traversal_rejected(self, tmp_path):
        from rocq_mcp.server import _resolve_file_in_workspace

        with pytest.raises(ValueError, match="within workspace"):
            _resolve_file_in_workspace("../../../etc/passwd", str(tmp_path))

    def test_absolute_path_rejected(self, tmp_path):
        from rocq_mcp.server import _resolve_file_in_workspace

        with pytest.raises(ValueError, match="within workspace"):
            _resolve_file_in_workspace("/etc/passwd", str(tmp_path))

    def test_file_not_found(self, tmp_path):
        from rocq_mcp.server import _resolve_file_in_workspace

        with pytest.raises(FileNotFoundError, match="not found"):
            _resolve_file_in_workspace("missing.v", str(tmp_path))

    def test_directory_rejected(self, tmp_path):
        """A directory path should be rejected (is_file() fails)."""
        from rocq_mcp.server import _resolve_file_in_workspace

        subdir = tmp_path / "subdir"
        subdir.mkdir()
        with pytest.raises(FileNotFoundError, match="not found"):
            _resolve_file_in_workspace("subdir", str(tmp_path))

    def test_empty_file_string(self, tmp_path):
        """Empty string resolves to workspace dir, which is not a file."""
        from rocq_mcp.server import _resolve_file_in_workspace

        with pytest.raises(FileNotFoundError):
            _resolve_file_in_workspace("", str(tmp_path))

    def test_subdirectory_file(self, tmp_path):
        from rocq_mcp.server import _resolve_file_in_workspace

        subdir = tmp_path / "sub"
        subdir.mkdir()
        vfile = subdir / "test.v"
        vfile.write_text("Definition x := 1.\n")
        result = _resolve_file_in_workspace("sub/test.v", str(tmp_path))
        assert result == str(vfile.resolve())


# ---------------------------------------------------------------------------
# _get_file_end_state edge case tests
# ---------------------------------------------------------------------------


class TestGetFileEndState:
    """Unit tests for _get_file_end_state edge cases."""

    def test_no_trailing_newline_line_count(self, tmp_path):
        """File without trailing newline should still position past the last line."""
        from rocq_mcp.interactive import _get_file_end_state
        from unittest.mock import MagicMock

        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.")  # no trailing newline

        mock_pet = MagicMock()
        mock_state = MagicMock()
        mock_pet.get_state_at_pos.return_value = mock_state

        lifespan_state = {"current_workspace": None}
        result = _get_file_end_state(mock_pet, "test.v", str(tmp_path), lifespan_state)

        assert result is mock_state
        # end_line should be 1 (count("\n") + 1 = 0 + 1), not 0
        mock_pet.get_state_at_pos.assert_called_once()
        call_args = mock_pet.get_state_at_pos.call_args
        assert call_args[0][1] == 1  # line argument

    def test_with_trailing_newline_line_count(self, tmp_path):
        """File with trailing newline should position past the last line."""
        from rocq_mcp.interactive import _get_file_end_state
        from unittest.mock import MagicMock

        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")

        mock_pet = MagicMock()
        mock_state = MagicMock()
        mock_pet.get_state_at_pos.return_value = mock_state

        lifespan_state = {"current_workspace": None}
        result = _get_file_end_state(mock_pet, "test.v", str(tmp_path), lifespan_state)

        assert result is mock_state
        # end_line should be 2 (count("\n") + 1 = 1 + 1)
        call_args = mock_pet.get_state_at_pos.call_args
        assert call_args[0][1] == 2

    def test_empty_file_line_count(self, tmp_path):
        """Empty file should position at line 1."""
        from rocq_mcp.interactive import _get_file_end_state
        from unittest.mock import MagicMock

        vfile = tmp_path / "test.v"
        vfile.write_text("")

        mock_pet = MagicMock()
        mock_state = MagicMock()
        mock_pet.get_state_at_pos.return_value = mock_state

        lifespan_state = {"current_workspace": None}
        result = _get_file_end_state(mock_pet, "test.v", str(tmp_path), lifespan_state)

        assert result is mock_state
        call_args = mock_pet.get_state_at_pos.call_args
        assert call_args[0][1] == 1  # 0 + 1

    def test_skips_workspace_reset_when_unchanged(self, tmp_path):
        """File mode delegates workspace management to
        ``_set_workspace_if_needed``: when the workspace path matches
        the cached value, no ``pet.set_workspace`` call should fire.
        The previous eager-reset behaviour thrashed pet across sibling
        calls on the same project for no Rocq-semantic benefit
        (coq-lsp re-reads the .v file on every get_state_at_pos)."""
        from rocq_mcp.interactive import _get_file_end_state
        from unittest.mock import MagicMock

        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")

        mock_pet = MagicMock()
        mock_pet.get_state_at_pos.return_value = MagicMock()

        ws = str(Path(tmp_path).resolve())
        lifespan_state = {"current_workspace": ws}

        _get_file_end_state(mock_pet, "test.v", str(tmp_path), lifespan_state)

        mock_pet.set_workspace.assert_not_called()

    def test_permission_error_gives_clean_message(self, tmp_path):
        """PermissionError should not leak the resolved absolute path."""
        from rocq_mcp.interactive import _get_file_end_state
        from unittest.mock import MagicMock, patch

        vfile = tmp_path / "secret.v"
        vfile.write_text("Definition x := 1.\n")

        mock_pet = MagicMock()
        lifespan_state = {"current_workspace": None}

        with patch.object(Path, "read_text", side_effect=PermissionError("denied")):
            with pytest.raises(FileNotFoundError, match="not accessible"):
                _get_file_end_state(mock_pet, "secret.v", str(tmp_path), lifespan_state)


# ---------------------------------------------------------------------------
# File-mode integration tests (require pet)
# ---------------------------------------------------------------------------


@_pet_only
class TestQueryFileModeIntegration:
    """Integration tests for file-based query mode (require pet)."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = _make_lifespan_state()
        yield state
        _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_query_with_file(self, workspace, lifespan_state):
        """Query using a .v file should have its definitions in scope."""
        # Write a file with a custom definition
        vfile = Path(workspace) / "query_file_test.v"
        vfile.write_text("Definition my_query_test_val := 42.\n")

        result = await run_query(
            command="Check my_query_test_val.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            file="query_file_test.v",
        )
        assert result["success"] is True
        assert "nat" in result["output"].lower() or "42" in result["output"]


# ---------------------------------------------------------------------------
# MCP wrapper tests (no pet required)
# ---------------------------------------------------------------------------


class TestRocqQueryWrapper:
    """Tests for the rocq_query MCP wrapper in server.py."""

    @pytest.mark.asyncio
    async def test_ctx_none_returns_error(self):
        from rocq_mcp.server import rocq_query

        result = await rocq_query(command="Check nat.", ctx=None)
        assert result["success"] is False
        assert "context" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_invalid_workspace_returns_error(self):
        from rocq_mcp.server import rocq_query
        from tests.conftest import _MockContext

        mock_ctx = _MockContext({})
        result = await rocq_query(
            command="Check nat.",
            workspace="/nonexistent_rocq_workspace_xyz",
            ctx=mock_ctx,
        )
        assert result["success"] is False

    @pytest.mark.asyncio
    async def test_params_forwarded(self, monkeypatch, tmp_path):
        """Wrapper should forward all params to run_query."""
        from rocq_mcp.server import rocq_query
        from tests.conftest import _MockContext
        import rocq_mcp.server as _server

        captured = {}

        async def mock_run_query(**kwargs):
            captured.update(kwargs)
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "run_query", mock_run_query)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        mock_ctx = _MockContext({"pet_client": None})

        await rocq_query(
            command="Check nat.",
            preamble="Require Import Arith.",
            file="test.v",
            workspace=str(tmp_path),
            max_results=5,
            ctx=mock_ctx,
        )

        assert captured["command"] == "Check nat."
        assert captured["preamble"] == "Require Import Arith."
        assert captured["file"] == "test.v"
        assert captured["max_results"] == 5
        assert captured["lifespan_state"] is mock_ctx.lifespan_context


# ---------------------------------------------------------------------------
# timeout parameter (per-call timeout for rocq_query)
# ---------------------------------------------------------------------------


import rocq_mcp.server as _server
from rocq_mcp.server import rocq_query
from tests.conftest import _MockContext


class TestQueryTimeoutRunQuery:
    """run_query forwards timeout to _run_with_pet."""

    @pytest.mark.asyncio
    @pytest.mark.parametrize(
        "timeout_arg,expected",
        [(None, None), (60, 60)],
        ids=["default-none", "explicit-60"],
    )
    async def test_timeout_forwarded(
        self, monkeypatch, tmp_path, timeout_arg, expected
    ):
        captured: dict = {}

        async def mock_run_with_pet(fn, lifespan_state, desc, *, timeout=None, **kw):
            captured["timeout"] = timeout
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        kwargs = {"timeout": timeout_arg} if timeout_arg is not None else {}
        result = await run_query(
            command="Check nat.",
            preamble="",
            workspace=str(tmp_path),
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            **kwargs,
        )
        assert result["success"] is True
        assert captured["timeout"] == expected


class TestRocqQueryTimeout:
    """timeout on the rocq_query MCP wrapper."""

    @staticmethod
    def _patch(monkeypatch):
        captured: dict = {}

        async def mock_run_query(**kwargs):
            captured.update(kwargs)
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "run_query", mock_run_query)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        return captured

    @pytest.mark.asyncio
    async def test_default_falls_back_to_lifespan(self, monkeypatch, tmp_path):
        captured = self._patch(monkeypatch)
        result = await rocq_query(
            command="Check nat.",
            workspace=str(tmp_path),
            ctx=_MockContext({"pet_client": None}),
        )
        assert result["success"] is True
        assert captured["timeout"] is None
        assert "clamped_timeout" not in result

    @pytest.mark.asyncio
    async def test_explicit_timeout_forwarded(self, monkeypatch, tmp_path):
        captured = self._patch(monkeypatch)
        result = await rocq_query(
            command="Time Eval vm_compute in 1.",
            workspace=str(tmp_path),
            timeout=60,
            ctx=_MockContext({"pet_client": None}),
        )
        assert result["success"] is True
        assert captured["timeout"] == 60
        assert "clamped_timeout" not in result

    @pytest.mark.asyncio
    @pytest.mark.parametrize("bad", [0, -5], ids=["zero", "negative"])
    async def test_invalid_falls_back_to_lifespan(self, monkeypatch, tmp_path, bad):
        captured = self._patch(monkeypatch)
        result = await rocq_query(
            command="Check nat.",
            workspace=str(tmp_path),
            timeout=bad,
            ctx=_MockContext({"pet_client": None}),
        )
        assert result["success"] is True
        assert captured["timeout"] is None
        assert "clamped_timeout" not in result

    @pytest.mark.asyncio
    async def test_above_cap_clamped_with_signal(self, monkeypatch, tmp_path):
        monkeypatch.setattr(_server, "ROCQ_QUERY_TIMEOUT_CAP", 100)
        captured = self._patch(monkeypatch)
        result = await rocq_query(
            command="Check nat.",
            workspace=str(tmp_path),
            timeout=9999,
            ctx=_MockContext({"pet_client": None}),
        )
        assert result["success"] is True
        assert captured["timeout"] == 100
        assert result["clamped_timeout"] == 100

    @pytest.mark.asyncio
    async def test_at_cap_not_clamped(self, monkeypatch, tmp_path):
        monkeypatch.setattr(_server, "ROCQ_QUERY_TIMEOUT_CAP", 100)
        captured = self._patch(monkeypatch)
        result = await rocq_query(
            command="Check nat.",
            workspace=str(tmp_path),
            timeout=100,
            ctx=_MockContext({"pet_client": None}),
        )
        assert result["success"] is True
        assert captured["timeout"] == 100
        assert "clamped_timeout" not in result

    def test_default_cap_is_300(self):
        assert _server.ROCQ_QUERY_TIMEOUT_CAP == 300


# ---------------------------------------------------------------------------
# from_state mode (third context mode) — unit tests
# ---------------------------------------------------------------------------


class TestQueryFromStateUnit:
    """Unit tests for run_query's from_state mode (no pet required)."""

    @pytest.mark.asyncio
    async def test_from_state_routes_to_state_lookup(self, monkeypatch):
        """from_state should call _state_get_or_error, not _get_or_create_import_state."""
        import rocq_mcp.interactive as _interactive
        from unittest.mock import MagicMock

        # Insert a fake state into the table
        from rocq_mcp.interactive import _state_add

        fake_pet_state = MagicMock()
        fake_pet_state.proof_finished = False
        sid = _state_add(
            state=fake_pet_state,
            file="",
            theorem="t",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )

        lookup_called = {"count": 0, "with_id": None}
        original = _interactive._state_get_or_error

        def spy_lookup(state_id):
            lookup_called["count"] += 1
            lookup_called["with_id"] = state_id
            return original(state_id)

        import_state_called = {"count": 0}

        def fail_import_state(*args, **kwargs):
            import_state_called["count"] += 1
            raise AssertionError("_get_or_create_import_state should not be called")

        monkeypatch.setattr(_interactive, "_state_get_or_error", spy_lookup)
        monkeypatch.setattr(
            _interactive, "_get_or_create_import_state", fail_import_state
        )

        # Stub _run_with_pet to invoke _do_query with a mock pet.
        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            mock_pet = MagicMock()
            # Make pet.run return a fake state with empty feedback.
            new_state = MagicMock()
            new_state.feedback = []
            new_state.proof_finished = False
            mock_pet.run.return_value = new_state
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            from_state=sid,
        )
        assert result["success"] is True
        assert lookup_called["count"] == 1
        assert lookup_called["with_id"] == sid
        assert import_state_called["count"] == 0

    @pytest.mark.asyncio
    async def test_from_state_with_evicted_state_returns_error(self, monkeypatch):
        """If state was evicted, return a clear error pointing to rocq_start."""
        import rocq_mcp.interactive as _interactive
        from unittest.mock import MagicMock

        # Force _state_get_or_error to return an "expired" error.
        def fake_lookup(state_id):
            return None, (
                f"State {state_id} expired: evicted from the table, lost to a "
                f"pet restart, or clobbered by another agent.  Call rocq_start."
            )

        monkeypatch.setattr(_interactive, "_state_get_or_error", fake_lookup)

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            mock_pet = MagicMock()
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            from_state=42,
        )
        assert result["success"] is False
        assert "rocq_start" in result["error"]
        assert "42" in result["error"]

    @pytest.mark.asyncio
    async def test_from_state_nonexistent_returns_error(self, monkeypatch):
        """If state was never created, return the helper's error verbatim."""
        import rocq_mcp.interactive as _interactive
        from unittest.mock import MagicMock

        def fake_lookup(state_id):
            return None, f"State {state_id} does not exist."

        monkeypatch.setattr(_interactive, "_state_get_or_error", fake_lookup)

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            mock_pet = MagicMock()
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            from_state=9999,
        )
        assert result["success"] is False
        # Verbatim helper message (no conditional re-suffix anymore).
        assert "9999" in result["error"]
        assert "does not exist" in result["error"]

    @pytest.mark.asyncio
    async def test_from_state_does_not_advance_state(self, monkeypatch):
        """The transient query state must NOT be added to the state table."""
        import rocq_mcp.interactive as _interactive
        from rocq_mcp.interactive import _state_add, _state_table
        from unittest.mock import MagicMock

        fake_pet_state = MagicMock()
        fake_pet_state.proof_finished = False
        sid = _state_add(
            state=fake_pet_state,
            file="",
            theorem="t",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )

        # Snapshot the table contents.
        table_keys_before = set(_state_table.keys())

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            mock_pet = MagicMock()
            new_state = MagicMock()
            new_state.feedback = []
            new_state.proof_finished = False
            mock_pet.run.return_value = new_state
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            from_state=sid,
        )
        assert result["success"] is True
        # State table should be unchanged: same set of state IDs.
        assert set(_state_table.keys()) == table_keys_before
        # Parent state still maps to the same pet state object.
        assert _state_table[sid].state is fake_pet_state


# ---------------------------------------------------------------------------
# from_state validation — core (run_query) and wrapper forwarding
# ---------------------------------------------------------------------------


class TestQueryFromStateValidation:
    """Validation tests for from_state — exercised against the core run_query."""

    @pytest.mark.asyncio
    async def test_from_state_and_file_mutually_exclusive(self):
        """Passing both file and from_state should fail before pet is touched."""
        result = await run_query(
            command="Check nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            file="test.v",
            from_state=1,
        )
        assert result["success"] is False
        assert "not both" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_from_state_with_preamble_rejected(self):
        """preamble + from_state must fail loudly — silent drop misleads the LLM."""
        result = await run_query(
            command="Check nat.",
            preamble="Require Import Foo.",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            from_state=1,
        )
        assert result["success"] is False
        assert "preamble" in result["error"].lower()
        assert "from_state" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_from_state_with_blank_preamble_allowed(self, monkeypatch):
        """Whitespace-only preamble + from_state is fine (no information conveyed)."""
        import rocq_mcp.interactive as _interactive
        from rocq_mcp.interactive import _state_add
        from unittest.mock import MagicMock

        fake_pet_state = MagicMock()
        fake_pet_state.proof_finished = False
        sid = _state_add(
            state=fake_pet_state,
            file="",
            theorem="t",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )

        async def mock_run_with_pet(fn, lifespan_state, desc, **kw):
            mock_pet = MagicMock()
            new_state = MagicMock()
            new_state.feedback = []
            new_state.proof_finished = False
            mock_pet.run.return_value = new_state
            return fn(mock_pet)

        monkeypatch.setattr(_server, "_run_with_pet", mock_run_with_pet)

        result = await run_query(
            command="Search nat.",
            preamble="   \n  ",
            workspace="/tmp",
            lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            from_state=sid,
        )
        assert result["success"] is True


class TestRocqQueryFromStateWrapper:
    """The wrapper now just forwards from_state — no validation here."""

    @pytest.mark.asyncio
    async def test_from_state_forwarded_to_run_query(self, monkeypatch, tmp_path):
        """Valid from_state should be forwarded to run_query."""
        captured: dict = {}

        async def mock_run_query(**kwargs):
            captured.update(kwargs)
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "run_query", mock_run_query)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        result = await rocq_query(
            command="Search nat.",
            from_state=7,
            workspace=str(tmp_path),
            ctx=_MockContext({"pet_client": None}),
        )
        assert result["success"] is True
        assert captured["from_state"] == 7

    @pytest.mark.asyncio
    async def test_from_state_default_none(self, monkeypatch, tmp_path):
        """When from_state is omitted, run_query receives None (back-compat)."""
        captured: dict = {}

        async def mock_run_query(**kwargs):
            captured.update(kwargs)
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "run_query", mock_run_query)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        await rocq_query(
            command="Check nat.",
            workspace=str(tmp_path),
            ctx=_MockContext({"pet_client": None}),
        )
        assert captured["from_state"] is None


# ---------------------------------------------------------------------------
# from_state mode integration tests (require pet)
# ---------------------------------------------------------------------------


@_pet_only
class TestQueryFromStateIntegration:
    """Integration tests for from_state mode — require pet."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = _make_lifespan_state()
        yield state
        _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_from_state_search_sees_live_context(self, workspace, lifespan_state):
        """Search via notation pattern requires the live R_scope to be open."""
        from rocq_mcp.interactive import run_start

        # Open a session with Reals + open R_scope so '+' resolves to Rplus
        # in the parsed notation pattern.  Without R_scope being open in
        # the queried state, "Search (_ + _)." would default to nat's plus
        # and Rplus would NOT appear in the results.
        start = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="From Coq Require Import Reals.\nOpen Scope R_scope.",
        )
        assert start["success"] is True
        sid = start["state_id"]

        # Notation lookup; requires R_scope to be open in the queried state.
        result = await run_query(
            command="Search (_ + _).",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            from_state=sid,
        )
        assert result["success"] is True
        # Rplus_comm / Rplus_assoc / similar Reals lemmas should appear
        # only because R_scope is open in the queried state.
        assert "Rplus" in result["output"]
        # The response should echo the queried state ID per MCP F5.
        assert result.get("from_state_id") == sid

    @pytest.mark.asyncio
    async def test_from_state_does_not_mutate_parent(self, workspace, lifespan_state):
        """Querying via from_state must not mutate the parent state's pet state."""
        from rocq_mcp.interactive import run_start, _state_table

        start = await run_start(
            file="",
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            preamble="From Coq Require Import Arith.",
        )
        assert start["success"] is True
        sid = start["state_id"]
        parent_pet_state_before = _state_table[sid].state

        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            from_state=sid,
        )
        assert result["success"] is True
        # Parent's pet state object identity preserved; entry untouched.
        assert _state_table[sid].state is parent_pet_state_before

    @pytest.mark.asyncio
    async def test_from_state_surfaces_stale_warning_when_file_changed(
        self, workspace, lifespan_state
    ):
        """If the .v file backing a session is modified after rocq_start,
        a subsequent from_state query must surface ``stale_warning`` so
        the agent knows the proof state may not match the current
        source — same contract as rocq_check."""
        from rocq_mcp.interactive import _state_table, run_start

        vfile = Path(workspace) / "stale_query.v"
        vfile.write_text("Theorem stale_thm : True.\nProof. exact I. Qed.\n")

        start = await run_start(
            file=str(vfile.relative_to(workspace)),
            theorem="stale_thm",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert start["success"] is True
        sid = start["state_id"]

        # Mutate the file's mtime (simulate an out-of-band edit).
        entry = _state_table[sid]
        assert entry.file_mtime is not None
        entry.file_mtime = entry.file_mtime - 100  # pretend session is older

        result = await run_query(
            command="Check Nat.add.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            from_state=sid,
        )
        assert result["success"] is True
        assert "stale_warning" in result
        assert "modified" in result["stale_warning"].lower()


# ---------------------------------------------------------------------------
# LSP DiagnosticSeverity wire convention (Audit finding #2)
# ---------------------------------------------------------------------------


@_pet_only
class TestLspSeverityWire:
    """Pin pet's feedback severity convention at the wire boundary.

    pet emits feedback as ``List[Tuple[int, str]]``.  Our filter
    (``_extract_feedback`` / ``run_query``) treats integer ``2`` as
    LSP DiagnosticSeverity.Warning.  If pet ever switched to Coq's
    ``Feedback.level`` enum (where 2 means Notice, 3 means Info), the
    filter would silently drop the wrong messages.

    These tests trigger a real Rocq deprecation warning
    (``From Coq Require Import …`` is deprecated in Rocq 9.x in favor
    of ``From Stdlib Require Import …``) and verify both that the wire
    integer is 2 *and* that the ``include_warnings=False`` filter
    actually drops it end-to-end.

    **Rocq version dependency**: the deprecation message text comes
    from Rocq 9.0+'s standard library namespace rename.  If a future
    Rocq stops emitting this warning (or renames the message), the
    deprecation-text assertion below should fall back to a more
    generic "warning"/"deprecat" substring match — but the
    ``2 in levels`` assertion will still hold for any LSP-severity
    warning.
    """

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = _make_lifespan_state()
        yield state
        _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_warning_level_is_lsp_severity_2(self, workspace, lifespan_state):
        """Direct pet probe: state.feedback for a deprecation must be (2, msg)."""
        from rocq_mcp.server import _ensure_pet, _set_workspace_if_needed
        from rocq_mcp.interactive import _get_or_create_import_state

        pet = _ensure_pet(lifespan_state)
        _set_workspace_if_needed(pet, str(workspace), lifespan_state)
        # Empty initial state — no preamble cached.
        state = _get_or_create_import_state(pet, str(workspace), [], lifespan_state)
        # Run a deprecated import directly — feedback on the resulting state
        # must contain the warning at LSP severity 2.
        state = pet.run(state, "From Coq Require Import Arith.")
        levels = [lvl for lvl, _ in (state.feedback or [])]
        assert 2 in levels, (
            f"Expected LSP severity 2 (Warning) in feedback levels {levels!r}; "
            "if pet ever switched to Coq Feedback.level enum (Notice=2 / "
            "Info=3), this test pins the convention."
        )
        warning_msgs = [msg for lvl, msg in (state.feedback or []) if lvl == 2]
        joined = " ".join(warning_msgs).lower()
        assert "deprecat" in joined or "from stdlib" in joined or "warning" in joined

    @pytest.mark.asyncio
    async def test_include_warnings_false_drops_real_warning(
        self, workspace, lifespan_state
    ):
        """End-to-end: include_warnings=False must drop the real Rocq warning
        from rocq_query output, validating that the level==2 filter targets
        the right messages."""
        with_warn = await run_query(
            command="From Coq Require Import Arith.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            include_warnings=True,
        )
        assert with_warn["success"] is True
        # Warning text must surface when include_warnings=True.
        assert "deprecat" in with_warn["output"].lower() or (
            "from stdlib" in with_warn["output"].lower()
        )

        without_warn = await run_query(
            command="From Coq Require Import Arith.",
            preamble="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            include_warnings=False,
        )
        assert without_warn["success"] is True
        # The deprecation warning must be filtered out.
        assert "deprecat" not in without_warn["output"].lower()
        assert "from stdlib" not in without_warn["output"].lower()
