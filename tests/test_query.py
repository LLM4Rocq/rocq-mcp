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


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
    }


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

    def test_forces_workspace_reset(self, tmp_path):
        """File mode should force workspace re-set for coq-lsp re-indexing."""
        from rocq_mcp.interactive import _get_file_end_state
        from unittest.mock import MagicMock

        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")

        mock_pet = MagicMock()
        mock_pet.get_state_at_pos.return_value = MagicMock()

        # Set current_workspace to the same workspace (would skip re-set normally)
        ws = str(Path(tmp_path).resolve())
        lifespan_state = {"current_workspace": ws}

        _get_file_end_state(mock_pet, "test.v", str(tmp_path), lifespan_state)

        # Should have been forced to None then re-set
        mock_pet.set_workspace.assert_called_once()

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
        from unittest.mock import MagicMock

        mock_ctx = MagicMock()
        mock_ctx.lifespan_context = {}
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
        from unittest.mock import MagicMock
        import rocq_mcp.server as _server

        captured = {}

        async def mock_run_query(**kwargs):
            captured.update(kwargs)
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "run_query", mock_run_query)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        mock_ctx = MagicMock()
        mock_ctx.lifespan_context = {"pet_client": None}

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
