"""Tests for the rocq_compile_file tool."""

from __future__ import annotations

import asyncio
import glob as glob_mod
import pytest

from tests.conftest import (
    COQC_AVAILABLE,
    _MockContext,
    _fake_coqc_result,
    make_lifespan_state,
)
from rocq_mcp.compile import run_compile_file

pytestmark = pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------


class TestCompileFileSuccess:
    """Files that compile without error."""

    def test_simple_proof_file(self, workspace, simple_proof):
        path = workspace / "simple.v"
        path.write_text(simple_proof)
        result = run_compile_file(file="simple.v", workspace=str(workspace), timeout=60)
        assert result["success"] is True

    def test_empty_file(self, workspace):
        path = workspace / "empty.v"
        path.write_text("")
        result = run_compile_file(file="empty.v", workspace=str(workspace), timeout=60)
        assert result["success"] is True


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------


class TestCompileFileErrors:
    """Files that should fail compilation with a clear error."""

    def test_type_error(self, workspace):
        path = workspace / "type_err.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="type_err.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error" in result
        assert len(result["error"]) > 0

    def test_error_uses_file_label(self, workspace):
        """Error output should use the file name, not <proof>."""
        path = workspace / "label_test.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="label_test.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "label_test.v" in result["error"]
        assert "<proof>" not in result["error"]


# ---------------------------------------------------------------------------
# Input validation
# ---------------------------------------------------------------------------


class TestCompileFileValidation:
    """Edge cases around path validation."""

    def test_nonexistent_file(self, workspace):
        result = run_compile_file(
            file="nonexistent.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "not found" in result["error"].lower()

    def test_path_traversal(self, workspace):
        result = run_compile_file(
            file="../../../etc/passwd", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "within workspace" in result["error"].lower()

    def test_oversized_file(self, workspace, monkeypatch):
        path = workspace / "big.v"
        path.write_text("x" * 100)
        import rocq_mcp.server as _srv

        monkeypatch.setattr(_srv, "ROCQ_MAX_SOURCE_SIZE", 50)
        result = run_compile_file(file="big.v", workspace=str(workspace), timeout=60)
        assert result["success"] is False
        assert "size" in result["error"].lower()


# ---------------------------------------------------------------------------
# Cleanup
# ---------------------------------------------------------------------------


class TestCompileFileCleanup:
    """Compilation should clean artifacts but preserve the source .v file."""

    def test_source_preserved_artifacts_cleaned(self, workspace, simple_proof):
        path = workspace / "preserved.v"
        path.write_text(simple_proof)
        run_compile_file(file="preserved.v", workspace=str(workspace), timeout=60)
        # Source file must still exist
        assert path.exists(), "Source .v file was deleted"
        # Artifacts should be cleaned
        base = workspace / "preserved"
        for ext in [".vo", ".vok", ".vos", ".glob"]:
            assert not base.with_suffix(ext).exists(), f"Artifact {ext} not cleaned"

    def test_source_preserved_on_error(self, workspace):
        path = workspace / "err_preserve.v"
        path.write_text("Theorem bad : .\nQed.\n")
        run_compile_file(file="err_preserve.v", workspace=str(workspace), timeout=60)
        assert path.exists(), "Source .v file was deleted on error"


# ---------------------------------------------------------------------------
# Forbidden commands
# ---------------------------------------------------------------------------


class TestCompileFileForbidden:
    """Files with forbidden commands should be rejected before compilation."""

    def test_drop_command_rejected(self, workspace):
        path = workspace / "forbidden_drop.v"
        path.write_text("Drop.\n")
        result = run_compile_file(
            file="forbidden_drop.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error" in result

    def test_redirect_rejected(self, workspace):
        path = workspace / "forbidden_redirect.v"
        path.write_text('Redirect "/tmp/out" Check nat.\n')
        result = run_compile_file(
            file="forbidden_redirect.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error" in result


# ---------------------------------------------------------------------------
# Directory handling
# ---------------------------------------------------------------------------


class TestCompileFileDirectory:
    """Edge cases for directory paths."""

    def test_not_a_file(self, workspace):
        subdir = workspace / "subdir"
        subdir.mkdir(exist_ok=True)
        result = run_compile_file(file="subdir", workspace=str(workspace), timeout=60)
        assert result["success"] is False
        assert "not found" in result["error"].lower()


# ---------------------------------------------------------------------------
# Timeout (monkeypatched)
# ---------------------------------------------------------------------------


class TestCompileFileTimeout:
    """Test timeout handling via monkeypatched _run_coqc_file."""

    # Override module-level skip — these tests use monkeypatch, not real coqc
    pytestmark = []

    def test_timeout_returns_error(self, workspace, monkeypatch):
        """When _run_coqc_file reports timed_out=True, result shows timeout error."""
        path = workspace / "timeout_test.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        import rocq_mcp.compile as _compile

        monkeypatch.setattr(
            _compile,
            "_run_coqc_file",
            lambda fp, ws, to: {
                "returncode": -1,
                "stdout": "",
                "stderr": "",
                "timed_out": True,
            },
        )
        result = run_compile_file(
            file="timeout_test.v", workspace=str(workspace), timeout=5
        )
        assert result["success"] is False
        assert "timed out" in result["error"].lower()


# ---------------------------------------------------------------------------
# Structured error output
# ---------------------------------------------------------------------------


class TestCompileFileStructuredErrors:
    """Verify error_positions and hint keys in structured error output."""

    def test_error_positions_present(self, workspace):
        """Compilation error should include error_positions with line info."""
        path = workspace / "pos_test.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="pos_test.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error_positions" in result
        assert len(result["error_positions"]) >= 1
        pos = result["error_positions"][0]
        assert "line" in pos
        assert "character" in pos
        assert "message" in pos

    def test_hint_present_on_error(self, workspace):
        """Compilation error should include a hint."""
        path = workspace / "hint_test.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="hint_test.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "hint" in result


# ---------------------------------------------------------------------------
# Proof-state capture on compile errors
# ---------------------------------------------------------------------------


class TestCompileFileErrorStateCapture:
    """Compile-file orchestration: only the file-path-specific behaviours.

    Status-derivation logic is exercised by ``test_compile.TestStateCaptureStatus``
    via the inline-source path; the file-path code path shares the same
    ``_capture_compile_error_state`` machinery, so we only assert here the
    file-resolution glue (resolved_file, file_label).
    """

    pytestmark = []

    def test_compile_file_capture_receives_resolved_path(self, workspace, monkeypatch):
        """The resolved path and file_label flow through to capture_position_state."""
        import rocq_mcp.compile as _compile
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as _server

        path = workspace / "resolved_path_test.v"
        path.write_text("Theorem bad : True.\n  exact 0.\n")
        stderr = (
            'File "resolved_path_test.v", line 2, characters 1-8:\n'
            "Error: Real failure.\n"
        )
        captured = {}

        monkeypatch.setattr(
            _compile,
            "_run_coqc_file",
            lambda *a, **kw: _fake_coqc_result(stderr),
        )

        async def _mock_cps(**kwargs):
            captured.update(kwargs)
            return {"success": False, "error": "boom", "pet_restarted": True}

        monkeypatch.setattr(_interactive, "capture_position_state", _mock_cps)

        asyncio.run(
            _server.run_compile_file_with_state(
                file="resolved_path_test.v",
                workspace=str(workspace),
                timeout=60,
                lifespan_state=make_lifespan_state(),
            )
        )

        assert captured["file"] == "resolved_path_test.v"
        assert captured["resolved_file"] == str(path.resolve())

    def test_status_no_position_when_path_resolution_fails(
        self, workspace, monkeypatch
    ):
        """A path that escapes the workspace short-circuits with status='no_position'."""
        import rocq_mcp.compile as _compile
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as _server

        stderr = "Error: nonsense.\n"
        cps_called = {"called": False}

        monkeypatch.setattr(
            _compile,
            "_run_coqc_file",
            lambda *a, **kw: _fake_coqc_result(stderr),
        )

        async def _mock_cps(**kwargs):
            cps_called["called"] = True
            return {"success": False, "error": "should not be reached"}

        monkeypatch.setattr(_interactive, "capture_position_state", _mock_cps)

        result = asyncio.run(
            _server.run_compile_file_with_state(
                file="../escaping_path.v",
                workspace=str(workspace),
                timeout=60,
                lifespan_state=make_lifespan_state(),
            )
        )

        assert result["success"] is False
        assert result["state_capture_status"] == "no_position"
        assert "state_id" not in result
        assert cps_called["called"] is False


# ---------------------------------------------------------------------------
# Wrapper forwarding
# ---------------------------------------------------------------------------


class TestRocqCompileFileWrapper:
    """The server wrapper should forward ctx.lifespan_context."""

    pytestmark = []

    def test_ctx_forwarded(self, monkeypatch, tmp_path):
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        captured = {}

        async def mock_run_compile_file_with_state(
            file,
            workspace,
            timeout,
            include_warnings,
            lifespan_state=None,
        ):
            captured.update(
                {
                    "file": file,
                    "workspace": workspace,
                    "timeout": timeout,
                    "include_warnings": include_warnings,
                    "lifespan_state": lifespan_state,
                }
            )
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        monkeypatch.setattr(
            _server,
            "run_compile_file_with_state",
            mock_run_compile_file_with_state,
        )

        mock_ctx = _MockContext({"pet_client": None})

        result = asyncio.run(
            rocq_compile_file(
                file="proof.v",
                workspace=str(tmp_path),
                timeout=9,
                include_warnings=False,
                ctx=mock_ctx,
            )
        )

        assert result["success"] is True
        assert captured["file"] == "proof.v"
        assert captured["workspace"] == str(tmp_path)
        assert captured["timeout"] == 9
        assert captured["include_warnings"] is False
        assert captured["lifespan_state"] is mock_ctx.lifespan_context
