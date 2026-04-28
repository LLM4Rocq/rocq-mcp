"""Tests for the rocq_compile tool.

Tests are grouped into:
- TestCompileSuccess: valid Rocq sources that should compile cleanly
- TestCompileErrors: sources with type errors, syntax errors, missing imports
- TestCompileTimeout: diverging tactic with a short timeout
- TestCompileInputValidation: bad workspace, oversized source, coqc not on PATH
- TestCompileCleanup: verify no artifacts are left after compilation
"""

from __future__ import annotations

import asyncio
import glob as glob_mod
from unittest.mock import MagicMock

import pytest

from tests.conftest import COQC_AVAILABLE
from rocq_mcp.server import rocq_compile

pytestmark = pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")


def _call_rocq_compile(**kwargs):
    """Run the async server wrapper from synchronous tests."""
    return asyncio.run(rocq_compile(**kwargs))


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------


class TestCompileSuccess:
    """Sources that compile without error."""

    def test_simple_proof(self, workspace, simple_proof):
        result = _call_rocq_compile(source=simple_proof, workspace=str(workspace))
        assert result["success"] is True

    def test_empty_source(self, workspace):
        """An empty file is valid Rocq source."""
        result = _call_rocq_compile(source="", workspace=str(workspace))
        assert result["success"] is True

    def test_braces_in_proof(self, workspace, braces_proof):
        """Proofs using { } subgoal braces must not confuse f-string templates."""
        result = _call_rocq_compile(source=braces_proof, workspace=str(workspace))
        assert result["success"] is True

    def test_multiline_import(self, workspace, multiline_import_proof):
        """Multi-line From ... Require Import must compile correctly."""
        result = _call_rocq_compile(
            source=multiline_import_proof, workspace=str(workspace)
        )
        assert result["success"] is True


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------


class TestCompileErrors:
    """Sources that should fail compilation with a clear error."""

    def test_type_error(self, workspace):
        """A proof of an obviously false statement must fail."""
        source = "Theorem bad : nat = bool.\n" "Proof. reflexivity. Qed.\n"
        result = _call_rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result
        assert len(result["error"]) > 0

    def test_syntax_error(self, workspace):
        """Malformed syntax should produce a compilation error."""
        source = "Theorem bad : .\nQed.\n"
        result = _call_rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result

    def test_missing_import(self, workspace):
        """Using R without importing Reals should fail."""
        source = "Theorem test : forall x : R, x = x.\n" "Proof. reflexivity. Qed.\n"
        result = _call_rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result


# ---------------------------------------------------------------------------
# Timeout
# ---------------------------------------------------------------------------


class TestCompileTimeout:
    """Diverging tactics should trigger timeout."""

    def test_diverging_tactic(self, workspace, timeout_proof):
        result = _call_rocq_compile(
            source=timeout_proof, workspace=str(workspace), timeout=3
        )
        assert result["success"] is False
        assert "timed out" in result["error"].lower()


# ---------------------------------------------------------------------------
# Input validation
# ---------------------------------------------------------------------------


class TestCompileInputValidation:
    """Edge cases around bad inputs (no coqc needed for some of these)."""

    def test_bad_workspace(self):
        """Non-existent workspace should return a clear error."""
        result = _call_rocq_compile(source="", workspace="/nonexistent/path/xyz")
        assert result["success"] is False
        assert (
            "not exist" in result["error"].lower()
            or "not found" in result["error"].lower()
            or "does not exist" in result["error"].lower()
        )

    def test_oversized_source(self, workspace):
        """Source exceeding ROCQ_MAX_SOURCE_SIZE should be rejected early."""
        result = _call_rocq_compile(source="x" * 2_000_000, workspace=str(workspace))
        assert result["success"] is False
        assert "size" in result["error"].lower()

    def test_coqc_not_on_path(self, workspace, monkeypatch):
        """When ROCQ_COQC_BINARY points to a non-existent binary, report error."""
        monkeypatch.setattr(
            "rocq_mcp.server.ROCQ_COQC_BINARY", "nonexistent_coqc_binary_xyz"
        )
        result = _call_rocq_compile(source="", workspace=str(workspace))
        assert result["success"] is False
        assert "not found" in result["error"].lower()


# ---------------------------------------------------------------------------
# Cleanup
# ---------------------------------------------------------------------------


class TestCompileCleanup:
    """Compilation should not leave temp files behind."""

    def test_no_artifacts_left(self, workspace, simple_proof):
        before = set(glob_mod.glob(str(workspace / "*")))
        _call_rocq_compile(source=simple_proof, workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_error(self, workspace):
        """Even on compilation error, temp files should be cleaned up."""
        source = "Theorem bad : .\nQed.\n"
        before = set(glob_mod.glob(str(workspace / "*")))
        _call_rocq_compile(source=source, workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_timeout(self, workspace, timeout_proof):
        """Even on timeout, temp files should be cleaned up."""
        before = set(glob_mod.glob(str(workspace / "*")))
        _call_rocq_compile(source=timeout_proof, workspace=str(workspace), timeout=3)
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"


# ---------------------------------------------------------------------------
# Regression: warnings-before-error truncation bug
# ---------------------------------------------------------------------------


class TestCompileWarningsTruncation:
    """Ensure coqc failures are detected even when stderr starts with
    voluminous warnings (e.g. math-comp coercion ambiguity notices) that
    exceed the internal _MAX_ERROR_LENGTH budget.

    Regression test for: stderr[:4000] contained only warnings → _format_error
    returned "" → rocq_compile falsely reported success despite returncode != 0.
    """

    @staticmethod
    def _make_fake_result(stderr, returncode=1):
        return {
            "returncode": returncode,
            "stdout": "",
            "stderr": stderr,
            "timed_out": False,
        }

    @staticmethod
    def _big_warnings(min_bytes=6000):
        """Generate structured warnings exceeding the given byte count."""
        warning_line = (
            'File "/tmp/tmp.v", line 2, characters 0-75:\n'
            "Warning: Notation overridden.\n"
        )
        return warning_line * (min_bytes // len(warning_line) + 1)

    def test_error_after_large_warnings_detected(self, workspace, monkeypatch):
        """When warnings exceed _MAX_ERROR_LENGTH and the error is at the end,
        rocq_compile must still report failure with the actual error content."""
        from rocq_mcp import compile as _compile

        warnings = self._big_warnings()
        error = (
            'File "/tmp/tmp.v", line 50, characters 11-41:\n'
            "Error: The LHS of map_trmx does not match any subterm of the goal\n"
        )
        fake_stderr = warnings + error
        assert len(warnings) > _compile._MAX_ERROR_LENGTH

        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(fake_stderr),
        )

        source = "Theorem t : True. Proof. exact I. Qed."
        result = _call_rocq_compile(source=source, workspace=str(workspace))

        assert (
            result["success"] is False
        ), "rocq_compile must not report success when coqc exits with code 1"
        assert (
            "map_trmx" in result["error"]
        ), "Error content must be preserved, not lost to warning truncation"

    def test_genuine_pure_warnings_still_succeed(self, workspace, monkeypatch):
        """When returncode == 0, warnings-only stderr is still success."""
        from rocq_mcp import compile as _compile

        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(
                'File "/tmp/tmp.v", line 1, characters 0-10:\nWarning: Deprecated.\n',
                returncode=0,
            ),
        )

        source = "Theorem t : True. Proof. exact I. Qed."
        result = _call_rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is True

    def test_empty_stderr_nonzero_returncode(self, workspace, monkeypatch):
        """Empty stderr with returncode != 0 must report failure, not success."""
        from rocq_mcp import compile as _compile

        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(""),
        )

        result = _call_rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "coqc exited with code" in result["error"]

    def test_whitespace_only_stderr_nonzero_returncode(self, workspace, monkeypatch):
        """Whitespace-only stderr with non-zero returncode must still fail."""
        from rocq_mcp import compile as _compile

        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result("   \n\n  "),
        )

        result = _call_rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "coqc exited with code" in result["error"]

    def test_only_warnings_nonzero_returncode(self, workspace, monkeypatch):
        """Structured warnings but no Error + returncode != 0: must fail
        with the raw warning tail as fallback (not empty error)."""
        from rocq_mcp import compile as _compile

        warnings = self._big_warnings()
        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(warnings),
        )

        result = _call_rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "Notation overridden" in result["error"]

    def test_include_warnings_false_strips_warnings(self, workspace, monkeypatch):
        """include_warnings=False must flow through to _format_error and
        exclude warnings from the error output."""
        from rocq_mcp import compile as _compile

        warn = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Warning: Something deprecated.\n"
        )
        error = (
            'File "/tmp/tmp.v", line 2, characters 0-10:\n'
            "Error: Tactic failure: Cannot find witness.\n"
        )
        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(warn + error),
        )

        result = _call_rocq_compile(
            source="x",
            workspace=str(workspace),
            include_warnings=False,
        )
        assert result["success"] is False
        assert "Tactic failure" in result["error"]
        assert "deprecated" not in result["error"]

    def test_output_bounded_many_unique_warnings(self, workspace, monkeypatch):
        """Even with many unique warnings, output must be bounded."""
        from rocq_mcp import compile as _compile

        # 50 distinct warnings + 1 error
        warnings = "".join(
            f'File "/tmp/tmp.v", line {i}, characters 0-10:\n'
            f"Warning: Unique warning number {i}.\n"
            for i in range(50)
        )
        error = (
            'File "/tmp/tmp.v", line 99, characters 0-10:\n' "Error: Real error here.\n"
        )
        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(warnings + error),
        )

        result = _call_rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "Real error here" in result["error"]
        assert len(result["error"]) <= _compile._MAX_ERROR_LENGTH


# ---------------------------------------------------------------------------
# Proof-state capture on compile errors
# ---------------------------------------------------------------------------


class TestCompileErrorStateCapture:
    """Compile errors should include rocq_start-style state when available."""

    pytestmark = []

    @staticmethod
    def _make_fake_result(stderr, returncode=1):
        return {
            "returncode": returncode,
            "stdout": "",
            "stderr": stderr,
            "timed_out": False,
        }

    def test_compile_error_includes_state_when_capture_succeeds(
        self, workspace, monkeypatch
    ):
        """Successful PET capture should enrich the compile error result."""
        from rocq_mcp import compile as _compile
        from rocq_mcp import server as _server

        stderr = (
            'File "/tmp/tmp.v", line 2, characters 2-9:\n'
            'Error: The term "0" has type "nat" while it is expected to have type "True".\n'
        )
        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(stderr),
        )

        async def _mock_capture_success(*args, **kwargs):
            return {
                "state_id": 17,
                "goals": "|- True",
                "file": "<proof>",
                "theorem": "@pos(1,2)",
                "proof_finished": False,
            }

        monkeypatch.setattr(
            _server,
            "_capture_compile_error_state",
            _mock_capture_success,
        )

        result = asyncio.run(
            _server.run_compile_with_state(
                "Theorem bad : True.\n  exact 0.\n",
                str(workspace),
                60,
                lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            )
        )

        assert result["success"] is False
        assert result["state_id"] == 17
        assert result["goals"] == "|- True"
        assert result["file"] == "<proof>"
        assert result["theorem"] == "@pos(1,2)"
        assert result["proof_finished"] is False
        assert "rocq_check(from_state=17)" in result["hint"]

    def test_warning_before_error_uses_error_position(self, workspace, monkeypatch):
        """State capture must target the first Error, not a preceding Warning."""
        from rocq_mcp import compile as _compile
        from rocq_mcp import server as _server

        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Warning: Deprecated.\n"
            'File "/tmp/tmp.v", line 5, characters 3-11:\n'
            "Error: Real failure.\n"
        )
        captured = {}

        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(stderr),
        )

        async def _mock_capture(*args, **kwargs):
            captured.update(kwargs)
            return None

        monkeypatch.setattr(_server, "_capture_compile_error_state", _mock_capture)

        asyncio.run(
            _server.run_compile_with_state(
                "x",
                str(workspace),
                60,
                lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            )
        )

        assert captured["line"] == 4
        assert captured["character"] == 3

    def test_capture_failure_preserves_existing_hint(self, workspace, monkeypatch):
        """Failed PET capture should fall back to the original compile guidance."""
        from rocq_mcp import compile as _compile
        from rocq_mcp import server as _server

        stderr = 'File "/tmp/tmp.v", line 2, characters 0-5:\n' "Error: Real failure.\n"
        monkeypatch.setattr(
            _compile,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(stderr),
        )

        async def _mock_capture_none(*args, **kwargs):
            return None

        monkeypatch.setattr(_server, "_capture_compile_error_state", _mock_capture_none)

        result = asyncio.run(
            _server.run_compile_with_state(
                "x",
                str(workspace),
                60,
                lifespan_state={"pet_client": None, "pet_timeout": 30.0},
            )
        )

        assert result["success"] is False
        assert "state_id" not in result
        assert "Use rocq_start" in result["hint"]


# ---------------------------------------------------------------------------
# Wrapper forwarding
# ---------------------------------------------------------------------------


class TestRocqCompileWrapper:
    """The server wrapper should forward ctx.lifespan_context."""

    pytestmark = []

    def test_ctx_forwarded(self, monkeypatch, tmp_path):
        import rocq_mcp.server as _server

        captured = {}

        async def mock_run_compile_with_state(
            source,
            workspace,
            timeout,
            include_warnings,
            lifespan_state=None,
        ):
            captured.update(
                {
                    "source": source,
                    "workspace": workspace,
                    "timeout": timeout,
                    "include_warnings": include_warnings,
                    "lifespan_state": lifespan_state,
                }
            )
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        monkeypatch.setattr(
            _server, "run_compile_with_state", mock_run_compile_with_state
        )

        mock_ctx = MagicMock()
        mock_ctx.lifespan_context = {"pet_client": None}

        result = _call_rocq_compile(
            source="Check nat.",
            workspace=str(tmp_path),
            timeout=7,
            include_warnings=False,
            ctx=mock_ctx,
        )

        assert result["success"] is True
        assert captured["source"] == "Check nat."
        assert captured["workspace"] == str(tmp_path)
        assert captured["timeout"] == 7
        assert captured["include_warnings"] is False
        assert captured["lifespan_state"] is mock_ctx.lifespan_context
