"""Tests for the rocq_compile tool.

Tests are grouped into:
- TestCompileSuccess: valid Rocq sources that should compile cleanly
- TestCompileErrors: sources with type errors, syntax errors, missing imports
- TestCompileTimeout: diverging tactic with a short timeout
- TestCompileInputValidation: bad workspace, oversized source, coqc not on PATH
- TestCompileCleanup: verify no artifacts are left after compilation
"""

from __future__ import annotations

import glob as glob_mod

import pytest

from tests.conftest import COQC_AVAILABLE
from rocq_mcp.server import rocq_compile

pytestmark = pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------


class TestCompileSuccess:
    """Sources that compile without error."""

    def test_simple_proof(self, workspace, simple_proof):
        result = rocq_compile(source=simple_proof, workspace=str(workspace))
        assert result["success"] is True

    def test_empty_source(self, workspace):
        """An empty file is valid Rocq source."""
        result = rocq_compile(source="", workspace=str(workspace))
        assert result["success"] is True

    def test_braces_in_proof(self, workspace, braces_proof):
        """Proofs using { } subgoal braces must not confuse f-string templates."""
        result = rocq_compile(source=braces_proof, workspace=str(workspace))
        assert result["success"] is True

    def test_multiline_import(self, workspace, multiline_import_proof):
        """Multi-line From ... Require Import must compile correctly."""
        result = rocq_compile(source=multiline_import_proof, workspace=str(workspace))
        assert result["success"] is True


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------


class TestCompileErrors:
    """Sources that should fail compilation with a clear error."""

    def test_type_error(self, workspace):
        """A proof of an obviously false statement must fail."""
        source = "Theorem bad : nat = bool.\n" "Proof. reflexivity. Qed.\n"
        result = rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result
        assert len(result["error"]) > 0

    def test_syntax_error(self, workspace):
        """Malformed syntax should produce a compilation error."""
        source = "Theorem bad : .\nQed.\n"
        result = rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result

    def test_missing_import(self, workspace):
        """Using R without importing Reals should fail."""
        source = "Theorem test : forall x : R, x = x.\n" "Proof. reflexivity. Qed.\n"
        result = rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result


# ---------------------------------------------------------------------------
# Timeout
# ---------------------------------------------------------------------------


class TestCompileTimeout:
    """Diverging tactics should trigger timeout."""

    def test_diverging_tactic(self, workspace, timeout_proof):
        result = rocq_compile(source=timeout_proof, workspace=str(workspace), timeout=3)
        assert result["success"] is False
        assert "timed out" in result["error"].lower()


# ---------------------------------------------------------------------------
# Input validation
# ---------------------------------------------------------------------------


class TestCompileInputValidation:
    """Edge cases around bad inputs (no coqc needed for some of these)."""

    def test_bad_workspace(self):
        """Non-existent workspace should return a clear error."""
        result = rocq_compile(source="", workspace="/nonexistent/path/xyz")
        assert result["success"] is False
        assert (
            "not exist" in result["error"].lower()
            or "not found" in result["error"].lower()
            or "does not exist" in result["error"].lower()
        )

    def test_oversized_source(self, workspace):
        """Source exceeding ROCQ_MAX_SOURCE_SIZE should be rejected early."""
        result = rocq_compile(source="x" * 2_000_000, workspace=str(workspace))
        assert result["success"] is False
        assert "size" in result["error"].lower()

    def test_coqc_not_on_path(self, workspace, monkeypatch):
        """When ROCQ_COQC_BINARY points to a non-existent binary, report error."""
        monkeypatch.setattr(
            "rocq_mcp.server.ROCQ_COQC_BINARY", "nonexistent_coqc_binary_xyz"
        )
        result = rocq_compile(source="", workspace=str(workspace))
        assert result["success"] is False
        assert "not found" in result["error"].lower()


# ---------------------------------------------------------------------------
# Cleanup
# ---------------------------------------------------------------------------


class TestCompileCleanup:
    """Compilation should not leave temp files behind."""

    def test_no_artifacts_left(self, workspace, simple_proof):
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_compile(source=simple_proof, workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_error(self, workspace):
        """Even on compilation error, temp files should be cleaned up."""
        source = "Theorem bad : .\nQed.\n"
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_compile(source=source, workspace=str(workspace))
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"

    def test_no_artifacts_on_timeout(self, workspace, timeout_proof):
        """Even on timeout, temp files should be cleaned up."""
        before = set(glob_mod.glob(str(workspace / "*")))
        rocq_compile(source=timeout_proof, workspace=str(workspace), timeout=3)
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
        from rocq_mcp import server

        warnings = self._big_warnings()
        error = (
            'File "/tmp/tmp.v", line 50, characters 11-41:\n'
            "Error: The LHS of map_trmx does not match any subterm of the goal\n"
        )
        fake_stderr = warnings + error
        assert len(warnings) > server._MAX_ERROR_LENGTH

        monkeypatch.setattr(
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(fake_stderr),
        )

        source = "Theorem t : True. Proof. exact I. Qed."
        result = rocq_compile(source=source, workspace=str(workspace))

        assert (
            result["success"] is False
        ), "rocq_compile must not report success when coqc exits with code 1"
        assert (
            "map_trmx" in result["error"]
        ), "Error content must be preserved, not lost to warning truncation"

    def test_genuine_pure_warnings_still_succeed(self, workspace, monkeypatch):
        """When returncode == 0, warnings-only stderr is still success."""
        from rocq_mcp import server

        monkeypatch.setattr(
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(
                'File "/tmp/tmp.v", line 1, characters 0-10:\nWarning: Deprecated.\n',
                returncode=0,
            ),
        )

        source = "Theorem t : True. Proof. exact I. Qed."
        result = rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is True

    def test_empty_stderr_nonzero_returncode(self, workspace, monkeypatch):
        """Empty stderr with returncode != 0 must report failure, not success."""
        from rocq_mcp import server

        monkeypatch.setattr(
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(""),
        )

        result = rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "coqc exited with code" in result["error"]

    def test_whitespace_only_stderr_nonzero_returncode(self, workspace, monkeypatch):
        """Whitespace-only stderr with non-zero returncode must still fail."""
        from rocq_mcp import server

        monkeypatch.setattr(
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result("   \n\n  "),
        )

        result = rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "coqc exited with code" in result["error"]

    def test_only_warnings_nonzero_returncode(self, workspace, monkeypatch):
        """Structured warnings but no Error + returncode != 0: must fail
        with the raw warning tail as fallback (not empty error)."""
        from rocq_mcp import server

        warnings = self._big_warnings()
        monkeypatch.setattr(
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(warnings),
        )

        result = rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "Notation overridden" in result["error"]

    def test_include_warnings_false_strips_warnings(self, workspace, monkeypatch):
        """include_warnings=False must flow through to _format_error and
        exclude warnings from the error output."""
        from rocq_mcp import server

        warn = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Warning: Something deprecated.\n"
        )
        error = (
            'File "/tmp/tmp.v", line 2, characters 0-10:\n'
            "Error: Tactic failure: Cannot find witness.\n"
        )
        monkeypatch.setattr(
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(warn + error),
        )

        result = rocq_compile(
            source="x",
            workspace=str(workspace),
            include_warnings=False,
        )
        assert result["success"] is False
        assert "Tactic failure" in result["error"]
        assert "deprecated" not in result["error"]

    def test_output_bounded_many_unique_warnings(self, workspace, monkeypatch):
        """Even with many unique warnings, output must be bounded."""
        from rocq_mcp import server

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
            server,
            "_run_coqc",
            lambda *a, **kw: self._make_fake_result(warnings + error),
        )

        result = rocq_compile(source="x", workspace=str(workspace))
        assert result["success"] is False
        assert "Real error here" in result["error"]
        assert len(result["error"]) <= server._MAX_ERROR_LENGTH
