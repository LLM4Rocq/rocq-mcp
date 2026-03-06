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

pytestmark = pytest.mark.skipif(
    not COQC_AVAILABLE, reason="coqc not available"
)


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
        result = rocq_compile(
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
        source = (
            "Theorem bad : nat = bool.\n"
            "Proof. reflexivity. Qed.\n"
        )
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
        source = (
            "Theorem test : forall x : R, x = x.\n"
            "Proof. reflexivity. Qed.\n"
        )
        result = rocq_compile(source=source, workspace=str(workspace))
        assert result["success"] is False
        assert "error" in result


# ---------------------------------------------------------------------------
# Timeout
# ---------------------------------------------------------------------------

class TestCompileTimeout:
    """Diverging tactics should trigger timeout."""

    def test_diverging_tactic(self, workspace, timeout_proof):
        result = rocq_compile(
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
        result = rocq_compile(source="", workspace="/nonexistent/path/xyz")
        assert result["success"] is False
        assert (
            "not exist" in result["error"].lower()
            or "not found" in result["error"].lower()
            or "does not exist" in result["error"].lower()
        )

    def test_oversized_source(self, workspace):
        """Source exceeding ROCQ_MAX_SOURCE_SIZE should be rejected early."""
        result = rocq_compile(
            source="x" * 2_000_000, workspace=str(workspace)
        )
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
        rocq_compile(
            source=timeout_proof, workspace=str(workspace), timeout=3
        )
        after = set(glob_mod.glob(str(workspace / "*")))
        assert before == after, f"Leftover artifacts: {after - before}"
