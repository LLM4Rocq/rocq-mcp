"""Unit tests for server.py helpers (NO coqc needed).

TestFormatError: error formatting, annotation, truncation
TestParseCoqcErrorPositions: structured error position parsing
TestValidateWorkspace: workspace containment + existence checks
"""

from __future__ import annotations

import os
from pathlib import Path
from unittest import mock

import pytest

from rocq_mcp.server import (
    _format_error,
    _parse_coqc_error_positions,
    _validate_workspace,
    _MAX_ERROR_LENGTH,
    _MAX_FORMAT_WARNINGS,
)


# =========================================================================
# _format_error
# =========================================================================


class TestFormatError:
    """Test _format_error formatting, annotation, and edge cases."""

    PROOF = (
        "Theorem t : True.\n"  # line 1
        "Proof.\n"              # line 2
        "  exact I.\n"          # line 3
        "Qed.\n"                # line 4
    )

    def test_empty_string_returns_empty(self):
        assert _format_error("", self.PROOF) == ""

    def test_structured_error_with_annotation(self):
        """Standard coqc error with File/line/characters header."""
        stderr = (
            'File "/tmp/test.v", line 3, characters 2-9:\n'
            "Error: Not a proposition or a type."
        )
        result = _format_error(stderr, self.PROOF)
        # Should replace tmp path with <proof>
        assert "<proof>" in result
        assert "/tmp/test.v" not in result
        # Should include source line annotation
        assert "exact I." in result
        # Should include caret underline
        assert "^" in result
        # Should include the error message
        assert "Not a proposition or a type" in result

    def test_warnings_only_returns_empty(self):
        """Pure warnings (no Error) should return empty string."""
        stderr = (
            'File "/tmp/test.v", line 1, characters 0-10:\n'
            "Warning: Deprecated."
        )
        result = _format_error(stderr, self.PROOF)
        assert result == ""

    def test_include_warnings_false(self):
        """With include_warnings=False, warnings before the error are excluded."""
        stderr = (
            'File "/tmp/test.v", line 1, characters 0-10:\n'
            "Warning: Some deprecation.\n"
            'File "/tmp/test.v", line 3, characters 2-9:\n'
            "Error: Type mismatch."
        )
        result_with = _format_error(stderr, self.PROOF, include_warnings=True)
        result_without = _format_error(stderr, self.PROOF, include_warnings=False)
        # With warnings, both warning and error appear
        assert "deprecation" in result_with.lower()
        assert "Type mismatch" in result_with
        # Without warnings, only error appears
        assert "deprecation" not in result_without.lower()
        assert "Type mismatch" in result_without

    def test_duplicate_warnings_deduplicated(self):
        """Duplicate warnings should be collapsed."""
        warnings = ""
        for i in range(5):
            warnings += (
                f'File "/tmp/test.v", line {i+1}, characters 0-5:\n'
                "Warning: Same warning.\n"
            )
        stderr = (
            warnings
            + 'File "/tmp/test.v", line 3, characters 2-9:\n'
            + "Error: Fail."
        )
        result = _format_error(stderr, self.PROOF)
        # "Same warning" should appear only once (deduplicated)
        assert result.count("Same warning") == 1

    def test_warning_cap_at_max(self):
        """At most _MAX_FORMAT_WARNINGS unique warnings are included."""
        warnings = ""
        for i in range(_MAX_FORMAT_WARNINGS + 3):
            warnings += (
                f'File "/tmp/test.v", line 1, characters 0-5:\n'
                f"Warning: Unique warning {i}.\n"
            )
        stderr = (
            warnings
            + 'File "/tmp/test.v", line 3, characters 2-9:\n'
            + "Error: Fail."
        )
        result = _format_error(stderr, self.PROOF)
        # Count unique warnings in output
        count = sum(
            1 for i in range(_MAX_FORMAT_WARNINGS + 3)
            if f"Unique warning {i}" in result
        )
        assert count == _MAX_FORMAT_WARNINGS

    def test_unstructured_error_fallback(self):
        """Non-coqc error (no File/line header) uses fallback path."""
        stderr = "coqc not found or not executable: FileNotFoundError"
        result = _format_error(stderr, self.PROOF)
        assert "coqc not found" in result

    def test_unstructured_error_path_cleaned(self):
        """Tmp file paths are replaced with <proof> in fallback."""
        stderr = 'Some error in "/tmp/foo_abc123.v": bad stuff'
        result = _format_error(stderr, self.PROOF)
        assert "<proof>" in result
        assert "/tmp/foo_abc123.v" not in result

    def test_truncation_for_long_output(self):
        """Output exceeding _MAX_ERROR_LENGTH is truncated."""
        # Create a very long error body
        long_body = "x" * (_MAX_ERROR_LENGTH + 500)
        stderr = (
            'File "/tmp/test.v", line 3, characters 2-9:\n'
            f"Error: {long_body}"
        )
        result = _format_error(stderr, self.PROOF)
        assert len(result) <= _MAX_ERROR_LENGTH

    def test_unstructured_truncation(self):
        """Unstructured fallback also truncates."""
        long_stderr = "x" * (_MAX_ERROR_LENGTH + 500)
        result = _format_error(long_stderr, self.PROOF)
        assert len(result) <= _MAX_ERROR_LENGTH

    def test_out_of_range_line_number(self):
        """Line number beyond proof lines should not crash."""
        stderr = (
            'File "/tmp/test.v", line 999, characters 0-5:\n'
            "Error: Something."
        )
        result = _format_error(stderr, self.PROOF)
        assert "Something" in result
        # No source annotation since line 999 doesn't exist
        assert "999" in result

    def test_caret_length_is_at_least_one(self):
        """Even for zero-length char range, at least one caret."""
        stderr = (
            'File "/tmp/test.v", line 1, characters 5-5:\n'
            "Error: Empty range."
        )
        result = _format_error(stderr, self.PROOF)
        assert "^" in result


# =========================================================================
# _parse_coqc_error_positions
# =========================================================================


class TestParseCoqcErrorPositions:
    """Test structured error position parsing from coqc stderr."""

    def test_single_error(self):
        stderr = (
            'File "/tmp/test.v", line 3, characters 2-9:\n'
            "Error: Not a proposition."
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        p = positions[0]
        assert p["line"] == 2  # 0-based (coqc line 3 -> 2)
        assert p["character"] == 2
        assert p["end_character"] == 9
        assert "Not a proposition" in p["message"]

    def test_multiple_diagnostics(self):
        stderr = (
            'File "/tmp/test.v", line 1, characters 0-10:\n'
            "Warning: Deprecated.\n"
            'File "/tmp/test.v", line 5, characters 3-7:\n'
            "Error: Type mismatch."
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 2
        assert positions[0]["line"] == 0  # line 1 -> 0
        assert positions[0]["message"].startswith("Warning:")
        assert positions[1]["line"] == 4  # line 5 -> 4
        assert positions[1]["message"].startswith("Error:")

    def test_empty_stderr(self):
        assert _parse_coqc_error_positions("") == []

    def test_no_file_header(self):
        """stderr without File/line format returns empty list."""
        assert _parse_coqc_error_positions("some random output\n") == []

    def test_message_truncated_at_500(self):
        long_msg = "Error: " + "x" * 600
        stderr = (
            f'File "/tmp/test.v", line 1, characters 0-5:\n'
            f"{long_msg}"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert len(positions[0]["message"]) <= 500


# =========================================================================
# _validate_workspace
# =========================================================================


class TestValidateWorkspace:
    """Test workspace validation: containment, existence, writability."""

    def test_valid_workspace(self, tmp_path):
        """A real writable directory should pass."""
        assert _validate_workspace(str(tmp_path)) is None

    def test_nonexistent_directory(self, tmp_path):
        bad = tmp_path / "nonexistent"
        result = _validate_workspace(str(bad))
        assert result is not None
        assert "does not exist" in result

    def test_not_writable(self, tmp_path):
        """A non-writable directory should be rejected."""
        ro_dir = tmp_path / "readonly"
        ro_dir.mkdir()
        ro_dir.chmod(0o444)
        try:
            result = _validate_workspace(str(ro_dir))
            assert result is not None
            assert "not writable" in result
        finally:
            ro_dir.chmod(0o755)

    def test_containment_enforced_when_explicit(self, tmp_path):
        """When ROCQ_WORKSPACE is explicitly set, workspace must be within it."""
        root = tmp_path / "root"
        root.mkdir()
        outside = tmp_path / "outside"
        outside.mkdir()

        with mock.patch("rocq_mcp.server._ROCQ_WORKSPACE_EXPLICIT", True), \
             mock.patch("rocq_mcp.server.ROCQ_WORKSPACE", str(root)):
            # Inside root: OK
            assert _validate_workspace(str(root)) is None

            # Subdirectory of root: OK
            sub = root / "sub"
            sub.mkdir()
            assert _validate_workspace(str(sub)) is None

            # Outside root: rejected
            result = _validate_workspace(str(outside))
            assert result is not None
            assert "must be within" in result

    def test_containment_not_enforced_when_not_explicit(self, tmp_path):
        """When ROCQ_WORKSPACE is not explicitly set, containment is not checked."""
        with mock.patch("rocq_mcp.server._ROCQ_WORKSPACE_EXPLICIT", False):
            assert _validate_workspace(str(tmp_path)) is None
