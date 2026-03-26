"""Unit tests for server.py helpers (NO coqc needed).

TestFormatError: error formatting, annotation, truncation
TestParseCoqcErrorPositions: structured error position parsing
TestValidateWorkspace: workspace containment + existence checks
TestParseProjectFlags: _RocqProject / _CoqProject parsing
"""

from __future__ import annotations

import os
from pathlib import Path
from unittest import mock

import pytest

from rocq_mcp.server import (
    _format_error,
    _parse_coqc_error_positions,
    _parse_project_flags,
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
        "Proof.\n"  # line 2
        "  exact I.\n"  # line 3
        "Qed.\n"  # line 4
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
        stderr = 'File "/tmp/test.v", line 1, characters 0-10:\n' "Warning: Deprecated."
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
            warnings + 'File "/tmp/test.v", line 3, characters 2-9:\n' + "Error: Fail."
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
            warnings + 'File "/tmp/test.v", line 3, characters 2-9:\n' + "Error: Fail."
        )
        result = _format_error(stderr, self.PROOF)
        # Count unique warnings in output
        count = sum(
            1
            for i in range(_MAX_FORMAT_WARNINGS + 3)
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
        stderr = 'File "/tmp/test.v", line 3, characters 2-9:\n' f"Error: {long_body}"
        result = _format_error(stderr, self.PROOF)
        assert len(result) <= _MAX_ERROR_LENGTH

    def test_unstructured_truncation(self):
        """Unstructured fallback also truncates."""
        long_stderr = "x" * (_MAX_ERROR_LENGTH + 500)
        result = _format_error(long_stderr, self.PROOF)
        assert len(result) <= _MAX_ERROR_LENGTH

    def test_out_of_range_line_number(self):
        """Line number beyond proof lines should not crash."""
        stderr = 'File "/tmp/test.v", line 999, characters 0-5:\n' "Error: Something."
        result = _format_error(stderr, self.PROOF)
        assert "Something" in result
        # No source annotation since line 999 doesn't exist
        assert "999" in result

    def test_caret_length_is_at_least_one(self):
        """Even for zero-length char range, at least one caret."""
        stderr = 'File "/tmp/test.v", line 1, characters 5-5:\n' "Error: Empty range."
        result = _format_error(stderr, self.PROOF)
        assert "^" in result


# =========================================================================
# _parse_coqc_error_positions
# =========================================================================


class TestParseCoqcErrorPositions:
    """Test structured error position parsing from coqc stderr."""

    def test_single_error(self):
        stderr = (
            'File "/tmp/test.v", line 3, characters 2-9:\n' "Error: Not a proposition."
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
        stderr = f'File "/tmp/test.v", line 1, characters 0-5:\n' f"{long_msg}"
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

        with (
            mock.patch("rocq_mcp.server._ROCQ_WORKSPACE_EXPLICIT", True),
            mock.patch("rocq_mcp.server.ROCQ_WORKSPACE", str(root)),
        ):
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


# =========================================================================
# _parse_project_flags
# =========================================================================


class TestParseProjectFlags:
    """Test _RocqProject / _CoqProject parsing."""

    def test_no_project_file_fallback(self, tmp_path):
        """Without a project file, fall back to -Q <ws> Test."""
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", str(tmp_path), "Test"]

    def test_coqproject_q_flag(self, tmp_path):
        """_CoqProject with -Q is parsed correctly."""
        (tmp_path / "_CoqProject").write_text("-Q . MyProject\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "MyProject"]

    def test_coqproject_r_flag(self, tmp_path):
        """_CoqProject with -R is parsed correctly."""
        (tmp_path / "_CoqProject").write_text("-R theories MyLib\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-R", "theories", "MyLib"]

    def test_coqproject_i_flag(self, tmp_path):
        """_CoqProject with -I is parsed correctly."""
        (tmp_path / "_CoqProject").write_text("-I src\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-I", "src"]

    def test_rocqproject_takes_priority(self, tmp_path):
        """_RocqProject takes priority over _CoqProject."""
        (tmp_path / "_CoqProject").write_text("-Q . Old\n")
        (tmp_path / "_RocqProject").write_text("-Q . New\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "New"]

    def test_arg_same_line(self, tmp_path):
        """-arg value on same line."""
        (tmp_path / "_CoqProject").write_text("-arg -noinit\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-noinit"]

    def test_arg_next_line(self, tmp_path):
        """-arg on one line, value on next."""
        (tmp_path / "_CoqProject").write_text("-arg\n-noinit\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-noinit"]

    def test_comments_and_blanks_ignored(self, tmp_path):
        """Comments (#) and blank lines are skipped."""
        (tmp_path / "_CoqProject").write_text(
            "# This is a comment\n" "\n" "-Q . MyProject\n" "# Another comment\n"
        )
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "MyProject"]

    def test_v_files_ignored(self, tmp_path):
        """.v file entries are silently skipped."""
        (tmp_path / "_CoqProject").write_text(
            "-Q . MyProject\n" "src/Foo.v\n" "src/Bar.v\n"
        )
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "MyProject"]

    def test_multiple_flags(self, tmp_path):
        """Multiple flags are all collected."""
        (tmp_path / "_CoqProject").write_text(
            "-R . MyLib\n" "-Q extra Extra\n" "-I plugins\n"
        )
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-R", ".", "MyLib", "-Q", "extra", "Extra", "-I", "plugins"]

    def test_empty_project_file(self, tmp_path):
        """Empty project file produces no flags."""
        (tmp_path / "_CoqProject").write_text("")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    # --- Security: -arg allowlist ---

    def test_arg_dangerous_load_rejected(self, tmp_path):
        """-arg -load-vernac-source must be silently dropped."""
        (tmp_path / "_CoqProject").write_text(
            "-Q . Safe\n" "-arg -load-vernac-source\n"
        )
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "Safe"]
        assert "-load-vernac-source" not in flags

    def test_arg_dangerous_output_dir_rejected(self, tmp_path):
        """-arg -output-directory must be silently dropped."""
        (tmp_path / "_CoqProject").write_text("-arg -output-directory\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_arg_dangerous_init_file_rejected(self, tmp_path):
        """-arg -init-file must be silently dropped."""
        (tmp_path / "_CoqProject").write_text("-arg -init-file\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_arg_safe_noinit_allowed(self, tmp_path):
        """-arg -noinit is in the allowlist."""
        (tmp_path / "_CoqProject").write_text("-arg -noinit\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-noinit"]

    def test_arg_safe_warning_allowed(self, tmp_path):
        """-arg -w <warning> is split into two separate coqc arguments."""
        (tmp_path / "_CoqProject").write_text("-arg -w -notation-overridden\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-w", "-notation-overridden"]

    def test_arg_unknown_rejected(self, tmp_path):
        """Unknown -arg values are silently dropped."""
        (tmp_path / "_CoqProject").write_text("-arg -some-unknown-flag\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_arg_next_line_dangerous_rejected(self, tmp_path):
        """-arg (next-line form) with dangerous value must be dropped."""
        (tmp_path / "_CoqProject").write_text("-arg\n-load-vernac-source\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    # --- Security: path containment ---

    def test_q_absolute_path_rejected(self, tmp_path):
        """-Q with absolute path must be silently dropped."""
        (tmp_path / "_CoqProject").write_text("-Q /etc Evil\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_r_path_traversal_rejected(self, tmp_path):
        """-R with ../ path escape must be silently dropped."""
        (tmp_path / "_CoqProject").write_text("-R ../../evil Evil\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_i_absolute_path_rejected(self, tmp_path):
        """-I with absolute path must be silently dropped."""
        (tmp_path / "_CoqProject").write_text("-I /usr/lib\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_q_subdir_allowed(self, tmp_path):
        """-Q with a subdirectory path is allowed."""
        (tmp_path / "_CoqProject").write_text("-Q theories MyLib\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", "theories", "MyLib"]

    # --- Parsing edge cases ---

    def test_q_malformed_missing_name_dropped(self, tmp_path):
        """-Q with missing logical name is silently dropped."""
        (tmp_path / "_CoqProject").write_text("-Q .\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []

    def test_arg_dangling_at_eof(self, tmp_path):
        """-arg as the last line with no value is silently dropped."""
        (tmp_path / "_CoqProject").write_text("-arg\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == []
