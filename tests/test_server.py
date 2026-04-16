"""Unit tests for server.py helpers (NO coqc needed).

TestFormatError: error formatting, annotation, truncation
TestParseCoqcErrorPositions: structured error position parsing
TestValidateWorkspace: workspace containment + existence checks
TestParseProjectFlags: _RocqProject / _CoqProject parsing
TestParseDuneFlags: dune project detection via dune coq top
TestForceReleasePetLock: _force_release_pet_lock deadlock recovery
TestReconstructTacticPath: state table chain walk + completeness flag
TestFormatGoals: goal formatting, truncation by count and length
TestRunCheckBodySizeLimit: run_check body size rejection
TestStateTableEviction: eviction logic + expired/nonexistent error messages
TestPetInvalidationHooks: invalidation hooks clear state table + import cache
TestRunCheckBodyWithinLimit: run_check body within size limit passes check
TestKillPet: _kill_pet process termination (signals, escalation, FD cleanup)
TestEnsurePetHooks: _ensure_pet invalidation hooks on dead pet detection
TestRunWithPetExceptionHandling: _run_with_pet PetanqueError/BrokenPipe/FileNotFound paths
TestFormatGoalsDefField: _format_goals hypothesis def_ field rendering
"""

from __future__ import annotations

import asyncio
import os
import threading
import time
from pathlib import Path
from unittest import mock

import pytest

from rocq_mcp.server import (
    _force_release_pet_lock,
    _merge_partial_state,
    _parse_dune_flags,
    _parse_project_flags,
    _PetLockTimeout,
    _run_with_pet,
    _validate_workspace,
)
from rocq_mcp.compile import (
    _format_error,
    _parse_coqc_error_positions,
    _MAX_ERROR_LENGTH,
    _MAX_FORMAT_WARNINGS,
)
from rocq_mcp.interactive import _format_goals

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

    # --- .mcp-workspace/ directory support ---

    def test_mcp_workspace_coqproject_preferred(self, tmp_path):
        """.mcp-workspace/_CoqProject is preferred over root _CoqProject."""
        (tmp_path / "_CoqProject").write_text("-Q . RootProject\n")
        mcp_ws = tmp_path / ".mcp-workspace"
        mcp_ws.mkdir()
        (mcp_ws / "_CoqProject").write_text("-Q . McpProject\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "McpProject"]

    def test_mcp_workspace_rocqproject_preferred(self, tmp_path):
        """.mcp-workspace/_RocqProject is preferred over root _RocqProject."""
        (tmp_path / "_RocqProject").write_text("-Q . RootProject\n")
        mcp_ws = tmp_path / ".mcp-workspace"
        mcp_ws.mkdir()
        (mcp_ws / "_RocqProject").write_text("-Q . McpProject\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "McpProject"]

    def test_mcp_workspace_missing_falls_back(self, tmp_path):
        """Without .mcp-workspace/, falls back to root _CoqProject."""
        (tmp_path / "_CoqProject").write_text("-Q . RootProject\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "RootProject"]

    def test_mcp_workspace_empty_falls_back(self, tmp_path):
        """.mcp-workspace/ exists but has no project file -> root _CoqProject."""
        (tmp_path / "_CoqProject").write_text("-Q . RootProject\n")
        mcp_ws = tmp_path / ".mcp-workspace"
        mcp_ws.mkdir()
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "RootProject"]

    def test_mcp_workspace_rocqproject_over_root_coqproject(self, tmp_path):
        """.mcp-workspace/_RocqProject beats root _CoqProject."""
        (tmp_path / "_CoqProject").write_text("-Q . RootCoq\n")
        mcp_ws = tmp_path / ".mcp-workspace"
        mcp_ws.mkdir()
        (mcp_ws / "_RocqProject").write_text("-Q . McpRocq\n")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "McpRocq"]


# =========================================================================
# _parse_dune_flags — dune project detection
# =========================================================================


class TestParseDuneFlags:
    """Test dune project flag extraction via ``dune coq top``."""

    def test_no_dune_project_returns_none(self, tmp_path):
        """Without dune-project, returns None."""
        assert _parse_dune_flags(tmp_path) is None

    def test_dune_project_but_no_v_files_returns_none(self, tmp_path):
        """dune-project exists but no .v files — returns None."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        assert _parse_dune_flags(tmp_path) is None

    def test_dune_flags_parsed_from_subprocess(self, tmp_path):
        """Successful dune coq top output is parsed into flags."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R _build/default/mylib mylib -Q . Test"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        assert flags == ["-R", "_build/default/mylib", "mylib", "-Q", ".", "Test"]
        # Verify _RocqProject was written for coq-lsp.
        proj = tmp_path / "_RocqProject"
        assert proj.is_file()
        content = proj.read_text()
        assert content.startswith("# Auto-generated by rocq-mcp from dune\n")
        assert "-R _build/default/mylib mylib" in content
        assert "-Q . Test" in content

    def test_dune_flags_include_w(self, tmp_path):
        """-w flags from dune are preserved."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R . mylib -w -notation-overridden"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        assert "-w" in flags
        assert "-notation-overridden" in flags

    def test_dune_flags_include_noinit(self, tmp_path):
        """-noinit from dune is preserved."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-noinit -R . mylib"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        assert flags == ["-noinit", "-R", ".", "mylib"]

    def test_dune_path_traversal_rejected(self, tmp_path):
        """Paths escaping the workspace are dropped."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R ../../escape evil -Q . Safe"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        # Escaped path dropped, safe path kept.
        assert flags == ["-Q", ".", "Safe"]

    def test_dune_absolute_path_outside_root_rejected(self, tmp_path):
        """Absolute paths outside the dune project root are dropped."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R /etc/evil evil -Q . Safe"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        assert flags == ["-Q", ".", "Safe"]

    def test_dune_absolute_path_in_root_converted_to_relative(self, tmp_path):
        """Absolute paths within the dune root are accepted and made relative."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        subdir = tmp_path / "src"
        subdir.mkdir()
        (subdir / "test.v").write_text("")
        build_dir = tmp_path / "_build" / "default" / "mylib"
        build_dir.mkdir(parents=True)
        abs_path = str(build_dir.resolve())
        fake_output = f"-R {abs_path} mylib"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(subdir)
        # Absolute path converted to relative from ws (subdir).
        assert flags == [
            "-R",
            os.path.join("..", "_build", "default", "mylib"),
            "mylib",
        ]

    def test_dune_does_not_overwrite_user_project_file(self, tmp_path):
        """Existing _RocqProject in ws is not overwritten."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "_RocqProject").write_text("-Q . UserProject\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R . mylib"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        # Flags are returned but _RocqProject is untouched.
        assert flags == ["-R", ".", "mylib"]
        assert (tmp_path / "_RocqProject").read_text() == "-Q . UserProject\n"

    def test_dune_not_installed_returns_none(self, tmp_path):
        """If dune is not installed, returns None gracefully."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        with mock.patch(
            "rocq_mcp.server.subprocess.run", side_effect=FileNotFoundError
        ):
            assert _parse_dune_flags(tmp_path) is None

    def test_dune_timeout_returns_none(self, tmp_path):
        """If dune times out, returns None gracefully."""
        import subprocess as sp

        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        with mock.patch(
            "rocq_mcp.server.subprocess.run", side_effect=sp.TimeoutExpired("dune", 10)
        ):
            assert _parse_dune_flags(tmp_path) is None

    def test_dune_nonzero_exit_returns_none(self, tmp_path):
        """If dune exits non-zero, returns None."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=1, stdout="", stderr="error")
            assert _parse_dune_flags(tmp_path) is None

    def test_dune_empty_output_returns_none(self, tmp_path):
        """If dune outputs nothing useful, returns None."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout="")
            assert _parse_dune_flags(tmp_path) is None

    def test_dune_project_in_parent_detected(self, tmp_path):
        """dune-project in a parent directory is detected."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        subdir = tmp_path / "src"
        subdir.mkdir()
        (subdir / "test.v").write_text("")
        fake_output = "-R . mylib"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(subdir)
        assert flags == ["-R", ".", "mylib"]

    def test_parse_project_flags_dune_fallback(self, tmp_path):
        """_parse_project_flags falls through to dune when no project file."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R _build/default/mylib mylib"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_project_flags(tmp_path)
        assert flags == ["-R", "_build/default/mylib", "mylib"]

    def test_coqproject_takes_precedence_over_dune(self, tmp_path):
        """_CoqProject is preferred even when dune-project exists."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "_CoqProject").write_text("-Q . FromCoqProject\n")
        (tmp_path / "test.v").write_text("")
        flags = _parse_project_flags(tmp_path)
        assert flags == ["-Q", ".", "FromCoqProject"]

    def test_generated_rocqproject_reused_on_second_call(self, tmp_path):
        """Previously generated _RocqProject is reused without calling dune."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-R _build/default/mylib mylib"
        # First call: generates _RocqProject via dune.
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags1 = _parse_project_flags(tmp_path)
        assert flags1 == ["-R", "_build/default/mylib", "mylib"]
        assert (tmp_path / "_RocqProject").is_file()
        # Second call: _RocqProject exists, dune is NOT called.
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            flags2 = _parse_project_flags(tmp_path)
            mock_run.assert_not_called()
        assert flags2 == ["-R", "_build/default/mylib", "mylib"]

    def test_dune_flags_unknown_flags_dropped(self, tmp_path):
        """Unknown flags from dune output are silently dropped."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        (tmp_path / "test.v").write_text("")
        fake_output = "-native-compiler yes -R . mylib -boot"
        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout=fake_output)
            flags = _parse_dune_flags(tmp_path)
        assert flags == ["-R", ".", "mylib"]


# =========================================================================
# _force_release_pet_lock — deadlock recovery
# =========================================================================


class TestForceReleasePetLock:
    """Tests for _force_release_pet_lock deadlock recovery."""

    @pytest.fixture(autouse=True)
    def _restore_pet_lock(self):
        """Save and restore _pet_lock to prevent cross-test contamination."""
        import rocq_mcp.server as srv

        original = srv._pet_lock
        yield
        srv._pet_lock = original

    @pytest.mark.asyncio
    async def test_unlocked_is_noop(self):
        """When lock is free, _force_release_pet_lock is a no-op."""
        import rocq_mcp.server as srv

        old_lock = srv._pet_lock
        await _force_release_pet_lock()
        # Lock should still be the same object (not replaced)
        assert srv._pet_lock is old_lock
        # Lock must still be usable (not left in acquired state)
        assert old_lock.acquire(timeout=0.1)
        old_lock.release()

    @pytest.mark.asyncio
    async def test_replaces_stuck_lock(self):
        """When lock is held by another thread, replaces with fresh lock."""
        import rocq_mcp.server as srv

        old_lock = srv._pet_lock
        # Simulate an orphaned thread holding the lock
        old_lock.acquire()
        try:
            await _force_release_pet_lock()
            # Global lock should be replaced with a new one
            assert srv._pet_lock is not old_lock
            # New lock should be acquirable
            assert srv._pet_lock.acquire(timeout=0.1)
            srv._pet_lock.release()
        finally:
            old_lock.release()

    @pytest.mark.asyncio
    async def test_orphaned_thread_releases_old_lock_harmlessly(self):
        """Orphaned thread releasing old lock doesn't affect new global lock."""
        import rocq_mcp.server as srv

        old_lock = srv._pet_lock
        old_lock.acquire()

        await _force_release_pet_lock()
        new_lock = srv._pet_lock
        assert new_lock is not old_lock

        # Simulate orphaned thread waking up and releasing old lock
        old_lock.release()

        # New lock is unaffected
        assert new_lock.acquire(timeout=0.1)
        new_lock.release()

    def test_execute_captures_local_ref(self):
        """_execute functions capture local lock ref for safe release."""
        import rocq_mcp.server as srv

        results = []
        acquired_event = threading.Event()

        def simulate_execute():
            lock = srv._pet_lock  # capture local ref like _execute does
            lock.acquire()
            acquired_event.set()
            try:
                time.sleep(0.1)
                results.append("completed")
            finally:
                lock.release()

        t = threading.Thread(target=simulate_execute)
        t.start()
        acquired_event.wait(timeout=2)  # deterministic sync
        # Replace global (simulating _force_release_pet_lock)
        srv._pet_lock = threading.Lock()
        t.join(timeout=2)

        assert results == ["completed"]

    def test_pet_lock_timeout_is_not_asyncio_timeout(self):
        """_PetLockTimeout is NOT caught by except asyncio.TimeoutError."""
        with pytest.raises(_PetLockTimeout):
            try:
                raise _PetLockTimeout("test")
            except asyncio.TimeoutError:
                pytest.fail("_PetLockTimeout must not be caught as TimeoutError")


class TestReconstructTacticPath:
    """Tests for _reconstruct_tactic_path (state table chain walk)."""

    @pytest.fixture(autouse=True)
    def _clean_state_table(self):
        """Reset state table before/after each test."""
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        yield
        _state_invalidate_all()

    def _add_state(self, parent_id, tactic, step=0):
        """Helper: add a mock state entry to the table."""
        from rocq_mcp.interactive import _state_add
        from unittest.mock import MagicMock

        state = MagicMock()
        state.proof_finished = False
        return _state_add(
            state=state,
            file="test.v",
            theorem="t",
            workspace="/tmp",
            parent_id=parent_id,
            tactic=tactic,
            step=step,
        )

    def test_single_tactic(self):
        """Chain: root → tactic1."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = self._add_state(None, None, step=0)
        s1 = self._add_state(root, "intros.", step=1)
        tactics, complete = _reconstruct_tactic_path(s1)
        assert tactics == ["intros."]
        assert complete is True

    def test_multi_step_chain(self):
        """Chain: root → t1 → t2 → t3."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = self._add_state(None, None, step=0)
        s1 = self._add_state(root, "intros.", step=1)
        s2 = self._add_state(s1, "induction n.", step=2)
        s3 = self._add_state(s2, "reflexivity.", step=3)
        tactics, complete = _reconstruct_tactic_path(s3)
        assert tactics == [
            "intros.",
            "induction n.",
            "reflexivity.",
        ]
        assert complete is True

    def test_root_state_returns_empty(self):
        """Root state (tactic=None) returns empty list."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = self._add_state(None, None, step=0)
        tactics, complete = _reconstruct_tactic_path(root)
        assert tactics == []
        assert complete is True

    def test_branching_follows_parent_chain(self):
        """Two branches from root — each returns only its own path."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = self._add_state(None, None, step=0)
        # Branch A
        a1 = self._add_state(root, "intros.", step=1)
        a2 = self._add_state(a1, "auto.", step=2)
        # Branch B
        b1 = self._add_state(root, "intro n.", step=1)
        b2 = self._add_state(b1, "lia.", step=2)

        tactics_a, complete_a = _reconstruct_tactic_path(a2)
        assert tactics_a == ["intros.", "auto."]
        assert complete_a is True
        tactics_b, complete_b = _reconstruct_tactic_path(b2)
        assert tactics_b == ["intro n.", "lia."]
        assert complete_b is True

    def test_nonexistent_state_returns_empty(self):
        """Querying a non-existent state_id returns empty list."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        tactics, complete = _reconstruct_tactic_path(9999)
        assert tactics == []
        assert complete is False

    def test_broken_chain_returns_partial(self):
        """If ancestor is evicted, returns partial chain from first found."""
        from rocq_mcp.interactive import (
            _reconstruct_tactic_path,
            _state_table,
        )

        root = self._add_state(None, None, step=0)
        s1 = self._add_state(root, "intros.", step=1)
        s2 = self._add_state(s1, "auto.", step=2)
        # Simulate eviction of root and s1
        del _state_table[root]
        del _state_table[s1]
        # Only s2 survives — chain is broken
        tactics, complete = _reconstruct_tactic_path(s2)
        assert tactics == ["auto."]
        assert complete is False

    def test_cycle_detection(self):
        """A state whose parent_id points to itself terminates without infinite loop."""
        from rocq_mcp.interactive import (
            _reconstruct_tactic_path,
            _state_table,
        )

        s1 = self._add_state(None, "intros.", step=0)
        # Manually create a cycle: s1's parent_id points to itself
        _state_table[s1].parent_id = s1
        tactics, complete = _reconstruct_tactic_path(s1)
        # Should terminate; chain is not complete (cycle detected before reaching root)
        assert isinstance(tactics, list)
        assert complete is False

    def test_completeness_flag_true(self):
        """A normal chain root->s1->s2 returns (tactics, True)."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = self._add_state(None, None, step=0)
        s1 = self._add_state(root, "t1.", step=1)
        s2 = self._add_state(s1, "t2.", step=2)
        tactics, complete = _reconstruct_tactic_path(s2)
        assert tactics == ["t1.", "t2."]
        assert complete is True

    def test_completeness_flag_false_on_eviction(self):
        """When the root is evicted, returns (partial_tactics, False)."""
        from rocq_mcp.interactive import (
            _reconstruct_tactic_path,
            _state_table,
        )

        root = self._add_state(None, None, step=0)
        s1 = self._add_state(root, "intros.", step=1)
        s2 = self._add_state(s1, "auto.", step=2)
        # Evict root
        del _state_table[root]
        tactics, complete = _reconstruct_tactic_path(s2)
        assert complete is False
        # Should still have the tactics from surviving states
        assert "auto." in tactics


# =========================================================================
# _format_goals — truncation and formatting
# =========================================================================


class TestFormatGoals:
    """Test _format_goals formatting, truncation by count and by length."""

    def _make_goal(self, hyps_list=None, conclusion="True"):
        """Create a mock goal object with .hyps and .ty attributes."""
        from unittest.mock import MagicMock

        goal = MagicMock()
        goal.ty = conclusion
        if hyps_list is None:
            goal.hyps = []
        else:
            mock_hyps = []
            for names, ty in hyps_list:
                h = MagicMock()
                h.names = names
                h.ty = ty
                h.def_ = None
                mock_hyps.append(h)
            goal.hyps = mock_hyps
        return goal

    def test_truncates_many_goals(self):
        """More than _MAX_GOALS_SHOWN goals triggers the count truncation message."""
        from rocq_mcp.interactive import _format_goals, _MAX_GOALS_SHOWN

        goals = [
            self._make_goal(conclusion=f"goal_{i}") for i in range(_MAX_GOALS_SHOWN + 5)
        ]
        result = _format_goals(goals)
        assert "goals total, showing first" in result
        assert str(_MAX_GOALS_SHOWN + 5) in result

    def test_truncates_long_output(self):
        """Goals producing very long text (>_MAX_GOALS_LENGTH) are truncated."""
        from rocq_mcp.interactive import _format_goals, _MAX_GOALS_LENGTH

        # Create a single goal with a very long conclusion
        long_conclusion = "x" * (_MAX_GOALS_LENGTH + 500)
        goals = [self._make_goal(conclusion=long_conclusion)]
        result = _format_goals(goals)
        assert "truncated" in result
        # The result should be bounded (within _MAX_GOALS_LENGTH + truncation message)
        # The function truncates at _MAX_GOALS_LENGTH then appends message
        assert len(result) < _MAX_GOALS_LENGTH + 200

    def test_normal_goals_not_truncated(self):
        """Two small goals should not trigger any truncation."""
        from rocq_mcp.interactive import _format_goals

        goals = [
            self._make_goal(hyps_list=([["n"], "nat"],), conclusion="n = n"),
            self._make_goal(hyps_list=([["m"], "nat"],), conclusion="m = m"),
        ]
        result = _format_goals(goals)
        assert "truncated" not in result
        assert "goals total, showing first" not in result
        # Both goals should be present
        assert "Goal 1:" in result
        assert "Goal 2:" in result
        assert "n = n" in result
        assert "m = m" in result


# =========================================================================
# run_check body size limit
# =========================================================================


class TestRunCheckBodySizeLimit:
    """Test that run_check rejects bodies larger than ROCQ_MAX_SOURCE_SIZE."""

    @pytest.fixture(autouse=True)
    def _clean_state_table(self):
        """Reset state table before/after each test."""
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        yield
        _state_invalidate_all()

    def _add_state(self, parent_id, tactic, step=0):
        """Helper: add a mock state entry to the table."""
        from rocq_mcp.interactive import _state_add
        from unittest.mock import MagicMock

        state = MagicMock()
        state.proof_finished = False
        return _state_add(
            state=state,
            file="test.v",
            theorem="t",
            workspace="/tmp",
            parent_id=parent_id,
            tactic=tactic,
            step=step,
        )

    @pytest.mark.asyncio
    async def test_body_too_large(self, monkeypatch):
        """run_check with body exceeding ROCQ_MAX_SOURCE_SIZE returns error."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_check

        # Set a small source size limit for testing
        monkeypatch.setattr(srv, "ROCQ_MAX_SOURCE_SIZE", 100)

        # Create a state so that from_state lookup would succeed
        root = self._add_state(None, None, step=0)

        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
        }

        # Create body larger than the limit
        big_body = "x" * 200

        result = await run_check(
            body=big_body,
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root,
        )
        assert result["success"] is False
        assert (
            "too large" in result["error"].lower()
            or "Body too large" in result["error"]
        )


# =========================================================================
# State table eviction
# =========================================================================


class TestStateTableEviction:
    """Test state table eviction when _MAX_STATES is exceeded."""

    @pytest.fixture(autouse=True)
    def _clean_state_table(self):
        """Reset state table before/after each test."""
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        yield
        _state_invalidate_all()

    def _add_state(self, parent_id, tactic, step=0):
        """Helper: add a mock state entry to the table."""
        from rocq_mcp.interactive import _state_add
        from unittest.mock import MagicMock

        state = MagicMock()
        state.proof_finished = False
        return _state_add(
            state=state,
            file="test.v",
            theorem="t",
            workspace="/tmp",
            parent_id=parent_id,
            tactic=tactic,
            step=step,
        )

    def test_eviction_removes_oldest(self, monkeypatch):
        """When more states than _MAX_STATES are added, oldest are evicted."""
        import rocq_mcp.interactive as intermod

        monkeypatch.setattr(intermod, "_MAX_STATES", 5)

        ids = []
        for i in range(7):
            sid = self._add_state(None, f"tactic_{i}.", step=i)
            ids.append(sid)

        from rocq_mcp.interactive import _state_table

        # Only the last 5 should remain
        assert len(_state_table) == 5
        # First 2 should be evicted
        assert ids[0] not in _state_table
        assert ids[1] not in _state_table
        # Last 5 should still exist
        for sid in ids[2:]:
            assert sid in _state_table

    def test_evicted_state_returns_expired_error(self, monkeypatch):
        """Looking up an evicted state_id returns an 'expired' error."""
        import rocq_mcp.interactive as intermod
        from rocq_mcp.interactive import _state_get_or_error

        monkeypatch.setattr(intermod, "_MAX_STATES", 3)

        ids = []
        for i in range(5):
            sid = self._add_state(None, f"tactic_{i}.", step=i)
            ids.append(sid)

        # ids[0] and ids[1] should have been evicted
        entry, err = _state_get_or_error(ids[0])
        assert entry is None
        assert err is not None
        assert "expired" in err.lower()

    def test_nonexistent_state_returns_does_not_exist(self):
        """Looking up a state_id higher than _state_next_id returns 'does not exist'."""
        from rocq_mcp.interactive import _state_get_or_error, _state_next_id

        # Use an ID well beyond the next expected ID
        future_id = _state_next_id + 1000
        entry, err = _state_get_or_error(future_id)
        assert entry is None
        assert err is not None
        assert "does not exist" in err.lower()


# =========================================================================
# Pet invalidation hooks
# =========================================================================


class TestPetInvalidationHooks:
    """Test that pet invalidation hooks clear state table and import cache."""

    @pytest.fixture(autouse=True)
    def _clean(self):
        from rocq_mcp.interactive import _state_invalidate_all, _invalidate_import_cache

        _state_invalidate_all()
        _invalidate_import_cache()
        yield
        _state_invalidate_all()
        _invalidate_import_cache()

    def test_hooks_clear_state_table(self):
        """Invalidation hooks clear the state table."""
        from rocq_mcp.interactive import _state_add, _state_table, _state_invalidate_all
        from unittest.mock import MagicMock

        state = MagicMock()
        state.proof_finished = False
        _state_add(
            state=state,
            file="t.v",
            theorem="t",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )
        assert len(_state_table) > 0

        _state_invalidate_all()
        assert len(_state_table) == 0

    def test_hooks_clear_import_cache(self):
        """Invalidation hooks clear the import cache."""
        from rocq_mcp.interactive import _import_cache, _invalidate_import_cache

        _import_cache["test_key"] = "test_value"
        assert len(_import_cache) > 0

        _invalidate_import_cache()
        assert len(_import_cache) == 0

    def test_hooks_registered_in_server(self):
        """Both hooks are registered in _pet_invalidation_hooks."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import _state_invalidate_all, _invalidate_import_cache

        hook_funcs = srv._pet_invalidation_hooks
        assert _state_invalidate_all in hook_funcs
        assert _invalidate_import_cache in hook_funcs

    def test_invalidate_pet_calls_hooks(self):
        """_invalidate_pet triggers hooks that clear state table and import cache."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import (
            _state_add,
            _state_table,
            _import_cache,
        )
        from unittest.mock import MagicMock

        # Populate state table
        state = MagicMock()
        state.proof_finished = False
        _state_add(
            state=state,
            file="t.v",
            theorem="t",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )
        assert len(_state_table) > 0

        # Populate import cache
        _import_cache["key"] = "value"
        assert len(_import_cache) > 0

        # Call _invalidate_pet (no real pet, so pet_client is None)
        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }
        srv._invalidate_pet(lifespan_state)

        # Both should be cleared
        assert len(_state_table) == 0
        assert len(_import_cache) == 0

    def test_import_cache_generation_incremented(self):
        """_invalidate_import_cache increments the generation counter."""
        from rocq_mcp.interactive import (
            _import_cache_generation,
            _invalidate_import_cache,
        )
        import rocq_mcp.interactive as intermod

        gen_before = intermod._import_cache_generation
        _invalidate_import_cache()
        assert intermod._import_cache_generation == gen_before + 1


# =========================================================================
# run_check body within size limit
# =========================================================================


class TestRunCheckBodyWithinLimit:
    """Test that run_check does NOT reject bodies within ROCQ_MAX_SOURCE_SIZE."""

    @pytest.fixture(autouse=True)
    def _clean_state_table(self):
        """Reset state table before/after each test."""
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        yield
        _state_invalidate_all()

    def _add_state(self, parent_id, tactic, step=0):
        """Helper: add a mock state entry to the table."""
        from rocq_mcp.interactive import _state_add
        from unittest.mock import MagicMock

        state = MagicMock()
        state.proof_finished = False
        return _state_add(
            state=state,
            file="test.v",
            theorem="t",
            workspace="/tmp",
            parent_id=parent_id,
            tactic=tactic,
            step=step,
        )

    @pytest.mark.asyncio
    async def test_body_within_limit(self, monkeypatch):
        """run_check with body within ROCQ_MAX_SOURCE_SIZE passes the size check."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_check

        monkeypatch.setattr(srv, "ROCQ_MAX_SOURCE_SIZE", 1000)

        root = self._add_state(None, None, step=0)
        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
        }

        # Body within limit - should NOT be rejected by size check
        # (will fail for other reasons like no pet, but that's fine)
        small_body = "x" * 100
        result = await run_check(
            body=small_body,
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root,
        )
        # Should NOT have the "Body too large" error
        if not result["success"]:
            assert "too large" not in result.get("error", "").lower()

    @pytest.mark.asyncio
    async def test_body_exactly_at_limit(self, monkeypatch):
        """run_check with body exactly at ROCQ_MAX_SOURCE_SIZE passes the size check."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_check

        monkeypatch.setattr(srv, "ROCQ_MAX_SOURCE_SIZE", 200)

        root = self._add_state(None, None, step=0)
        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
        }

        # Body exactly at limit (not over)
        exact_body = "x" * 200
        result = await run_check(
            body=exact_body,
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root,
        )
        # Should NOT have the "Body too large" error
        if not result["success"]:
            assert "too large" not in result.get("error", "").lower()

    @pytest.mark.asyncio
    async def test_body_one_over_limit(self, monkeypatch):
        """run_check with body one byte over ROCQ_MAX_SOURCE_SIZE is rejected."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_check

        monkeypatch.setattr(srv, "ROCQ_MAX_SOURCE_SIZE", 200)

        root = self._add_state(None, None, step=0)
        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
        }

        # Body one byte over limit
        over_body = "x" * 201
        result = await run_check(
            body=over_body,
            timeout=30.0,
            lifespan_state=lifespan_state,
            from_state=root,
        )
        assert result["success"] is False
        assert "too large" in result["error"].lower()


# =========================================================================
# _kill_pet — process termination
# =========================================================================


class TestKillPet:
    """Unit tests for _kill_pet process termination."""

    def test_kill_pet_none(self):
        """_kill_pet with None pet is a no-op."""
        from rocq_mcp.server import _kill_pet

        _kill_pet(None)  # Should not raise

    def test_kill_pet_none_process(self):
        """_kill_pet with pet.process=None is a no-op."""
        from rocq_mcp.server import _kill_pet

        class FakePet:
            process = None

        _kill_pet(FakePet())  # Should not raise

    def test_kill_pet_already_dead_skips_signals(self):
        """_kill_pet skips signals if process already exited (PID reuse guard)."""
        from rocq_mcp.server import _kill_pet
        from unittest.mock import MagicMock, patch

        pet = MagicMock()
        pet.process.poll.return_value = 0  # Already exited
        pet.process.stdin = MagicMock()
        pet.process.stdout = MagicMock()
        pet.process.stderr = MagicMock()
        pet._own_pgrp = True

        with patch("rocq_mcp.server.os.killpg") as mock_killpg:
            _kill_pet(pet)
            mock_killpg.assert_not_called()  # No signals sent

        # But FDs should still be closed
        pet.process.stdin.close.assert_called_once()
        pet.process.stdout.close.assert_called_once()
        pet.process.stderr.close.assert_called_once()

    def test_kill_pet_with_own_pgrp_sends_sigterm(self):
        """_kill_pet with _own_pgrp=True uses os.killpg(SIGTERM)."""
        from rocq_mcp.server import _kill_pet
        from unittest.mock import MagicMock, patch
        import signal

        pet = MagicMock()
        pet.process.poll.return_value = None  # Still running
        pet.process.pid = 12345
        pet.process.wait.return_value = 0  # Exits after SIGTERM
        pet.process.stdin = MagicMock()
        pet.process.stdout = MagicMock()
        pet.process.stderr = MagicMock()
        pet._own_pgrp = True

        with (
            patch("rocq_mcp.server.os.getpgid", return_value=12345) as mock_getpgid,
            patch("rocq_mcp.server.os.killpg") as mock_killpg,
        ):
            _kill_pet(pet)
            mock_killpg.assert_called_once_with(12345, signal.SIGTERM)

    def test_kill_pet_without_own_pgrp_uses_terminate(self):
        """_kill_pet with _own_pgrp=False uses process.terminate()."""
        from rocq_mcp.server import _kill_pet
        from unittest.mock import MagicMock

        pet = MagicMock()
        pet.process.poll.return_value = None  # Still running
        pet.process.wait.return_value = 0
        pet.process.stdin = MagicMock()
        pet.process.stdout = MagicMock()
        pet.process.stderr = MagicMock()
        pet._own_pgrp = False

        _kill_pet(pet)
        pet.process.terminate.assert_called_once()

    def test_kill_pet_escalates_to_sigkill(self):
        """_kill_pet escalates to SIGKILL if SIGTERM doesn't work."""
        from rocq_mcp.server import _kill_pet
        from unittest.mock import MagicMock, patch
        import signal
        import subprocess

        pet = MagicMock()
        pet.process.poll.return_value = None  # Still running
        pet.process.pid = 12345
        # First wait raises TimeoutExpired, second succeeds
        pet.process.wait.side_effect = [
            subprocess.TimeoutExpired("coqc", 2),
            0,
        ]
        pet.process.stdin = MagicMock()
        pet.process.stdout = MagicMock()
        pet.process.stderr = MagicMock()
        pet._own_pgrp = True

        with (
            patch("rocq_mcp.server.os.getpgid", return_value=12345),
            patch("rocq_mcp.server.os.killpg") as mock_killpg,
        ):
            _kill_pet(pet)
            assert mock_killpg.call_count == 2
            mock_killpg.assert_any_call(12345, signal.SIGTERM)
            mock_killpg.assert_any_call(12345, signal.SIGKILL)


# =========================================================================
# _ensure_pet — invalidation hooks on dead pet
# =========================================================================


class TestEnsurePetHooks:
    """Test that _ensure_pet calls invalidation hooks when pet is dead."""

    def test_hooks_called_on_dead_pet_detection(self):
        """When _ensure_pet finds a dead pet, it calls _kill_pet and hooks."""
        import rocq_mcp.server as server
        from unittest.mock import MagicMock, patch

        hook_calls = []
        original_hooks = list(server._pet_invalidation_hooks)
        server._pet_invalidation_hooks.append(lambda: hook_calls.append("called"))

        dead_pet = MagicMock()
        dead_pet.process.poll.return_value = 1  # Dead
        dead_pet.process.stdin = MagicMock()
        dead_pet.process.stdout = MagicMock()
        dead_pet.process.stderr = MagicMock()
        dead_pet._own_pgrp = False

        lifespan_state = {"pet_client": dead_pet}

        try:
            # Mock pytanque import to avoid real subprocess
            mock_pytanque = MagicMock()
            mock_new_pet = MagicMock()
            mock_new_pet.process = MagicMock()
            mock_new_pet.process.pid = 99999
            mock_pytanque.Pytanque.return_value = mock_new_pet
            mock_pytanque.PytanqueMode = MagicMock()

            with patch.dict("sys.modules", {"pytanque": mock_pytanque}):
                server._ensure_pet(lifespan_state)

            assert "called" in hook_calls, "Invalidation hooks should fire on dead pet"
            assert lifespan_state["pet_client"] is mock_new_pet
        finally:
            server._pet_invalidation_hooks[:] = original_hooks


# =========================================================================
# _run_with_pet — exception handling paths
# =========================================================================


class TestRunWithPetExceptionHandling:
    """Tests for _run_with_pet exception handling paths."""

    @pytest.fixture(autouse=True)
    def _reset_semaphore(self):
        """Reset the global semaphore so tests don't interfere."""
        import rocq_mcp.server as srv

        srv._pet_semaphore = None
        yield
        srv._pet_semaphore = None

    @pytest.mark.asyncio
    async def test_petanque_error_dead_pet_returns_pet_restarted(self):
        """PetanqueError + dead pet -> pet_restarted: True."""
        from unittest.mock import MagicMock

        try:
            from pytanque import PetanqueError
        except ImportError:
            pytest.skip("pytanque not installed")

        # Create a mock pet that appears dead (poll returns non-None)
        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = 1  # dead
        mock_pet.process.stdin = None
        mock_pet.process.stdout = None
        mock_pet.process.stderr = None
        mock_pet._own_pgrp = False

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 10.0,
            "current_workspace": None,
        }

        def fn_that_raises(pet):
            raise PetanqueError(1, "Connection lost")

        with pytest.MonkeyPatch.context() as mp:
            mp.setattr("rocq_mcp.server._ensure_pet", lambda ls: mock_pet)
            result = await _run_with_pet(fn_that_raises, lifespan_state, "Test")
        assert result["success"] is False
        assert result.get("pet_restarted") is True
        assert "Pet process died" in result["error"]

    @pytest.mark.asyncio
    async def test_petanque_error_alive_pet_returns_plain_error(self):
        """PetanqueError + alive pet -> plain error without pet_restarted."""
        from unittest.mock import MagicMock

        try:
            from pytanque import PetanqueError
        except ImportError:
            pytest.skip("pytanque not installed")

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None  # alive

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 10.0,
            "current_workspace": None,
        }

        def fn_that_raises(pet):
            raise PetanqueError(1, "Tactic failed")

        with pytest.MonkeyPatch.context() as mp:
            mp.setattr("rocq_mcp.server._ensure_pet", lambda ls: mock_pet)
            result = await _run_with_pet(fn_that_raises, lifespan_state, "Test")
        assert result["success"] is False
        assert "pet_restarted" not in result
        assert "Tactic failed" in result["error"]

    @pytest.mark.asyncio
    async def test_broken_pipe_calls_on_timeout_callback(self):
        """BrokenPipeError calls on_timeout callback and returns pet_restarted."""
        from unittest.mock import MagicMock

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = 1  # dead
        mock_pet.process.stdin = None
        mock_pet.process.stdout = None
        mock_pet.process.stderr = None
        mock_pet._own_pgrp = False

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 10.0,
            "current_workspace": None,
        }

        callback_called = []

        def fn_that_raises(pet):
            raise BrokenPipeError("broken")

        with pytest.MonkeyPatch.context() as mp:
            mp.setattr("rocq_mcp.server._ensure_pet", lambda ls: mock_pet)
            result = await _run_with_pet(
                fn_that_raises,
                lifespan_state,
                "Test",
                on_timeout=lambda: callback_called.append(True),
            )
        assert result["success"] is False
        assert result.get("pet_restarted") is True
        assert len(callback_called) == 1

    @pytest.mark.asyncio
    async def test_file_not_found_returns_helpful_error(self):
        """FileNotFoundError returns helpful error message."""
        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 10.0,
            "current_workspace": None,
        }

        def fn(pet):
            pass  # won't be called

        with pytest.MonkeyPatch.context() as mp:

            def raise_fnf(ls):
                raise FileNotFoundError("pet")

            mp.setattr("rocq_mcp.server._ensure_pet", raise_fnf)
            result = await _run_with_pet(fn, lifespan_state, "Test")
        assert result["success"] is False
        assert "pet binary not found" in result["error"]


# =========================================================================
# _merge_partial_state — safe merge helper
# =========================================================================


class TestMergePartialState:
    """Tests for _merge_partial_state."""

    def test_adds_new_keys(self):
        resp = {"success": False, "error": "timeout"}
        _merge_partial_state(resp, {"partial_results": [1, 2]})
        assert resp["partial_results"] == [1, 2]

    def test_does_not_overwrite_success(self):
        """partial_state must not clobber the 'success' key."""
        resp = {"success": False, "error": "timeout"}
        _merge_partial_state(resp, {"success": True, "extra": "data"})
        assert resp["success"] is False
        assert resp["extra"] == "data"

    def test_does_not_overwrite_error(self):
        """partial_state must not clobber the 'error' key."""
        resp = {"success": False, "error": "real error"}
        _merge_partial_state(resp, {"error": "fake", "partial_results": []})
        assert resp["error"] == "real error"
        assert resp["partial_results"] == []

    def test_does_not_overwrite_pet_restarted(self):
        resp = {"success": False, "error": "died", "pet_restarted": True}
        _merge_partial_state(resp, {"pet_restarted": False, "data": 42})
        assert resp["pet_restarted"] is True
        assert resp["data"] == 42

    def test_empty_partial_state(self):
        resp = {"success": False, "error": "timeout"}
        _merge_partial_state(resp, {})
        assert resp == {"success": False, "error": "timeout"}


# =========================================================================
# _format_goals — def_ field handling
# =========================================================================


class TestFormatGoalsDefField:
    """Test _format_goals with hypothesis def_ field."""

    def test_hypothesis_with_def(self):
        """Hypothesis with def_ should include ':= <value>' in output."""
        from unittest.mock import MagicMock

        goal = MagicMock()
        hyp = MagicMock()
        hyp.names = ["x"]
        hyp.def_ = "0"
        hyp.ty = "nat"
        goal.hyps = [hyp]
        goal.ty = "x = 0"

        result = _format_goals([goal])
        assert ":= 0" in result
        assert ": nat" in result

    def test_hypothesis_without_def(self):
        """Hypothesis with def_=None should NOT include ':=' in output."""
        from unittest.mock import MagicMock

        goal = MagicMock()
        hyp = MagicMock()
        hyp.names = ["x"]
        hyp.def_ = None
        hyp.ty = "nat"
        goal.hyps = [hyp]
        goal.ty = "x = 0"

        result = _format_goals([goal])
        assert ":=" not in result
        assert ": nat" in result

    def test_hypothesis_with_empty_string_def(self):
        """Hypothesis with def_='' (empty) should NOT include ':=' in output."""
        from unittest.mock import MagicMock

        goal = MagicMock()
        hyp = MagicMock()
        hyp.names = ["x"]
        hyp.def_ = ""
        hyp.ty = "nat"
        goal.hyps = [hyp]
        goal.ty = "x = 0"

        result = _format_goals([goal])
        assert ":=" not in result
        assert ": nat" in result
