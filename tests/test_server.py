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
    _find_project_root_from_file,
    _force_release_pet_lock,
    _merge_partial_state,
    _parse_dune_flags,
    _parse_project_flags,
    _PetLockTimeout,
    _resolve_call_timeout,
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
from tests.conftest import add_mock_state

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
# _resolve_call_timeout
# =========================================================================


class TestResolveCallTimeout:
    """Test _resolve_call_timeout: clamp-and-resolve helper shared by every
    pet-routed wrapper.  Locks in the (effective_timeout, clamped) contract
    that the wrappers depend on for the ``clamped_timeout`` echo."""

    def test_zero_falls_through_to_pet_timeout(self):
        """timeout=0 (the default) → (None, False), so the caller falls back
        to ``ROCQ_PET_TIMEOUT``."""
        effective, clamped = _resolve_call_timeout(0)
        assert effective is None
        assert clamped is False

    def test_negative_falls_through_to_pet_timeout(self):
        """A negative timeout is treated like the default sentinel."""
        effective, clamped = _resolve_call_timeout(-1)
        assert effective is None
        assert clamped is False

    def test_under_cap_passes_through_as_float(self):
        """A positive timeout under the cap is forwarded as a float, no clamp."""
        with mock.patch("rocq_mcp.server.ROCQ_QUERY_TIMEOUT_CAP", 300):
            effective, clamped = _resolve_call_timeout(10)
        assert effective == 10.0
        assert isinstance(effective, float)
        assert clamped is False

    def test_at_cap_passes_through_unclamped(self):
        """A timeout exactly equal to the cap is not flagged as clamped."""
        with mock.patch("rocq_mcp.server.ROCQ_QUERY_TIMEOUT_CAP", 300):
            effective, clamped = _resolve_call_timeout(300)
        assert effective == 300.0
        assert clamped is False

    def test_over_cap_is_clamped(self):
        """A timeout above the cap is clamped to the cap, clamped=True."""
        with mock.patch("rocq_mcp.server.ROCQ_QUERY_TIMEOUT_CAP", 300):
            effective, clamped = _resolve_call_timeout(400)
        assert effective == 300.0
        assert clamped is True


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

    def test_multi_theory_unions_per_theory_flags(self, tmp_path):
        """Workspace with N coq.theory dirs queries each, unions all -Q lines."""
        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        # Two theory roots, mirroring bn-peters' rocq-lsp-dune example.
        (tmp_path / "thA").mkdir()
        (tmp_path / "thA" / "dune").write_text(
            "(coq.theory (name thA) (theories Stdlib))\n"
        )
        (tmp_path / "thA" / "a.v").write_text("")
        (tmp_path / "thB").mkdir()
        (tmp_path / "thB" / "dune").write_text(
            "(coq.theory (name thB) (theories Stdlib))\n"
        )
        (tmp_path / "thB" / "b.v").write_text("")

        # Per-call dune coq top output: each theory yields its own -Q
        # line plus a shared -w flag (which must be deduped).
        def fake_run(cmd, *_a, **_kw):
            v_arg = cmd[-1]
            assert v_arg.endswith(".v"), cmd
            if v_arg.startswith("thA"):
                stdout = "-Q _build/default/thA thA -w -shared"
            else:
                stdout = "-Q _build/default/thB thB -w -shared"
            return mock.Mock(returncode=0, stdout=stdout)

        with mock.patch("rocq_mcp.server.subprocess.run", side_effect=fake_run):
            flags = _parse_dune_flags(tmp_path)

        # Both theory roots present.
        assert flags is not None
        assert "_build/default/thA" in flags and "thA" in flags
        assert "_build/default/thB" in flags and "thB" in flags
        # The shared -w flag appears once, not twice.
        assert flags.count("-shared") == 1

        # Generated _RocqProject has both -Q lines.
        proj = (tmp_path / "_RocqProject").read_text()
        assert "-Q _build/default/thA thA" in proj
        assert "-Q _build/default/thB thB" in proj
        # And the deduped -w line appears once.
        assert proj.count("-arg -shared") == 1

    def test_multi_theory_invokes_dune_once_per_theory(self, tmp_path):
        """Sanity: N=2 theory roots -> exactly 2 dune coq top calls."""
        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        for name in ("thA", "thB"):
            d = tmp_path / name
            d.mkdir()
            (d / "dune").write_text(f"(coq.theory (name {name}))\n")
            (d / "x.v").write_text("")

        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout="-Q . X")
            _parse_dune_flags(tmp_path)
        assert mock_run.call_count == 2

    def test_single_theory_uses_single_query(self, tmp_path):
        """N<=1 theory root preserves the original single-file behaviour."""
        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        # Only one coq.theory stanza.
        d = tmp_path / "only"
        d.mkdir()
        (d / "dune").write_text("(coq.theory (name only))\n")
        (d / "x.v").write_text("")

        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(
                returncode=0, stdout="-Q _build/default/only only"
            )
            flags = _parse_dune_flags(tmp_path)
        assert mock_run.call_count == 1
        assert flags == ["-Q", "_build/default/only", "only"]

    def test_coq_theory_in_line_comment_not_matched(self, tmp_path):
        """A ``;``-commented `(coq.theory ...)` line must not be treated as a stanza.

        Anchored regex protects against false positives in commented-out
        stanzas; without anchoring, the substring scan would count this dir.
        """
        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        # One real theory + one with the stanza commented out.
        (tmp_path / "real").mkdir()
        (tmp_path / "real" / "dune").write_text("(coq.theory (name real))\n")
        (tmp_path / "real" / "x.v").write_text("")
        (tmp_path / "fake").mkdir()
        (tmp_path / "fake" / "dune").write_text("; (coq.theory (name fake))\n")
        (tmp_path / "fake" / "x.v").write_text("")

        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(returncode=0, stdout="-Q . real")
            _parse_dune_flags(tmp_path)
        # Only the real stanza counts -> exactly one dune coq top call.
        assert mock_run.call_count == 1

    def test_pick_v_file_skips_build_dir(self, tmp_path):
        """_pick_v_file ignores .v files under _build/."""
        from rocq_mcp.server import _pick_v_file

        # Only .v files under _build -> should return None.
        build = tmp_path / "_build" / "default"
        build.mkdir(parents=True)
        (build / "foo.v").write_text("")
        assert _pick_v_file(tmp_path) is None

        # Adding a real source .v elsewhere -> _pick_v_file returns it.
        src = tmp_path / "src"
        src.mkdir()
        real = src / "real.v"
        real.write_text("")
        assert _pick_v_file(tmp_path) == real

    def test_pick_v_file_prefers_shallow(self, tmp_path):
        """_pick_v_file prefers a top-level .v over a deeper one."""
        from rocq_mcp.server import _pick_v_file

        sub = tmp_path / "sub"
        sub.mkdir()
        deep = sub / "deep.v"
        deep.write_text("")
        shallow = tmp_path / "shallow.v"
        shallow.write_text("")
        assert _pick_v_file(tmp_path) == shallow

    def test_multi_theory_one_failure_others_succeed(self, tmp_path):
        """If one theory's dune coq top fails, the others still produce flags."""
        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        for name in ("thA", "thB"):
            d = tmp_path / name
            d.mkdir()
            (d / "dune").write_text(f"(coq.theory (name {name}))\n")
            (d / "x.v").write_text("")

        def fake_run(cmd, *_a, **_kw):
            v_arg = cmd[-1]
            if v_arg.startswith("thA"):
                # thA fails (e.g., dune build cache missing for that theory).
                return mock.Mock(returncode=1, stdout="")
            return mock.Mock(returncode=0, stdout="-Q _build/default/thB thB")

        with mock.patch("rocq_mcp.server.subprocess.run", side_effect=fake_run):
            flags = _parse_dune_flags(tmp_path)
        assert flags == ["-Q", "_build/default/thB", "thB"]


# =========================================================================
# _find_project_root_from_file — workspace auto-detection
# =========================================================================


def _make_v(parent_dir):
    """Create an empty foo.v in *parent_dir* and return its path."""
    f = parent_dir / "foo.v"
    f.write_text("")
    return f


class TestFindProjectRootFromFile:
    """Tests for the parent-directory walk that auto-detects workspaces."""

    def test_empty_string_returns_none(self):
        """Empty path short-circuits without walking."""
        assert _find_project_root_from_file("") is None

    def test_none_returns_none(self):
        """None path short-circuits without walking."""
        assert _find_project_root_from_file(None) is None

    def test_no_marker_returns_none(self, tmp_path):
        """A file with no project marker anywhere up the tree returns None."""
        assert _find_project_root_from_file(str(_make_v(tmp_path))) is None

    def test_rocqproject_in_same_dir(self, tmp_path):
        """File in the same dir as _RocqProject resolves there."""
        (tmp_path / "_RocqProject").write_text("-Q . MyLib\n")
        assert _find_project_root_from_file(str(_make_v(tmp_path))) == str(
            tmp_path.resolve()
        )

    def test_coqproject_in_same_dir(self, tmp_path):
        """_CoqProject is recognised when no _RocqProject is present."""
        (tmp_path / "_CoqProject").write_text("-Q . MyLib\n")
        assert _find_project_root_from_file(str(_make_v(tmp_path))) == str(
            tmp_path.resolve()
        )

    def test_dune_project_in_same_dir(self, tmp_path):
        """dune-project is recognised when no _RocqProject/_CoqProject is present."""
        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        assert _find_project_root_from_file(str(_make_v(tmp_path))) == str(
            tmp_path.resolve()
        )

    def test_rocqproject_beats_coqproject_in_same_dir(self, tmp_path):
        """When both markers coexist, _RocqProject (priority 0) wins.

        Locks in the priority order in ``_PROJECT_MARKERS`` so a future
        reorder doesn't silently change behaviour.  The returned path is
        the same dir either way; this test would catch a divergence if
        the markers ever placed different load paths.
        """
        (tmp_path / "_RocqProject").write_text("-Q . New\n")
        (tmp_path / "_CoqProject").write_text("-Q . Old\n")
        # Both live in the same dir, so the helper still returns tmp_path;
        # the value of this test is in pinning the helper to actually
        # iterate _PROJECT_MARKERS in order (rather than via os.listdir).
        assert _find_project_root_from_file(str(_make_v(tmp_path))) == str(
            tmp_path.resolve()
        )

    def test_rocqproject_in_parent(self, tmp_path):
        """Walks up: file in subdir, _RocqProject in tmp_path."""
        (tmp_path / "_RocqProject").write_text("-Q . MyLib\n")
        sub = tmp_path / "src"
        sub.mkdir()
        assert _find_project_root_from_file(str(_make_v(sub))) == str(
            tmp_path.resolve()
        )

    def test_walks_multiple_levels(self, tmp_path):
        """Walks up through several directory levels."""
        (tmp_path / "_RocqProject").write_text("-Q . MyLib\n")
        deep = tmp_path / "a" / "b" / "c"
        deep.mkdir(parents=True)
        assert _find_project_root_from_file(str(_make_v(deep))) == str(
            tmp_path.resolve()
        )

    def test_innermost_marker_wins(self, tmp_path):
        """When markers exist at multiple levels, the innermost wins."""
        (tmp_path / "_RocqProject").write_text("-Q . Outer\n")
        sub = tmp_path / "inner"
        sub.mkdir()
        (sub / "_RocqProject").write_text("-Q . Inner\n")
        assert _find_project_root_from_file(str(_make_v(sub))) == str(sub.resolve())

    def test_directory_path_walks_from_directory(self, tmp_path):
        """A directory path (not a file) starts the walk from itself."""
        (tmp_path / "_RocqProject").write_text("-Q . MyLib\n")
        sub = tmp_path / "src"
        sub.mkdir()
        # Pass the directory, not a file inside it.
        assert _find_project_root_from_file(str(sub)) == str(tmp_path.resolve())

    def test_nonexistent_path_walks_from_logical_parent(self, tmp_path):
        """Absolute path the user typed but the file does not exist yet.

        ``Path(...).absolute()`` still returns a path; ``is_file()`` is
        False so we walk from the lexical parent.
        """
        (tmp_path / "_RocqProject").write_text("-Q . MyLib\n")
        f = tmp_path / "src" / "does_not_exist.v"
        # Don't create src/ at all.
        assert _find_project_root_from_file(str(f)) == str(tmp_path.resolve())

    def test_relative_path_resolved_against_rocq_workspace(self, tmp_path, monkeypatch):
        """A relative *file* is resolved against ``ROCQ_WORKSPACE``.

        This matches the documented tool contract ("Path to the .v file
        (relative to workspace)") and avoids cwd-dependent surprises.
        """
        (tmp_path / "_RocqProject").write_text("-Q . MyLib\n")
        sub = tmp_path / "src"
        sub.mkdir()
        _make_v(sub)
        # Point ROCQ_WORKSPACE at tmp_path; pass the file as relative.
        monkeypatch.setattr("rocq_mcp.server.ROCQ_WORKSPACE", str(tmp_path))
        assert _find_project_root_from_file("src/foo.v") == str(tmp_path.resolve())

    def test_resolve_oserror_returns_none(self, monkeypatch):
        """Path resolution errors propagate as None (defensive)."""

        class _BadPath:
            def __init__(self, *_):
                pass

            def is_absolute(self):
                raise OSError("boom")

        monkeypatch.setattr("rocq_mcp.server.Path", _BadPath)
        assert _find_project_root_from_file("/some/file.v") is None


# =========================================================================
# Wrapper integration: workspace auto-detection flows through to the impl
# =========================================================================


class TestWrapperWorkspaceAutoDetect:
    """Integration: each file-accepting tool wires the helper into the workspace.

    These tests would catch a regression where one of the five
    ``_find_project_root_from_file`` call sites is silently removed during
    a refactor.  They spy on ``_validate_workspace`` (the boundary right
    after the auto-detection) to capture the workspace that flows in, and
    stub each tool's downstream implementation so the call short-circuits.
    """

    @pytest.fixture
    def project_with_file(self, tmp_path):
        """Create _RocqProject in *tmp_path* and a foo.v in a subdir."""
        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        sub = tmp_path / "src"
        sub.mkdir()
        f = sub / "foo.v"
        f.write_text("")
        return tmp_path, f

    @staticmethod
    def _setup_spies(monkeypatch):
        """Spy ``_validate_workspace`` and stub all 5 impl functions.

        Returns a dict that captures the workspace passed to validation.
        """
        from rocq_mcp import server as _server

        seen: dict = {}

        def spy_validate(ws):
            seen["workspace"] = ws
            return None

        async def stub(*_args, **_kwargs):
            return {"success": True, "output": ""}

        monkeypatch.setattr(_server, "_validate_workspace", spy_validate)
        for impl in (
            "run_compile_file_with_state",
            "run_query",
            "run_assumptions",
            "run_toc",
            "run_start",
        ):
            monkeypatch.setattr(_server, impl, stub)
        return seen

    @pytest.mark.parametrize(
        "tool_name,extra_kwargs",
        [
            ("rocq_compile_file", {}),
            ("rocq_query", {"command": "Check nat."}),
            ("rocq_assumptions", {"name": "t"}),
            ("rocq_toc", {}),
            ("rocq_start", {"theorem": "t"}),
        ],
    )
    async def test_wrapper_autodetects_workspace(
        self, tool_name, extra_kwargs, project_with_file, monkeypatch
    ):
        """Each wrapper auto-detects workspace from the file's project root."""
        from rocq_mcp import server as _server
        from tests.conftest import _MockContext

        proj, f = project_with_file
        seen = self._setup_spies(monkeypatch)
        ctx = _MockContext({"pet_client": None, "pet_timeout": 30.0})

        tool = getattr(_server, tool_name)
        await tool(file=str(f), ctx=ctx, **extra_kwargs)

        assert seen["workspace"] == str(Path(proj).absolute()), tool_name

    async def test_explicit_workspace_overrides_autodetect(
        self, project_with_file, monkeypatch
    ):
        """An explicit ``workspace=`` arg bypasses auto-detection."""
        from rocq_mcp import server as _server
        from tests.conftest import _MockContext

        _proj, f = project_with_file
        seen = self._setup_spies(monkeypatch)
        ctx = _MockContext({"pet_client": None, "pet_timeout": 30.0})

        explicit = "/some/other/dir"
        await _server.rocq_toc(file=str(f), workspace=explicit, ctx=ctx)

        assert seen["workspace"] == explicit


# =========================================================================
# Workspace warning on synthetic fallback (P1-2)
# =========================================================================


class TestWorkspaceHasProjectMarker:
    """Tests for the ``_workspace_has_project_marker`` helper."""

    def test_empty_dir_returns_false(self, tmp_path):
        from rocq_mcp.server import _workspace_has_project_marker

        assert _workspace_has_project_marker(tmp_path) is False

    def test_rocqproject_marker(self, tmp_path):
        from rocq_mcp.server import _workspace_has_project_marker

        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        assert _workspace_has_project_marker(tmp_path) is True

    def test_coqproject_marker(self, tmp_path):
        from rocq_mcp.server import _workspace_has_project_marker

        (tmp_path / "_CoqProject").write_text("-Q . M\n")
        assert _workspace_has_project_marker(tmp_path) is True

    def test_dune_project_marker(self, tmp_path):
        from rocq_mcp.server import _workspace_has_project_marker

        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        assert _workspace_has_project_marker(tmp_path) is True

    def test_directory_named_like_marker_is_not_a_marker(self, tmp_path):
        """A *directory* named _RocqProject doesn't count — only files do."""
        from rocq_mcp.server import _workspace_has_project_marker

        (tmp_path / "_RocqProject").mkdir()
        assert _workspace_has_project_marker(tmp_path) is False

    def test_dune_project_ancestor_subdir(self, tmp_path):
        """A subdir of a dune workspace (no local marker file) still counts
        because ``_parse_project_flags`` falls through to dune-aware
        resolution that walks UP via ``_find_dune_root``.  Without this,
        e.g. ``mathcomp/theories/algebra/`` would trigger a spurious
        warning.
        """
        from rocq_mcp.server import _workspace_has_project_marker

        (tmp_path / "dune-project").write_text("(lang dune 3.0)\n")
        sub = tmp_path / "theories" / "algebra"
        sub.mkdir(parents=True)
        assert _workspace_has_project_marker(sub) is True


class TestWorkspaceWarning:
    """End-to-end: each entry-point attaches workspace_warning when the
    resolved workspace lacks a project marker.

    Mirrors ``TestWrapperWorkspaceAutoDetect`` — spies validation and
    stubs the downstream impl so we exercise the wrapper logic in
    isolation.  Confirms the fix for the silent synthetic-flags
    fallback when a workspace has no project marker.
    """

    @staticmethod
    def _setup_spies(monkeypatch):
        from rocq_mcp import server as _server

        async def stub(*_args, **_kwargs):
            return {"success": True, "output": ""}

        # Validation always passes; we're testing the warning branch.
        monkeypatch.setattr(_server, "_validate_workspace", lambda _ws: None)
        for impl in (
            "run_compile_with_state",
            "run_compile_file_with_state",
            "run_verify",
            "run_query",
            "run_assumptions",
            "run_toc",
            "run_notations",
            "run_start",
        ):
            monkeypatch.setattr(_server, impl, stub)

    @pytest.fixture
    def markerless_dir(self, tmp_path):
        """A directory with no _RocqProject / _CoqProject / dune-project."""
        sub = tmp_path / "no_marker"
        sub.mkdir()
        return sub

    @pytest.fixture
    def marker_dir(self, tmp_path):
        """A directory with a _RocqProject file."""
        sub = tmp_path / "with_marker"
        sub.mkdir()
        (sub / "_RocqProject").write_text("-Q . M\n")
        return sub

    @pytest.fixture
    def _ctx(self):
        from tests.conftest import _MockContext

        return _MockContext({"pet_client": None, "pet_timeout": 30.0})

    # ---- explicit workspace= without marker → warning fires --------------

    @pytest.mark.parametrize(
        "tool_name,extra_kwargs",
        [
            ("rocq_compile", {"source": "Theorem t : True. Proof. exact I. Qed."}),
            ("rocq_compile_file", {"file": "foo.v"}),
            (
                "rocq_verify",
                {
                    "proof": "Theorem t : True. Proof. exact I. Qed.",
                    "problem_name": "t",
                    "problem_statement": "Theorem t : True. Admitted.",
                },
            ),
            ("rocq_query", {"command": "Check nat."}),
            ("rocq_assumptions", {"name": "t", "file": "foo.v"}),
            ("rocq_toc", {"file": "foo.v"}),
            ("rocq_notations", {"statement": "True"}),
            ("rocq_start", {"file": "foo.v", "theorem": "t"}),
        ],
    )
    async def test_explicit_workspace_without_marker_warns(
        self, tool_name, extra_kwargs, markerless_dir, _ctx, monkeypatch
    ):
        from rocq_mcp import server as _server

        self._setup_spies(monkeypatch)
        tool = getattr(_server, tool_name)
        result = await tool(workspace=str(markerless_dir), ctx=_ctx, **extra_kwargs)

        assert "workspace_warning" in result, tool_name
        warning = result["workspace_warning"]
        # Canonical text components.
        assert "No _RocqProject / _CoqProject / dune-project" in warning
        assert str(markerless_dir) in warning
        # Generic phrasing about unqualified library references (no
        # project-specific example symbol).
        assert "unqualified library references" in warning
        # Action-first recovery hint covering the file= path.
        assert "auto-detect from" in warning

    @pytest.mark.parametrize(
        "tool_name,extra_kwargs",
        [
            ("rocq_compile", {"source": "Theorem t : True. Proof. exact I. Qed."}),
            ("rocq_compile_file", {"file": "foo.v"}),
            (
                "rocq_verify",
                {
                    "proof": "Theorem t : True. Proof. exact I. Qed.",
                    "problem_name": "t",
                    "problem_statement": "Theorem t : True. Admitted.",
                },
            ),
            ("rocq_query", {"command": "Check nat."}),
            ("rocq_assumptions", {"name": "t", "file": "foo.v"}),
            ("rocq_toc", {"file": "foo.v"}),
            ("rocq_notations", {"statement": "True"}),
            ("rocq_start", {"file": "foo.v", "theorem": "t"}),
        ],
    )
    async def test_explicit_workspace_with_marker_quiet(
        self, tool_name, extra_kwargs, marker_dir, _ctx, monkeypatch
    ):
        """A workspace that DOES have a marker is quiet."""
        from rocq_mcp import server as _server

        self._setup_spies(monkeypatch)
        tool = getattr(_server, tool_name)
        result = await tool(workspace=str(marker_dir), ctx=_ctx, **extra_kwargs)

        assert "workspace_warning" not in result, tool_name

    # ---- auto-detect cases -----------------------------------------------

    async def test_auto_detect_with_marker_quiet(self, tmp_path, _ctx, monkeypatch):
        """When auto-detect finds a project root, no warning fires even
        though the user didn't pass workspace= explicitly.

        Strict policy: a successful walk-up is the happy path.
        """
        from rocq_mcp import server as _server

        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        sub = tmp_path / "src"
        sub.mkdir()
        f = sub / "foo.v"
        f.write_text("")

        self._setup_spies(monkeypatch)
        result = await _server.rocq_toc(file=str(f), ctx=_ctx)
        assert "workspace_warning" not in result

    async def test_auto_detect_misses_with_file_hint_warns(
        self, markerless_dir, _ctx, monkeypatch
    ):
        """When the user passes file= but no marker is found anywhere up
        the tree AND ROCQ_WORKSPACE has no marker either, the warning
        fires — they're trying to work with a real project and the
        synthetic fallback will likely surprise them.
        """
        from rocq_mcp import server as _server

        f = markerless_dir / "foo.v"
        f.write_text("")
        # Point ROCQ_WORKSPACE at the markerless dir so the fall-through
        # chain (auto-detect None -> ROCQ_WORKSPACE) lands on it.
        monkeypatch.setattr(_server, "ROCQ_WORKSPACE", str(markerless_dir))

        self._setup_spies(monkeypatch)
        result = await _server.rocq_toc(file=str(f), ctx=_ctx)

        assert "workspace_warning" in result
        assert str(markerless_dir) in result["workspace_warning"]

    async def test_explicit_workspace_plus_file_hint_warns(
        self, markerless_dir, _ctx, monkeypatch
    ):
        """Covers the matrix cell where the caller supplies BOTH
        ``workspace=`` AND ``file=``.  Confirms that having ``file=`` does
        not short-circuit the ``explicit=True`` branch — the warning still
        fires because the resolved workspace lacks a marker.
        """
        from rocq_mcp import server as _server

        f = markerless_dir / "foo.v"
        f.write_text("")

        self._setup_spies(monkeypatch)
        result = await _server.rocq_toc(
            workspace=str(markerless_dir), file=str(f), ctx=_ctx
        )

        assert "workspace_warning" in result
        assert str(markerless_dir) in result["workspace_warning"]

    async def test_no_file_no_explicit_workspace_quiet(self, _ctx, monkeypatch):
        """A source-string tool with no file= and no explicit workspace=
        is quiet — that's the legitimate scratch / one-off workflow,
        not a config bug.
        """
        from rocq_mcp import server as _server

        # ROCQ_WORKSPACE is whatever the test env has; force a markerless
        # tmpdir to be sure.
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            monkeypatch.setattr(_server, "ROCQ_WORKSPACE", td)
            self._setup_spies(monkeypatch)
            result = await _server.rocq_compile(
                source="Theorem t : True. Proof. exact I. Qed.", ctx=_ctx
            )

        assert "workspace_warning" not in result


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

    def test_single_tactic(self):
        """Chain: root → tactic1."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = add_mock_state(None, None, step=0)
        s1 = add_mock_state(root, "intros.", step=1)
        tactics, complete = _reconstruct_tactic_path(s1)
        assert tactics == ["intros."]
        assert complete is True

    def test_multi_step_chain(self):
        """Chain: root → t1 → t2 → t3."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = add_mock_state(None, None, step=0)
        s1 = add_mock_state(root, "intros.", step=1)
        s2 = add_mock_state(s1, "induction n.", step=2)
        s3 = add_mock_state(s2, "reflexivity.", step=3)
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

        root = add_mock_state(None, None, step=0)
        tactics, complete = _reconstruct_tactic_path(root)
        assert tactics == []
        assert complete is True

    def test_branching_follows_parent_chain(self):
        """Two branches from root — each returns only its own path."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = add_mock_state(None, None, step=0)
        # Branch A
        a1 = add_mock_state(root, "intros.", step=1)
        a2 = add_mock_state(a1, "auto.", step=2)
        # Branch B
        b1 = add_mock_state(root, "intro n.", step=1)
        b2 = add_mock_state(b1, "lia.", step=2)

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

        root = add_mock_state(None, None, step=0)
        s1 = add_mock_state(root, "intros.", step=1)
        s2 = add_mock_state(s1, "auto.", step=2)
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

        s1 = add_mock_state(None, "intros.", step=0)
        # Manually create a cycle: s1's parent_id points to itself
        _state_table[s1].parent_id = s1
        tactics, complete = _reconstruct_tactic_path(s1)
        # Should terminate; chain is not complete (cycle detected before reaching root)
        assert isinstance(tactics, list)
        assert complete is False

    def test_completeness_flag_true(self):
        """A normal chain root->s1->s2 returns (tactics, True)."""
        from rocq_mcp.interactive import _reconstruct_tactic_path

        root = add_mock_state(None, None, step=0)
        s1 = add_mock_state(root, "t1.", step=1)
        s2 = add_mock_state(s1, "t2.", step=2)
        tactics, complete = _reconstruct_tactic_path(s2)
        assert tactics == ["t1.", "t2."]
        assert complete is True

    def test_completeness_flag_false_on_eviction(self):
        """When the root is evicted, returns (partial_tactics, False)."""
        from rocq_mcp.interactive import (
            _reconstruct_tactic_path,
            _state_table,
        )

        root = add_mock_state(None, None, step=0)
        s1 = add_mock_state(root, "intros.", step=1)
        s2 = add_mock_state(s1, "auto.", step=2)
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

    @pytest.mark.asyncio
    async def test_body_too_large(self, monkeypatch):
        """run_check with body exceeding ROCQ_MAX_SOURCE_SIZE returns error."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_check

        # Set a small source size limit for testing
        monkeypatch.setattr(srv, "ROCQ_MAX_SOURCE_SIZE", 100)

        # Create a state so that from_state lookup would succeed
        root = add_mock_state(None, None, step=0)

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

    def test_eviction_removes_oldest(self, monkeypatch):
        """When more states than _MAX_STATES are added, oldest are evicted."""
        import rocq_mcp.interactive as intermod

        monkeypatch.setattr(intermod, "_MAX_STATES", 5)

        ids = []
        for i in range(7):
            sid = add_mock_state(None, f"tactic_{i}.", step=i)
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
            sid = add_mock_state(None, f"tactic_{i}.", step=i)
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

    def test_lru_touch_keeps_active_state_alive(self, monkeypatch):
        """A state being actively queried via ``_state_get_or_error``
        survives eviction pressure from a parallel caller churning new
        states.  This is the two-sub-agents-different-files case: one
        agent parks on state N while the other adds many states; the
        parked state must NOT be evicted as long as it's being read."""
        import rocq_mcp.interactive as intermod
        from rocq_mcp.interactive import _state_get_or_error, _state_table

        monkeypatch.setattr(intermod, "_MAX_STATES", 5)

        # Agent A creates state 1 and keeps using it.
        parked = add_mock_state(None, "agent_a_intro.", step=0)

        # Agent B churns through many states, exceeding the cap.
        for i in range(8):
            add_mock_state(None, f"agent_b_step_{i}.", step=i)
            # Agent A touches its parked state between each of B's writes.
            entry, err = _state_get_or_error(parked)
            assert err is None
            assert entry is not None

        # The parked state must still be alive despite B writing 8 entries
        # against a cap of 5 — LRU promotion kept it from being evicted.
        assert parked in _state_table

    def test_lru_evicts_genuinely_oldest_unused(self, monkeypatch):
        """When no state is touched, eviction order matches insertion
        order (FIFO degenerate case of LRU)."""
        import rocq_mcp.interactive as intermod
        from rocq_mcp.interactive import _state_table

        monkeypatch.setattr(intermod, "_MAX_STATES", 3)

        ids = [add_mock_state(None, f"t_{i}.", step=i) for i in range(5)]
        # First two evicted, last three remain.
        assert ids[0] not in _state_table
        assert ids[1] not in _state_table
        for sid in ids[2:]:
            assert sid in _state_table


# =========================================================================
# _set_workspace_if_needed -- triggers _parse_project_flags side effect
# =========================================================================


class TestSetWorkspaceIfNeededDuneSideEffect:
    """The pet path must trigger _parse_project_flags so dune-derived
    _RocqProject is on disk before pet.set_workspace runs."""

    def test_writes_rocqproject_for_dune_workspace(self, tmp_path):
        """First call on a fresh dune workspace: _parse_project_flags
        runs (writing _RocqProject) before pet.set_workspace."""
        from rocq_mcp.server import _set_workspace_if_needed

        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        (tmp_path / "dune").write_text("(coq.theory (name only))\n")
        (tmp_path / "x.v").write_text("")
        # Pet stub records call ordering.
        order: list[str] = []

        class _MockPet:
            def set_workspace(self, debug=False, dir=None):
                order.append("set_workspace")
                # By the time pet.set_workspace runs, _RocqProject must
                # already be on disk so coq-lsp picks it up.
                assert (tmp_path / "_RocqProject").is_file()

        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(
                returncode=0, stdout="-Q _build/default/only only"
            )
            state: dict = {}
            _set_workspace_if_needed(_MockPet(), str(tmp_path), state)
        assert order == ["set_workspace"]
        assert (tmp_path / "_RocqProject").is_file()

    def test_idempotent_for_unchanged_workspace(self, tmp_path):
        """Repeat calls with the same workspace skip pet.set_workspace
        (and therefore the dune side effect runs only once)."""
        from rocq_mcp.server import _set_workspace_if_needed

        (tmp_path / "dune-project").write_text("(lang dune 3.8)\n")
        (tmp_path / "dune").write_text("(coq.theory (name only))\n")
        (tmp_path / "x.v").write_text("")
        calls: list = []

        class _MockPet:
            def set_workspace(self, debug=False, dir=None):
                calls.append(dir)

        with mock.patch("rocq_mcp.server.subprocess.run") as mock_run:
            mock_run.return_value = mock.Mock(
                returncode=0, stdout="-Q _build/default/only only"
            )
            state: dict = {}
            _set_workspace_if_needed(_MockPet(), str(tmp_path), state)
            _set_workspace_if_needed(_MockPet(), str(tmp_path), state)
        # Second call short-circuits via the current_workspace cache.
        assert len(calls) == 1


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

    @pytest.mark.asyncio
    async def test_body_within_limit(self, monkeypatch):
        """run_check with body within ROCQ_MAX_SOURCE_SIZE passes the size check."""
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import run_check

        monkeypatch.setattr(srv, "ROCQ_MAX_SOURCE_SIZE", 1000)

        root = add_mock_state(None, None, step=0)
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

        root = add_mock_state(None, None, step=0)
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

        root = add_mock_state(None, None, step=0)
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


# =========================================================================
# vo_rebuild_warning — .vo rebuild detection for rocq_compile_file
# =========================================================================


class TestVoRebuildHelpers:
    """Unit tests for the helper trio: snapshot / diff / count_sessions."""

    def test_diff_vo_mtimes_detects_modified(self):
        from rocq_mcp.server import _diff_vo_mtimes

        before = {"/a.vo": 1.0, "/b.vo": 2.0}
        after = {"/a.vo": 1.0, "/b.vo": 2.5}
        assert _diff_vo_mtimes(before, after) == ["/b.vo"]

    def test_diff_vo_mtimes_detects_new(self):
        from rocq_mcp.server import _diff_vo_mtimes

        before = {"/a.vo": 1.0}
        after = {"/a.vo": 1.0, "/c.vo": 9.0}
        assert _diff_vo_mtimes(before, after) == ["/c.vo"]

    def test_diff_vo_mtimes_ignores_deletions(self):
        from rocq_mcp.server import _diff_vo_mtimes

        before = {"/a.vo": 1.0, "/gone.vo": 2.0}
        after = {"/a.vo": 1.0}
        assert _diff_vo_mtimes(before, after) == []

    def test_diff_vo_mtimes_unchanged(self):
        from rocq_mcp.server import _diff_vo_mtimes

        before = {"/a.vo": 1.0}
        after = {"/a.vo": 1.0}
        assert _diff_vo_mtimes(before, after) == []

    def test_snapshot_vo_mtimes_finds_files(self, tmp_path):
        from rocq_mcp.server import _snapshot_vo_mtimes

        (tmp_path / "a.vo").write_text("x")
        sub = tmp_path / "sub"
        sub.mkdir()
        (sub / "b.vo").write_text("y")
        (sub / "ignored.txt").write_text("z")

        snap = _snapshot_vo_mtimes(tmp_path)
        assert snap is not None
        keys = {Path(k).name for k in snap.keys()}
        assert keys == {"a.vo", "b.vo"}

    def test_snapshot_vo_mtimes_prunes_hidden(self, tmp_path):
        from rocq_mcp.server import _snapshot_vo_mtimes

        (tmp_path / "a.vo").write_text("x")
        git = tmp_path / ".git"
        git.mkdir()
        (git / "skip.vo").write_text("y")

        snap = _snapshot_vo_mtimes(tmp_path)
        assert snap is not None
        keys = {Path(k).name for k in snap.keys()}
        assert keys == {"a.vo"}

    def test_snapshot_vo_mtimes_returns_none_over_cap(self, tmp_path, monkeypatch):
        from rocq_mcp import server as _server

        monkeypatch.setattr(_server, "_VO_SCAN_FILE_CAP", 2)
        for i in range(5):
            (tmp_path / f"f{i}.vo").write_text("x")

        assert _server._snapshot_vo_mtimes(tmp_path) is None

    def test_count_sessions_in_workspace_under_ws(self, tmp_path):
        from rocq_mcp.interactive import _state_add
        from rocq_mcp.server import _count_sessions_in_workspace

        f = tmp_path / "thm.v"
        f.write_text("")
        st = mock.MagicMock()
        st.proof_finished = False
        _state_add(
            state=st,
            file="thm.v",
            theorem="t",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            resolved_file=str(f.resolve()),
        )

        assert _count_sessions_in_workspace(tmp_path) == 1

    def test_count_sessions_in_workspace_outside_ws(self, tmp_path):
        from rocq_mcp.interactive import _state_add
        from rocq_mcp.server import _count_sessions_in_workspace

        other = tmp_path / "other"
        other.mkdir()
        f = other / "thm.v"
        f.write_text("")
        st = mock.MagicMock()
        st.proof_finished = False
        _state_add(
            state=st,
            file="thm.v",
            theorem="t",
            workspace=str(other),
            parent_id=None,
            tactic=None,
            step=0,
            resolved_file=str(f.resolve()),
        )

        ws = tmp_path / "ws"
        ws.mkdir()
        assert _count_sessions_in_workspace(ws) == 0


class TestVoRebuildWarning:
    """End-to-end: rocq_compile_file attaches vo_rebuild_warning iff
    rebuilt .vo files coincide with active sessions in the workspace.

    Stubs the actual coqc call via run_compile_file so we exercise only
    the snapshot/diff/warning wiring.
    """

    @pytest.fixture
    def _ctx(self):
        from tests.conftest import _MockContext

        return _MockContext({"pet_client": None, "pet_timeout": 30.0})

    @staticmethod
    def _stub_run_compile_file(monkeypatch, result=None):
        """Replace ``run_compile_file`` (the source of the coqc call) with
        a stub that returns *result* unchanged.  Patched on the
        compile_enrichment module because that's where it's looked up.
        """
        from rocq_mcp import compile_enrichment as _ce

        if result is None:
            result = {"success": True, "output": ""}

        def _stub(*_a, **_kw):
            return dict(result)

        monkeypatch.setattr(_ce, "run_compile_file", _stub)

    @staticmethod
    def _add_session(workspace: Path, file_under_ws: Path):
        """Register one interactive session whose resolved_file lives
        under *workspace*.
        """
        from rocq_mcp.interactive import _state_add

        st = mock.MagicMock()
        st.proof_finished = False
        _state_add(
            state=st,
            file=file_under_ws.name,
            theorem="t",
            workspace=str(workspace),
            parent_id=None,
            tactic=None,
            step=0,
            resolved_file=str(file_under_ws.resolve()),
        )

    async def test_no_rebuild_no_warning(self, tmp_path, _ctx, monkeypatch):
        """coqc succeeds without touching any .vo → no warning."""
        from rocq_mcp import server as _server

        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        f = tmp_path / "foo.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        # Pre-existing .vo that won't change between snapshots.
        (tmp_path / "stale.vo").write_text("x")

        # Even with an active session, no rebuild → quiet.
        self._add_session(tmp_path, f)
        self._stub_run_compile_file(monkeypatch)

        result = await _server.rocq_compile_file(
            file=str(f), workspace=str(tmp_path), ctx=_ctx
        )
        assert "vo_rebuild_warning" not in result

    async def test_rebuild_no_sessions_no_warning(self, tmp_path, _ctx, monkeypatch):
        """Rebuild detected, but no interactive session in workspace → quiet."""
        from rocq_mcp import server as _server

        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        f = tmp_path / "foo.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        snapshots = [
            {"/x.vo": 1.0},
            {"/x.vo": 2.0},  # mtime changed → "rebuilt"
        ]

        def _fake_snapshot(_ws):
            return snapshots.pop(0)

        monkeypatch.setattr(_server, "_snapshot_vo_mtimes", _fake_snapshot)
        self._stub_run_compile_file(monkeypatch)

        result = await _server.rocq_compile_file(
            file=str(f), workspace=str(tmp_path), ctx=_ctx
        )
        assert "vo_rebuild_warning" not in result

    async def test_rebuild_with_sessions_warning_present(
        self, tmp_path, _ctx, monkeypatch
    ):
        """Rebuild + active session in workspace → warning fires and
        names the workspace path and the session count.
        """
        from rocq_mcp import server as _server

        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        f = tmp_path / "foo.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        snapshots = [
            {"/x.vo": 1.0, "/y.vo": 1.0},
            {"/x.vo": 2.0, "/y.vo": 3.0},  # both rewritten → 2 rebuilt
        ]

        def _fake_snapshot(_ws):
            return snapshots.pop(0)

        monkeypatch.setattr(_server, "_snapshot_vo_mtimes", _fake_snapshot)
        self._stub_run_compile_file(monkeypatch)
        self._add_session(tmp_path, f)

        result = await _server.rocq_compile_file(
            file=str(f), workspace=str(tmp_path), ctx=_ctx
        )
        assert "vo_rebuild_warning" in result
        warning = result["vo_rebuild_warning"]
        assert str(tmp_path) in warning
        assert "1 interactive session(s)" in warning
        assert "2 .vo file(s)" in warning
        assert "rocq_start" in warning

    async def test_over_cap_quiet(self, tmp_path, _ctx, monkeypatch):
        """Workspace exceeds _VO_SCAN_FILE_CAP → snapshot returns None and
        the warning stays quiet even with mtime changes and active sessions.
        """
        from rocq_mcp import server as _server

        (tmp_path / "_RocqProject").write_text("-Q . M\n")
        f = tmp_path / "foo.v"
        f.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        # Cap to 2 .vo paths; create 5 to blow past it.
        monkeypatch.setattr(_server, "_VO_SCAN_FILE_CAP", 2)
        for i in range(5):
            (tmp_path / f"f{i}.vo").write_text("x")

        self._add_session(tmp_path, f)
        self._stub_run_compile_file(monkeypatch)

        result = await _server.rocq_compile_file(
            file=str(f), workspace=str(tmp_path), ctx=_ctx
        )
        assert "vo_rebuild_warning" not in result


# =========================================================================
# README documentation patterns smoke test
# =========================================================================


class TestReadmeUsagePatterns:
    """Catch accidental deletion of the §1.8 'Recommended usage patterns' sections.

    Pure docs assertion — no Rocq invocation.  If these sections are
    renamed deliberately, update this test.
    """

    def _readme_text(self) -> str:
        readme = Path(__file__).resolve().parent.parent / "README.md"
        return readme.read_text(encoding="utf-8")

    def test_recommended_patterns_section_present(self):
        readme = self._readme_text()
        assert "## Recommended usage patterns" in readme

    def test_multi_tactic_exploration_subsection_present(self):
        readme = self._readme_text()
        assert "Multi-tactic exploration" in readme
        # Canonical example references both tools.
        assert "rocq_check" in readme
        assert "rocq_step_multi" in readme

    def test_imports_and_scopes_subsection_present(self):
        readme = self._readme_text()
        assert "Imports and scopes in `rocq_query`" in readme
        # Names the parameter agents should reach for.
        assert "preamble=" in readme
