"""Tests for position-based session start and coqc error position parsing."""

from __future__ import annotations

import pytest

from rocq_mcp.server import _parse_coqc_error_positions


# ---------------------------------------------------------------------------
# _parse_coqc_error_positions
# ---------------------------------------------------------------------------


class TestParseCoqcErrorPositions:
    """Test coqc stderr error position parsing."""

    def test_single_error(self):
        stderr = (
            'File "/tmp/foo.v", line 15, characters 2-5:\n'
            "Error: Unable to unify something.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        p = positions[0]
        assert p["line"] == 14  # 0-based
        assert p["character"] == 2
        assert p["end_character"] == 5
        assert "Unable to unify" in p["message"]

    def test_multiple_errors(self):
        stderr = (
            'File "/tmp/foo.v", line 3, characters 0-10:\n'
            "Error: First error.\n"
            'File "/tmp/foo.v", line 7, characters 4-8:\n'
            "Error: Second error.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 2
        assert positions[0]["line"] == 2
        assert positions[1]["line"] == 6

    def test_no_position(self):
        stderr = "Some random error without position info\n"
        positions = _parse_coqc_error_positions(stderr)
        assert positions == []

    def test_empty_stderr(self):
        assert _parse_coqc_error_positions("") == []

    def test_warning_parsed(self):
        stderr = (
            'File "/tmp/foo.v", line 1, characters 0-20:\n'
            "Warning: Deprecated feature.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert "Deprecated" in positions[0]["message"]

    def test_multiline_error_message(self):
        stderr = (
            'File "/tmp/foo.v", line 5, characters 10-15:\n'
            "Error: In environment\n"
            "n : nat\n"
            "Unable to unify something with something else.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert "In environment" in positions[0]["message"]

    def test_message_truncated(self):
        long_msg = "Error: " + "x" * 600
        stderr = (
            'File "/tmp/foo.v", line 1, characters 0-5:\n'
            f"{long_msg}\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert len(positions[0]["message"]) <= 500

    def test_line_conversion_1based_to_0based(self):
        """Line 1 in coqc → line 0 for pytanque."""
        stderr = (
            'File "/tmp/foo.v", line 1, characters 0-3:\n'
            "Error: Syntax error.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert positions[0]["line"] == 0
