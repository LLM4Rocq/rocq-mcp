"""Tests for _format_error LLM-friendly error formatting."""

from __future__ import annotations

from rocq_mcp.server import _format_error


class TestFormatError:
    """Test _format_error output formatting."""

    def test_empty_input(self):
        assert _format_error("", "some proof") == ""

    def test_single_error_with_annotation(self):
        proof = "Theorem t : True.\nProof.\n  exact 42.\nQed."
        stderr = (
            'File "/tmp/tmpXXXXXX.v", line 3, characters 2-10:\n'
            'Error: The term "42" has type "nat" but expected "True".\n'
        )
        result = _format_error(stderr, proof)
        assert "<proof>" in result
        assert "tmpXXXXXX" not in result
        assert "exact 42." in result  # source line shown
        assert "^" in result  # caret underline
        assert "Error:" in result

    def test_pure_warnings_suppressed(self):
        proof = "Theorem t : True. Proof. exact I. Qed."
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-10:\n'
            "Warning: Deprecated feature.\n"
        )
        result = _format_error(stderr, proof)
        assert result == ""

    def test_warning_before_error_included(self):
        proof = "Line 0\nLine 1\nLine 2\n"
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Warning: Something deprecated.\n"
            'File "/tmp/tmp.v", line 2, characters 0-5:\n'
            "Error: Real error.\n"
        )
        result = _format_error(stderr, proof)
        assert "Warning" in result
        assert "Error" in result

    def test_no_structured_location_fallback(self):
        proof = "some proof"
        stderr = 'Failed to run coqc on "/tmp/tmpABCDEF.v": not found'
        result = _format_error(stderr, proof)
        assert "<proof>" in result
        assert "tmpABCDEF" not in result

    def test_tmp_path_replaced(self):
        proof = "Theorem t : True."
        stderr = (
            'File "/tmp/tmpXYZ123.v", line 1, characters 0-5:\n'
            "Error: Syntax error.\n"
        )
        result = _format_error(stderr, proof)
        assert "tmpXYZ123" not in result
        assert "<proof>" in result

    def test_caret_position(self):
        proof = "  exact (foo bar)."
        stderr = 'File "/tmp/tmp.v", line 1, characters 8-17:\n' "Error: Wrong type.\n"
        result = _format_error(stderr, proof)
        assert "^" in result
        assert "exact (foo bar)." in result

    def test_line_out_of_range(self):
        """Error pointing to line beyond proof should format without crash."""
        proof = "Line 0\n"
        stderr = 'File "/tmp/tmp.v", line 99, characters 0-5:\n' "Error: Some error.\n"
        result = _format_error(stderr, proof)
        assert "Error:" in result

    def test_multiple_errors_only_first(self):
        """Only include up to the first Error, not subsequent ones."""
        proof = "Line 0\nLine 1\nLine 2\n"
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Error: First error.\n"
            'File "/tmp/tmp.v", line 3, characters 0-5:\n'
            "Error: Second error.\n"
        )
        result = _format_error(stderr, proof)
        assert "First error" in result
        assert "Second error" not in result

    def test_multiline_error_body(self):
        proof = "Theorem t : nat.\nProof. exact 0. Qed."
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-10:\n'
            "Error: In environment\n"
            "Unable to unify.\n"
        )
        result = _format_error(stderr, proof)
        assert "In environment" in result
