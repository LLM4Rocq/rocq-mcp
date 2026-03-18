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

    def test_large_warnings_before_error(self):
        """Error after 6000+ bytes of warnings must still be found."""
        warning_line = (
            'File "/tmp/tmp.v", line 2, characters 0-75:\n'
            "Warning: Notation overridden.\n"
        )
        warnings = warning_line * 100  # ~7000 bytes of warnings
        error = (
            'File "/tmp/tmp.v", line 50, characters 0-10:\n'
            "Error: The reference foo was not found.\n"
        )
        proof = "\n".join(f"line {i}" for i in range(60))
        result = _format_error(warnings + error, proof)
        assert "Error:" in result
        assert "foo was not found" in result

    def test_duplicate_warnings_deduplicated(self):
        """Identical warnings emitted multiple times should appear only once."""
        proof = "line 0\nline 1\nline 2\nline 3\n"
        # Same warning 3 times, then an error
        warn = (
            'File "/tmp/tmp.v", line 2, characters 0-10:\n'
            "Warning: Notation Nat.mul_mod is deprecated.\n"
        )
        error = (
            'File "/tmp/tmp.v", line 4, characters 0-10:\n' "Error: Tactic failure.\n"
        )
        stderr = warn * 3 + error
        result = _format_error(stderr, proof)
        assert "Error:" in result
        # The warning should appear exactly once, not three times
        assert result.count("Nat.mul_mod") == 1

    def test_distinct_warnings_preserved(self):
        """Different warnings before an error should all be kept."""
        proof = "line 0\nline 1\nline 2\nline 3\n"
        warn_a = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n' "Warning: Deprecated A.\n"
        )
        warn_b = (
            'File "/tmp/tmp.v", line 2, characters 0-5:\n' "Warning: Deprecated B.\n"
        )
        error = 'File "/tmp/tmp.v", line 3, characters 0-5:\n' "Error: Real error.\n"
        result = _format_error(warn_a + warn_b + error, proof)
        assert "Deprecated A" in result
        assert "Deprecated B" in result
        assert "Error:" in result

    def test_include_warnings_false_strips_warnings(self):
        """With include_warnings=False, only the error is returned."""
        proof = "Line 0\nLine 1\nLine 2\n"
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Warning: Something deprecated.\n"
            'File "/tmp/tmp.v", line 2, characters 0-5:\n'
            "Warning: Another deprecation.\n"
            'File "/tmp/tmp.v", line 3, characters 0-5:\n'
            "Error: Real error.\n"
        )
        result = _format_error(stderr, proof, include_warnings=False)
        assert "Real error" in result
        assert "Warning" not in result
        assert "deprecated" not in result

    def test_include_warnings_true_is_default(self):
        """Default behavior includes warnings before the error."""
        proof = "Line 0\nLine 1\nLine 2\n"
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-5:\n'
            "Warning: Something deprecated.\n"
            'File "/tmp/tmp.v", line 2, characters 0-5:\n'
            "Error: Real error.\n"
        )
        result = _format_error(stderr, proof)
        assert "deprecated" in result
        assert "Real error" in result

    def test_include_warnings_false_pure_warnings_still_empty(self):
        """Pure warnings with no error still return empty regardless of flag."""
        proof = "Theorem t : True. Proof. exact I. Qed."
        stderr = (
            'File "/tmp/tmp.v", line 1, characters 0-10:\n'
            "Warning: Deprecated feature.\n"
        )
        assert _format_error(stderr, proof, include_warnings=False) == ""
        assert _format_error(stderr, proof, include_warnings=True) == ""

    def test_excess_unique_warnings_capped(self):
        """At most _MAX_FORMAT_WARNINGS unique warnings are included."""
        from rocq_mcp.server import _MAX_FORMAT_WARNINGS

        proof = "\n".join(f"line {i}" for i in range(20))
        # Generate more unique warnings than the cap
        warnings = "".join(
            f'File "/tmp/tmp.v", line {i}, characters 0-5:\n'
            f"Warning: Unique warning {i}.\n"
            for i in range(10)
        )
        error = (
            'File "/tmp/tmp.v", line 15, characters 0-5:\n' "Error: The actual error.\n"
        )
        result = _format_error(warnings + error, proof)
        assert "The actual error" in result
        # Only the first _MAX_FORMAT_WARNINGS unique warnings should appear
        included = sum(1 for i in range(10) if f"Unique warning {i}" in result)
        assert included == _MAX_FORMAT_WARNINGS

    def test_structured_output_bounded(self):
        """Structured diagnostics output must be bounded to _MAX_ERROR_LENGTH."""
        from rocq_mcp.server import _MAX_ERROR_LENGTH

        proof = "\n".join(f"line {i}" for i in range(200))
        # Even with warnings within the count cap, a huge error body
        # should be capped
        error_body = "Error: " + "x" * (_MAX_ERROR_LENGTH * 2)
        stderr = f'File "/tmp/tmp.v", line 1, characters 0-5:\n{error_body}\n'
        result = _format_error(stderr, proof)
        assert len(result) <= _MAX_ERROR_LENGTH

    def test_no_diagnostics_output_capped(self):
        """Unstructured stderr must be capped to avoid drowning LLM context."""
        from rocq_mcp.server import _MAX_ERROR_LENGTH

        huge = "x" * (_MAX_ERROR_LENGTH * 3)
        result = _format_error(huge, "proof")
        assert len(result) <= _MAX_ERROR_LENGTH
