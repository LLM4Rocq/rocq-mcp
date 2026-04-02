"""Tests for _truncate_result utility and feedback collection in run_check."""

from __future__ import annotations

from rocq_mcp.interactive import _truncate_result, _MAX_FEEDBACK_LENGTH


class TestTruncateResult:
    """Unit tests for _truncate_result."""

    def test_short_text_unchanged(self):
        """Text shorter than max_length passes through unchanged."""
        text = "hello world"
        assert _truncate_result(text, 100) == text

    def test_exact_length_unchanged(self):
        """Text exactly at max_length passes through unchanged."""
        text = "x" * 50
        assert _truncate_result(text, 50) == text

    def test_over_limit_truncated(self):
        """Text exceeding max_length is truncated with notice."""
        text = "a" * 200
        result = _truncate_result(text, 100)
        assert result.startswith("a" * 100)
        assert "truncated" in result
        assert "200 total chars" in result

    def test_truncation_preserves_prefix(self):
        """The first max_length chars of the original are preserved."""
        text = "ABCDE" + "x" * 1000
        result = _truncate_result(text, 5)
        assert result.startswith("ABCDE")
        assert "truncated" in result

    def test_empty_string(self):
        """Empty string passes through unchanged."""
        assert _truncate_result("", 100) == ""

    def test_large_vm_compute_style_output(self):
        """Simulates large vm_compute output (the motivating use case)."""
        # vm_compute can produce megabytes of output
        huge = "0" * 6_500_000  # 6.5M chars
        result = _truncate_result(huge, _MAX_FEEDBACK_LENGTH)
        assert len(result) < _MAX_FEEDBACK_LENGTH + 200  # room for notice
        assert result.startswith("0" * _MAX_FEEDBACK_LENGTH)
        assert "6500000 total chars" in result

    def test_max_feedback_length_constant(self):
        """Verify the constant is set to the expected value."""
        assert _MAX_FEEDBACK_LENGTH == 50_000
