"""Tests for two-tier timeout mechanism."""

from __future__ import annotations

import pytest

from rocq_mcp.server import (
    _is_timeout_eligible,
    _compute_hard_timeout,
    _PET_TIMEOUT_GRACE,
)

# ---------------------------------------------------------------------------
# _is_timeout_eligible
# ---------------------------------------------------------------------------


class TestIsTimeoutEligible:
    """Test tactic eligibility for Rocq Timeout wrapping."""

    def test_normal_tactic(self):
        assert _is_timeout_eligible("auto.") is True

    def test_tactic_with_spaces(self):
        assert _is_timeout_eligible("  auto.  ") is True

    def test_bullet_dash(self):
        assert _is_timeout_eligible("- auto.") is False

    def test_bullet_plus(self):
        assert _is_timeout_eligible("+ auto.") is False

    def test_bullet_star(self):
        assert _is_timeout_eligible("* auto.") is False

    def test_no_dot(self):
        assert _is_timeout_eligible("auto") is False

    def test_brace_open(self):
        # "{ auto. }" does not end with "." — not eligible
        assert _is_timeout_eligible("{ auto. }") is False

    def test_brace_close(self):
        assert _is_timeout_eligible("}") is False

    def test_intros(self):
        assert _is_timeout_eligible("intros.") is True

    def test_complex_tactic(self):
        assert _is_timeout_eligible("rewrite IH; reflexivity.") is True

    def test_empty(self):
        assert _is_timeout_eligible("") is False

    def test_only_dot(self):
        assert _is_timeout_eligible(".") is True

    def test_numbered_goal(self):
        assert _is_timeout_eligible("1: auto.") is True

    def test_double_bullet(self):
        assert _is_timeout_eligible("-- auto.") is False

    def test_whitespace_before_bullet(self):
        assert _is_timeout_eligible("  - auto.") is False

    def test_semicolon_chain(self):
        assert _is_timeout_eligible("split; auto.") is True


# ---------------------------------------------------------------------------
# _compute_hard_timeout
# ---------------------------------------------------------------------------


class TestComputeHardTimeout:
    """Test hard timeout computation."""

    def test_default_grace(self):
        assert _compute_hard_timeout(30.0) == 30.0 + _PET_TIMEOUT_GRACE

    def test_small_timeout(self):
        assert _compute_hard_timeout(1.0) == 1.0 + _PET_TIMEOUT_GRACE

    def test_zero(self):
        assert _compute_hard_timeout(0.0) == _PET_TIMEOUT_GRACE
