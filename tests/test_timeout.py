"""Tests for two-tier timeout mechanism."""

from __future__ import annotations

import threading
import time

import pytest

import rocq_mcp.server as _server
from rocq_mcp.interactive import (
    _is_timeout_eligible,
    _compute_hard_timeout,
    _PET_TIMEOUT_GRACE,
)
from rocq_mcp.server import _run_with_pet
from tests.conftest import (
    make_lifespan_state,
    mock_pet as _mock_pet,
    patch_psutil_rss as _patch_psutil_rss,
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


# ---------------------------------------------------------------------------
# Timeout error message — actionable retry hint
# ---------------------------------------------------------------------------


class TestTimeoutErrorHint:
    """The pet timeout error string must include an actionable retry hint
    that names the per-call ``timeout=`` arg and the env-var cap."""

    @pytest.fixture(autouse=True)
    def _reset_pet_state(self, monkeypatch):
        _server._pet_semaphore = None
        monkeypatch.setattr(_server, "_pet_lock", threading.Lock())
        yield
        _server._pet_semaphore = None

    @pytest.fixture(autouse=True)
    def _fast_watchdog(self, monkeypatch):
        monkeypatch.setattr(_server, "_MEMORY_WATCHDOG_INTERVAL", 0.01)

    @pytest.mark.asyncio
    async def test_timeout_error_includes_retry_hint(self, monkeypatch):
        """When _run_with_pet times out, the error string includes
        ``Retry with`` so agents see the actionable knob name."""
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)

        pet = _mock_pet()
        ls = make_lifespan_state(pet_timeout=0.05, full=True)
        ls["pet_client"] = pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: pet)
        monkeypatch.setattr(
            _server,
            "_invalidate_pet",
            lambda lstate: lstate.update(pet_client=None),
        )

        def fn_slow(p):
            time.sleep(1.0)
            return {"success": True}

        result = await _run_with_pet(fn_slow, ls, "rocq_check")
        # Envelope contract:
        assert result["success"] is False
        assert isinstance(result.get("error"), str)
        assert result["reason"] == "timeout"
        assert result["pet_restarted"] is True
        # Actionable hint substrings (load-bearing pieces, not the
        # illustrative timeout value):
        assert "Retry with" in result["error"]
        assert "rocq_check(..., timeout=" in result["error"]
        assert "ROCQ_PET_TIMEOUT" in result["error"]
        assert "ROCQ_QUERY_TIMEOUT_CAP" in result["error"]
