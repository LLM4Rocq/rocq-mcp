"""Cross-tool unified envelope contract.

Every pet-touching tool emits the same failure envelope:
``{success: False, error: str, reason: str, ...}``.  This file pins
that contract by exercising one well-known failure mode against
*each* tool and asserting the shape, so a regression where one tool
silently drops ``reason`` (or reverts to a legacy field like
``verified``) gets caught here, not several months later when an
agent fails to handle the response.

The pet-touching tools covered:

- ``rocq_query``        — invalid command (live PetanqueError)
- ``rocq_assumptions``  — missing file parameter
- ``rocq_check``        — body too large
- ``rocq_step_multi``   — missing tactics list
- ``rocq_start``        — invalid theorem identifier

The coqc-based tools (``rocq_compile`` / ``rocq_compile_file`` /
``rocq_verify``) are covered by their own existing envelope tests
(``TestVerifyEnvelopeContract`` in test_verify.py and the various
``state_capture_status`` tests in test_compile.py); they go through
a different code path (no ``_run_with_pet`` wrapper) so duplicating
them here would not provide additional coverage.
"""

from __future__ import annotations

import pytest

from rocq_mcp.interactive import (
    run_assumptions,
    run_check,
    run_query,
    run_start,
    run_step_multi,
)
from tests.conftest import make_lifespan_state

# Required keys on every failure envelope.  ``reason`` is required
# because that's what agents key on to decide retry / recovery
# strategy; without it a "validation" failure looks identical to a
# pet crash.
_ENVELOPE_REQUIRED_FAILURE_KEYS = {"success", "error", "reason"}

# Legacy keys that must NEVER appear on a v2 response.  Catches the
# specific drift the audit flagged on rocq_verify before the §4
# migration.
_ENVELOPE_FORBIDDEN_KEYS = {"verified"}


def _assert_failure_envelope(result: dict, *, expected_reason: str | None = None):
    """Assert *result* matches the unified failure envelope contract."""
    assert isinstance(result, dict), f"non-dict response: {result!r}"
    assert result.get("success") is False
    missing = _ENVELOPE_REQUIRED_FAILURE_KEYS - set(result)
    assert not missing, f"envelope missing required keys: {missing!r}"
    forbidden = _ENVELOPE_FORBIDDEN_KEYS & set(result)
    assert not forbidden, f"envelope contains forbidden legacy keys: {forbidden!r}"
    assert isinstance(result["error"], str) and result["error"]
    assert isinstance(result["reason"], str) and result["reason"]
    if expected_reason is not None:
        assert (
            result["reason"] == expected_reason
        ), f"reason {result['reason']!r} != expected {expected_reason!r}"


class TestUnifiedFailureEnvelope:
    """One canonical failure per pet-touching tool — same envelope shape."""

    @pytest.mark.asyncio
    async def test_run_assumptions_validation_failure(self):
        """Empty file parameter → validation failure with the unified envelope."""
        ls = make_lifespan_state()
        ls["recent_errors"] = __import__("collections").deque(maxlen=10)
        result = await run_assumptions(
            name="thm",
            file="",
            workspace="/tmp",
            lifespan_state=ls,
        )
        _assert_failure_envelope(result, expected_reason="validation")

    @pytest.mark.asyncio
    async def test_run_query_validation_failure(self):
        """file + from_state → validation failure with the unified envelope."""
        ls = make_lifespan_state()
        ls["recent_errors"] = __import__("collections").deque(maxlen=10)
        result = await run_query(
            command="Check 1.",
            preamble="",
            workspace="/tmp",
            lifespan_state=ls,
            file="x.v",
            from_state=42,
        )
        _assert_failure_envelope(result, expected_reason="validation")

    @pytest.mark.asyncio
    async def test_run_check_oversize_failure(self):
        """Body over the size cap → validation failure with the unified envelope."""
        from rocq_mcp.server import ROCQ_MAX_SOURCE_SIZE

        ls = make_lifespan_state()
        ls["recent_errors"] = __import__("collections").deque(maxlen=10)
        result = await run_check(
            body="x" * (ROCQ_MAX_SOURCE_SIZE + 1),
            timeout=30.0,
            lifespan_state=ls,
        )
        _assert_failure_envelope(result, expected_reason="validation")

    @pytest.mark.asyncio
    async def test_run_step_multi_validation_failure(self):
        """Empty tactics list → validation failure with the unified envelope."""
        ls = make_lifespan_state()
        ls["recent_errors"] = __import__("collections").deque(maxlen=10)
        result = await run_step_multi(
            tactics=[],
            lifespan_state=ls,
        )
        _assert_failure_envelope(result, expected_reason="validation")

    @pytest.mark.asyncio
    async def test_run_start_validation_failure(self):
        """Empty file + empty preamble → validation failure with the unified
        envelope.  rocq_start requires at least one of the two."""
        ls = make_lifespan_state()
        ls["recent_errors"] = __import__("collections").deque(maxlen=10)
        result = await run_start(
            file="",
            theorem="",
            workspace="/tmp",
            lifespan_state=ls,
            preamble="",
        )
        _assert_failure_envelope(result, expected_reason="validation")
