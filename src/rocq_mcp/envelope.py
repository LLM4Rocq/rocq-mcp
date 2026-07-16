"""Failure-envelope construction and degraded-enrichment reporting.

Two related responsibilities, both about *how the server reports trouble*:

1. The failure envelope: ``_fail`` / ``_record_error`` / ``_no_ctx_fail``
   build the canonical ``{success: False, error, reason}`` response and
   feed the ``recent_errors`` ring buffer that ``rocq_diag`` exposes.

2. Degraded-enrichment notes: many response fields are *best-effort*
   (goals at an error position, ``available_in_file`` suggestions, focus
   depth...).  Historically their failures were swallowed into
   ``None``/``[]``, invisible to agents and operators alike.  The
   ``collect_degraded`` / ``note_degraded`` pair makes them visible: a
   swallow site records a stable ``"<field>:<code>"`` note, and the
   owning ``run_*`` attaches ``degraded: [codes]`` to an otherwise-normal
   response (the key is absent when nothing degraded).  Full exception
   text is only attached under ``ROCQ_DEBUG_ENRICHMENT=1`` to keep
   payloads bounded.

Imports nothing from :mod:`rocq_mcp.server` (leaf-ish module; depends
only on :mod:`rocq_mcp.taxonomy`).
"""

from __future__ import annotations

import functools
import os
import time
from contextvars import ContextVar
from typing import Any

from rocq_mcp.taxonomy import RECENT_ERROR_REASONS

_RECENT_ERROR_MESSAGE_LIMIT: int = 500

# ---------------------------------------------------------------------------
# Failure envelope
# ---------------------------------------------------------------------------


def _record_error(
    lifespan_state: dict[str, Any] | None,
    tool: str,
    message: str,
    reason: str,
) -> None:
    """Append an entry to the ``recent_errors`` ring buffer.

    Stores absolute ``occurred_at`` timestamps; ``ago_seconds`` is computed
    lazily by ``_build_diag_snapshot`` so values stay fresh when the buffer
    is read.

    *tool* is the canonical MCP tool name (e.g. ``"rocq_check"``) and
    matches the output schema key in ``_build_diag_snapshot``.

    *reason* must be a :class:`rocq_mcp.taxonomy.FailureReason` value —
    asserted here so a typo'd reason fails at the call site instead of
    silently appearing in ``rocq_diag`` output and breaking agent dispatch.

    Long *message* strings are truncated to
    ``_RECENT_ERROR_MESSAGE_LIMIT`` chars + ``"..."`` to keep the
    ``rocq_diag`` payload bounded; the full message is preserved in the
    immediate response of the failing tool call.

    Tolerates ``lifespan_state is None`` (no recording) and missing
    ``recent_errors`` key (no recording) — both happen when the failing
    tool call has no MCP context.
    """
    assert (
        reason in RECENT_ERROR_REASONS
    ), f"unknown error reason {reason!r}; add it to taxonomy.FailureReason"
    if lifespan_state is None:
        return
    buf = lifespan_state.get("recent_errors")
    if buf is None:
        return
    if message is not None and len(message) > _RECENT_ERROR_MESSAGE_LIMIT:
        message = message[:_RECENT_ERROR_MESSAGE_LIMIT] + "..."
    buf.append(
        {
            "tool": tool,
            "message": message,
            "reason": reason,
            "occurred_at": time.time(),
        }
    )


def _fail(
    lifespan_state: dict[str, Any] | None,
    tool: str,
    message: str,
    reason: str = "validation",
    **extra: Any,
) -> dict[str, Any]:
    """Build a failure response dict and record it in ``recent_errors``.

    Convenience for the ``return {"success": False, "error": msg}`` pattern
    that also needs to push the error onto the diag ring buffer.  Skips
    recording when *lifespan_state* is ``None`` (no MCP context) so test
    helpers and pre-context paths stay simple.

    Always includes ``reason`` in the response so the unified envelope
    is consistent across pet-side failures (set by ``_run_with_pet``)
    and pre-pet validation failures (set here).
    """
    _record_error(lifespan_state, tool=tool, message=message, reason=reason)
    return {"success": False, "error": message, "reason": reason, **extra}


def _no_ctx_fail(tool: str) -> dict[str, Any]:
    """Canonical "no MCP context" failure envelope for tool wrappers.

    Routes through :func:`_fail` so the response shape and the
    ``recent_errors`` side-effect policy stay defined in one place; when
    ``ctx is None`` we have no ``lifespan_state`` to record into, so
    ``_fail`` no-ops the buffer write (same policy as every other
    ``lifespan_state is None`` caller).
    """
    return _fail(None, tool, "Internal error: no MCP context.")


# ---------------------------------------------------------------------------
# Degraded-enrichment notes
# ---------------------------------------------------------------------------

#: Per-call accumulator.  ``None`` outside any collecting scope, so
#: ``note_degraded`` is a safe no-op for helpers invoked from paths that
#: don't collect (tests calling helpers directly, future callers...).
#: ``asyncio.to_thread`` copies the caller's context, and the copy holds
#: a reference to the *same* payload dict — so notes recorded inside
#: ``_run_with_pet``'s worker thread are visible to the owning ``run_*``.
_degraded: ContextVar[dict[str, Any] | None] = ContextVar(
    "rocq_mcp_degraded", default=None
)


def note_degraded(code: str, detail: str | None = None) -> None:
    """Record that a best-effort enrichment step failed.

    *code* is a stable machine string, format ``"<field>:<what>"``
    (e.g. ``"goals:pet_call_failed"``).  *detail* (typically ``repr(e)``)
    is kept only when ``ROCQ_DEBUG_ENRICHMENT=1`` — see
    :func:`attach_degraded`.

    No-op outside a :func:`collect_degraded` scope.
    """
    payload = _degraded.get()
    if payload is None:
        return
    if code not in payload["codes"]:
        payload["codes"].append(code)
    if detail and code not in payload["details"]:
        payload["details"][code] = detail[:500]


def _debug_enrichment_enabled() -> bool:
    return os.environ.get("ROCQ_DEBUG_ENRICHMENT", "") not in ("", "0")


def attach_degraded(result: Any, lifespan_state: dict[str, Any] | None = None) -> Any:
    """Attach collected degraded notes to *result* (a response dict).

    Adds ``degraded: [codes]`` only when at least one note was recorded
    (mirrors the optionality convention of ``workspace_warning``), plus
    ``degraded_detail`` under ``ROCQ_DEBUG_ENRICHMENT=1``.  Also bumps
    the per-code counters surfaced by ``rocq_diag`` as
    ``enrichment_failures``.
    """
    payload = _degraded.get()
    if payload is None or not payload["codes"] or not isinstance(result, dict):
        return result
    result.setdefault("degraded", list(payload["codes"]))
    if _debug_enrichment_enabled() and payload["details"]:
        result.setdefault("degraded_detail", dict(payload["details"]))
    if lifespan_state is not None:
        counters = lifespan_state.get("enrichment_failures")
        if isinstance(counters, dict):
            for code in payload["codes"]:
                counters[code] = counters.get(code, 0) + 1
    return result


def collects_degraded(fn: Any) -> Any:
    """Decorator for ``run_*`` implementations: scope + attach in one.

    Opens a fresh collection scope for the duration of the call and, if
    any notes were recorded, attaches them to the returned dict.  Reads
    ``lifespan_state`` from the wrapped function's kwargs for the
    ``enrichment_failures`` counters (all ``run_*`` take it as a kwarg).
    """

    @functools.wraps(fn)
    async def wrapper(*args: Any, **kwargs: Any) -> Any:
        payload: dict[str, Any] = {"codes": [], "details": {}}
        token = _degraded.set(payload)
        try:
            result = await fn(*args, **kwargs)
        finally:
            _degraded.reset(token)
        # Attach after reset using the captured payload: set the var
        # briefly again so attach_degraded sees it.
        token = _degraded.set(payload)
        try:
            return attach_degraded(result, kwargs.get("lifespan_state"))
        finally:
            _degraded.reset(token)

    return wrapper
