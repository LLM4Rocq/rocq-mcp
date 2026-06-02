"""Operational diagnostics — backing logic for the rocq_diag tool.

Builds a read-only snapshot of pet uptime, memory headroom, live state-
table entries, and recent error history.  The MCP tool wrapper
(``rocq_diag``) lives in :mod:`rocq_mcp.server`; this module provides
the snapshot builder it delegates to.
"""

from __future__ import annotations

import time
from typing import Any, Literal

import psutil

import rocq_mcp as _rocq_mcp  # for __version__
import rocq_mcp.server as _server
from rocq_mcp.interactive import _state_table

# Maximum number of ``live_states`` entries returned by ``rocq_diag``.
# Caps the response payload; ``live_states_total`` reports the full count.
_DIAG_LIVE_STATES_CAP: int = 50


_RssSampleStatus = Literal["ok", "no_pet", "psutil_error"]


def _sample_pet_rss_mb(
    lifespan_state: dict[str, Any],
) -> tuple[float | None, _RssSampleStatus]:
    """Best-effort live RSS sample of the pet subprocess.

    Returns a ``(rss_mb, status)`` tuple where *status* discriminates the
    ``rss_mb is None`` cases:

    - ``"ok"``: psutil returned a sample; ``rss_mb`` is the live RSS in MB.
    - ``"no_pet"``: pet is not running (no ``pet_client`` or no
      ``.process``); no sample was attempted.
    - ``"psutil_error"``: psutil raised (NoSuchProcess / AccessDenied /
      ZombieProcess / OSError / AttributeError); ``rss_mb`` is ``None``.
    """
    client = lifespan_state.get("pet_client")
    if client is None or getattr(client, "process", None) is None:
        return None, "no_pet"
    try:
        pid = client.process.pid
        rss_bytes = psutil.Process(pid).memory_info().rss
    except (psutil.Error, AttributeError, OSError):
        return None, "psutil_error"
    return rss_bytes / (1024 * 1024), "ok"


def _build_diag_snapshot(lifespan_state: dict[str, Any]) -> dict[str, Any]:
    """Build the response dict for the ``rocq_diag`` tool.

    Reads diagnostic state without spawning pet.  See ``rocq_diag`` for the
    output schema.  ``recent_errors`` entries are converted from the deque's
    ``occurred_at`` timestamp to a relative ``ago_seconds`` here so values
    stay fresh on every call.

    ``live_states`` is capped at :data:`_DIAG_LIVE_STATES_CAP` (most recent
    by ``created_at``); ``live_states_total`` reports the full count.
    """
    now = time.time()
    client = lifespan_state.get("pet_client")
    pet_pid: int | None = None
    if client is not None and getattr(client, "process", None) is not None:
        pet_pid = client.process.pid

    started = lifespan_state.get("pet_started_at")
    if started is None or pet_pid is None:
        uptime = 0.0
    else:
        uptime = max(0.0, now - float(started))

    pet_rss_mb, sample_status = _sample_pet_rss_mb(lifespan_state)
    peak = float(lifespan_state.get("peak_pet_rss_mb", 0.0) or 0.0)

    # Sort by created_at descending (most recent first), then take cap.
    all_entries = list(_state_table.items())
    all_entries.sort(key=lambda kv: getattr(kv[1], "created_at", 0.0), reverse=True)
    live_states_total = len(all_entries)
    capped_entries = all_entries[:_DIAG_LIVE_STATES_CAP]

    live_states: list[dict[str, Any]] = []
    for sid, entry in capped_entries:
        created = getattr(entry, "created_at", now)
        age = max(0.0, now - created)
        live_states.append(
            {
                "state_id": sid,
                "parent": getattr(entry, "parent_id", None),
                "file": getattr(entry, "file", None) or None,
                "theorem": getattr(entry, "theorem", None) or None,
                "age_seconds": age,
            }
        )

    raw_errors = lifespan_state.get("recent_errors") or []
    recent_errors: list[dict[str, Any]] = []
    for entry in raw_errors:
        occurred = float(entry.get("occurred_at", now))
        recent_errors.append(
            {
                "tool": entry.get("tool"),
                "message": entry.get("message"),
                "reason": entry.get("reason"),
                "ago_seconds": max(0.0, now - occurred),
            }
        )

    total_spawns = int(lifespan_state.get("total_spawns", 0))
    return {
        "success": True,
        "server_version": _rocq_mcp.__version__,
        "pet": {
            "pid": pet_pid,
            "uptime_seconds": uptime,
            "restarts": max(0, total_spawns - 1),
            "generation": int(lifespan_state.get("pet_generation", 0)),
        },
        "memory": {
            "pet_rss_mb": pet_rss_mb,
            "peak_pet_rss_mb": peak,
            "max_rss_mb_threshold": float(_server.ROCQ_MAX_PET_RSS_MB),
            "sample_status": sample_status,
        },
        "live_states": live_states,
        "live_states_total": live_states_total,
        "recent_errors": recent_errors,
    }
