"""Compile-error-state orchestration.

Wraps the coqc-only ``run_compile`` / ``run_compile_file`` from
:mod:`rocq_mcp.compile` with best-effort PET state capture at the
error position.  Lives in its own module (not in ``compile.py``) so
that ``compile.py`` stays free of any pytanque dependency for its
core operation.
"""

from __future__ import annotations

import os
import tempfile
from pathlib import Path
from typing import Any, Literal, TypedDict, get_args

import rocq_mcp.server as _server
from rocq_mcp.compile import (
    _PROOF_FILE_LABEL,
    _first_error_from_positions,
    run_compile,
    run_compile_file,
)

from rocq_mcp.proof_walk import ProofError, collect_file_errors

# Cap on how long enrichment may spend per call.  Coqc has already returned
# the basic error by the time we reach this code, so a stuck pet must not
# silently steal more than this from the agent.
_ENRICHMENT_TIMEOUT_CAP: float = float(
    os.environ.get("ROCQ_ENRICHMENT_TIMEOUT_CAP", "5.0")
)

# Outer wall-clock ceiling on the multi-error walker, expressed as a multiple
# of ``_ENRICHMENT_TIMEOUT_CAP``.  Under default config (cap=20, per-call=5s)
# the naive ``per_call_timeout * cap + per_call_timeout`` would be 105s; the
# ``min`` against ``_ENRICHMENT_TIMEOUT_CAP * _WALKER_BUDGET_MULTIPLIER``
# bounds the actual budget to 20s.  Set higher only if you have lifted
# ``ROCQ_ENRICHMENT_TIMEOUT_CAP`` and want the walker to follow.
_WALKER_BUDGET_MULTIPLIER: int = 4

# Status enum for proof-state capture on compile errors.  Used as the
# value type of the ``state_capture_status`` key returned by the
# ``run_compile_*_with_state`` orchestrators.  A subset
# (``"timeout"``, ``"crashed"``, ``"lock_contended"``, ``"unavailable"``)
# is also produced inside ``_run_with_pet`` under the dict key
# ``"reason"``; the remaining values (``"ok"``, ``"outside_proof"``,
# ``"no_position"``) are derived in the orchestrator.
#
# Note: ``"not_found"`` is an error *reason* used by tools like
# ``rocq_start`` and ``rocq_assumptions`` (see
# :data:`rocq_mcp.server._RECENT_ERROR_REASONS`), but it is never
# produced as a state-capture status — the orchestrator never reaches
# a state-capture step on a name-not-found error — so it does not
# appear here.
_StateCaptureStatus = Literal[
    "ok",
    "outside_proof",
    "timeout",
    "crashed",
    "memory_exhausted",
    "unavailable",
    "lock_contended",
    "no_position",
]

_VALID_STATE_CAPTURE_STATUSES: frozenset[str] = frozenset(get_args(_StateCaptureStatus))

# Non-failure members of ``_StateCaptureStatus``: the orchestrator-derived
# values produced after a *successful* enrichment lookup (or a structurally
# absent position).  Their complement inside :data:`_VALID_STATE_CAPTURE_STATUSES`
# is the set of pet-side failure modes that must stay aligned with
# :data:`rocq_mcp.server._PET_SIDE_FAILURE_REASONS`.
_NON_FAILURE_STATUSES: frozenset[str] = frozenset(
    {
        "ok",
        "outside_proof",
        "no_position",
    }
)

assert _server._PET_SIDE_FAILURE_REASONS <= _VALID_STATE_CAPTURE_STATUSES
assert (
    _VALID_STATE_CAPTURE_STATUSES - _NON_FAILURE_STATUSES
    == _server._PET_SIDE_FAILURE_REASONS
)


class _CaptureResult(TypedDict):
    """Return shape of :func:`_capture_compile_error_state`."""

    status: _StateCaptureStatus
    state: dict[str, Any] | None


async def _capture_compile_error_state(
    source: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    *,
    line: int,
    character: int,
    file_label: str,
    parent_tool: str,
    resolved_file: str | None = None,
    timeout: float | None = None,
) -> _CaptureResult:
    """Best-effort PET lookup of the proof state at a compile error.

    Returns a :class:`_CaptureResult` ``{"status": <_StateCaptureStatus>,
    "state": <dict|None>}``.  ``state`` is the captured state dict on
    ``"ok"`` / ``"outside_proof"``, ``None`` otherwise.
    """
    # Function-body import: serves two purposes.  (1) Tests monkeypatch
    # ``capture_position_state`` on ``rocq_mcp.interactive`` and need a
    # fresh attribute lookup each call — a module-level import would
    # freeze the reference at load time and bypass the monkeypatch.
    # (2) The ``except ImportError`` branch is exercised by
    # ``test_status_unavailable_when_import_fails`` (simulating an
    # interactive-module load failure) and surfaces ``"unavailable"``
    # gracefully instead of crashing the enrichment path.
    try:
        from rocq_mcp.interactive import _state_remove, capture_position_state
    except ImportError:
        return {"status": "unavailable", "state": None}

    lookup_file = resolved_file
    temp_path: str | None = None

    if lookup_file is None:
        ws = Path(workspace).resolve()
        try:
            with tempfile.NamedTemporaryFile(
                suffix=".v",
                mode="w",
                delete=False,
                dir=str(ws),
            ) as f:
                f.write(source)
                f.flush()
                temp_path = f.name
        except OSError:
            # Workspace I/O failure (no pet involvement). We collapse this
            # into "crashed" -- our catch-all for "enrichment couldn't run"
            # -- since we don't currently distinguish pre-pet failures from
            # real pet crashes.
            return {"status": "crashed", "state": None}
        lookup_file = temp_path

    try:
        try:
            state_result = await capture_position_state(
                file=file_label,
                resolved_file=lookup_file,
                workspace=workspace,
                lifespan_state=lifespan_state,
                line=line,
                character=character,
                tool=parent_tool,
                track_staleness=resolved_file is not None,
                timeout=timeout,
            )
        except Exception:
            # PetanqueError (or any other exception) escaping capture_position_state
            # is treated as a crash so the caller can surface ``state_capture_status``.
            return {"status": "crashed", "state": None}
    finally:
        if temp_path is not None:
            _server._cleanup_coqc_artifacts(temp_path)

    if not isinstance(state_result, dict):
        return {"status": "crashed", "state": None}

    if not state_result.get("success"):
        reason = state_result.get("reason", "crashed")
        if reason not in _VALID_STATE_CAPTURE_STATUSES:
            reason = "crashed"
        return {"status": reason, "state": None}

    goals = state_result.get("goals", "")
    proof_finished = state_result.get("proof_finished", False)
    if not goals or proof_finished:
        _state_remove(state_result["state_id"])
        return {"status": "outside_proof", "state": None}
    return {"status": "ok", "state": state_result}


def _merge_compile_error_state(
    result_dict: dict[str, Any],
    state_result: dict[str, Any],
) -> dict[str, Any]:
    """Attach captured proof-state fields to a compile failure result.

    Only called when ``state_capture_status == "ok"``: the captured state
    is actionable (``goals`` non-empty AND not ``proof_finished``), so we
    always merge the state fields and rewrite the hint to point at
    ``rocq_check(from_state=...)``.
    """
    for key in ("state_id", "goals", "file", "theorem", "proof_finished"):
        result_dict[key] = state_result[key]
    result_dict["hint"] = (
        "Interactive proof state captured at the error position. "
        f"Use rocq_check(from_state={state_result['state_id']}) or "
        f"rocq_step_multi(from_state={state_result['state_id']}) "
        "to explore fixes."
    )
    return result_dict


def _enrichment_timeout(lifespan_state: dict[str, Any]) -> float:
    """Per-call enrichment timeout, capped by ``_ENRICHMENT_TIMEOUT_CAP``."""
    pet_timeout = lifespan_state.get("pet_timeout", _server.ROCQ_PET_TIMEOUT)
    return min(float(pet_timeout), _ENRICHMENT_TIMEOUT_CAP)


async def _enrich_compile_failure(
    result: dict[str, Any],
    *,
    source: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    file_label: str,
    parent_tool: str,
    resolved_file: str | None = None,
) -> dict[str, Any]:
    """Apply state-capture enrichment to a failed compile result.

    Mutates *result* in place and returns it.  Sets ``state_capture_status``
    (a :data:`_StateCaptureStatus`) on every path: ``"no_position"`` when
    there is no usable error position, otherwise the status returned by
    :func:`_capture_compile_error_state`.

    *parent_tool* is the public MCP tool name of the calling tool
    (``"rocq_compile"`` or ``"rocq_compile_file"``); it is forwarded to
    ``_run_with_pet`` so any pet-level failure during enrichment is
    attributed to the right tool in ``recent_errors``.

    The caller is responsible for the mode-specific short-circuits
    (``lifespan_state is None``, ``result.get("success")``, and missing
    ``resolved_file`` in file-path mode).
    """
    if "error_positions" not in result:
        result["state_capture_status"] = "no_position"
        return result

    primary_error = _first_error_from_positions(result["error_positions"])
    if primary_error is None:
        result["state_capture_status"] = "no_position"
        return result

    capture = await _capture_compile_error_state(
        source,
        workspace,
        lifespan_state,
        line=primary_error["line"],
        character=primary_error["character"],
        file_label=file_label,
        parent_tool=parent_tool,
        resolved_file=resolved_file,
        timeout=_enrichment_timeout(lifespan_state),
    )
    result["state_capture_status"] = capture["status"]
    state_result = capture["state"]
    if state_result is None or capture["status"] != "ok":
        return result
    return _merge_compile_error_state(result, state_result)


async def run_compile_with_state(
    source: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
    lifespan_state: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Async wrapper for run_compile that enriches failures with PET state."""
    result = run_compile(source, workspace, timeout, include_warnings)
    if lifespan_state is None:
        return result
    if result.get("success"):
        return result
    # Record the coqc-level failure with the response's own reason
    # (validation, compile_error, or timeout) before optional pet
    # enrichment.  Falls back to "compile_error" when the helper
    # couldn't classify (defensive — should not happen post-fix).
    _server._record_error(
        lifespan_state,
        "rocq_compile",
        result.get("error", ""),
        reason=str(result.get("reason") or "compile_error"),
    )
    return await _enrich_compile_failure(
        result,
        source=source,
        workspace=workspace,
        lifespan_state=lifespan_state,
        file_label=_PROOF_FILE_LABEL,
        parent_tool="rocq_compile",
    )


async def _multi_error_walk(
    resolved_file: str,
    lifespan_state: dict[str, Any],
) -> list[Any] | None:
    """Run the proof-walk error collector against *resolved_file*.

    Returns the walker's ``list[ProofError]`` (possibly empty) when the
    walker ran, or ``None`` when the walker bailed (e.g. ``pet.toc``
    failed and the fallback yielded nothing) or when the call through
    ``_run_with_pet`` produced a failure envelope.  Uses
    ``auto_record=False`` because transient pet-level errors during the
    walk are not the signal we want to surface — the walker's own
    ``ProofError`` entries are.
    """
    try:
        with open(resolved_file, "r", encoding="utf-8") as f:
            source_text = f.read()
    except OSError:
        return None

    cap = _server._COMPILE_MULTI_ERROR_CAP
    per_call_timeout = _server._COMPILE_MULTI_ERROR_TIMEOUT

    def _do_walk(pet: Any) -> list[Any] | None:
        return collect_file_errors(
            file=resolved_file,
            source=source_text,
            pet=pet,
            per_call_timeout=per_call_timeout,
            max_errors=cap,
        )

    # Walker budget: generous enough that pet.toc + ``cap`` chunked runs
    # each at ``per_call_timeout`` can complete, plus headroom for the
    # lock/setup overhead.  Capped by the outer ceiling
    # ``_ENRICHMENT_TIMEOUT_CAP * _WALKER_BUDGET_MULTIPLIER`` so a
    # misconfigured CAP cannot starve the agent.
    walker_timeout = min(
        per_call_timeout * max(cap, 1) + per_call_timeout,
        _ENRICHMENT_TIMEOUT_CAP * _WALKER_BUDGET_MULTIPLIER,
    )

    result = await _server._run_with_pet(
        _do_walk,
        lifespan_state,
        "rocq_compile_file",
        timeout=walker_timeout,
        auto_record=False,
    )
    if isinstance(result, dict) and result.get("success") is False:
        return None
    return result


async def run_compile_file_with_state(
    file: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
    lifespan_state: dict[str, Any] | None = None,
    keep_vo: bool = False,
) -> dict[str, Any]:
    """Async wrapper for run_compile_file that enriches failures with PET state.

    *keep_vo* is forwarded to :func:`run_compile_file` to preserve the
    ``.vo``/``.vok``/``.vos`` outputs after a successful (or failed) coqc run.
    """
    try:
        resolved_file = _server._resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError):
        resolved_file = None

    # Snapshot .vo mtimes around the coqc call so we can detect rewrites
    # that may invalidate cached dependency state held by sibling
    # interactive sessions in the same workspace.  Both snapshots use
    # the same helper; the before/after diff is the only signal.
    ws_path = Path(workspace).resolve()
    vo_before = _server._snapshot_vo_mtimes(ws_path)
    result = run_compile_file(
        file, workspace, timeout, include_warnings, keep_vo=keep_vo
    )
    vo_after = _server._snapshot_vo_mtimes(ws_path)

    vo_warning = _server._maybe_vo_rebuild_warning(
        str(ws_path),
        before_mtimes=vo_before,
        after_mtimes=vo_after,
    )
    if vo_warning and isinstance(result, dict):
        result["vo_rebuild_warning"] = vo_warning

    if lifespan_state is None:
        return result
    if result.get("success"):
        return result
    _server._record_error(
        lifespan_state,
        "rocq_compile_file",
        result.get("error", ""),
        reason=str(result.get("reason") or "compile_error"),
    )
    if resolved_file is None:
        result["state_capture_status"] = "no_position"
        return result
    result = await _enrich_compile_failure(
        result,
        source="",
        workspace=workspace,
        lifespan_state=lifespan_state,
        file_label=file,
        resolved_file=resolved_file,
        parent_tool="rocq_compile_file",
    )

    # Multi-error walk: only on real compile errors and only when enabled
    # (CAP=0 disables).  Runs after state capture so existing behavior is
    # preserved.
    if result.get("reason") == "compile_error" and _server._COMPILE_MULTI_ERROR_CAP > 0:
        proof_errors = await _multi_error_walk(resolved_file, lifespan_state)
        if proof_errors is not None:
            result["errors"] = [
                {
                    "proof_name": e.proof_name,
                    "kind": e.kind,
                    "start_line": e.start_line,
                    "end_line": e.end_line,
                    "code": e.code,
                    "message": e.message,
                }
                for e in proof_errors
            ]
    return result
