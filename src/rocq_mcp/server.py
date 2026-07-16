"""Rocq MCP Server — tools for Rocq/Coq proof development.

This is the main entry point.  It defines the MCP application, shared
infrastructure (configuration, workspace validation, pet subprocess
management), and thin ``@mcp.tool`` wrappers that delegate to
implementation functions in :mod:`rocq_mcp.compile` and
:mod:`rocq_mcp.interactive`.
"""

from __future__ import annotations

import asyncio
import collections
import os
import shutil
import warnings
from pathlib import Path
from typing import Any, Callable, Literal

from fastmcp import Context, FastMCP
from fastmcp.server.lifespan import lifespan
from mcp.types import ToolAnnotations

import rocq_mcp
from rocq_mcp import config
from rocq_mcp import pet_runtime as _pet_runtime
from rocq_mcp import workspace as _workspace
from rocq_mcp.schemas import (
    CHECK_OUTPUT_SCHEMA,
    COMPILE_FILE_OUTPUT_SCHEMA,
    SEARCH_OUTPUT_SCHEMA,
    STEP_MULTI_OUTPUT_SCHEMA,
)

# Implementation functions from the domain modules (the old circular
# import is gone — these are ordinary top-level imports now).
from rocq_mcp.compile import (
    run_verify,
)
from rocq_mcp.compile_enrichment import (
    run_compile_file_with_state,
    run_compile_with_state,
)

# ---------------------------------------------------------------------------
# Configuration (env vars with defaults)
# ---------------------------------------------------------------------------
# Env-derived configuration lives in rocq_mcp.config (single definition
# site).  The names are re-bound here because submodules read them as
# ``_server.<NAME>`` and tests monkeypatch them on this module — both
# work against these bindings, since server code reads its own globals.
from rocq_mcp.config import (
    _COMPILE_MULTI_ERROR_CAP,  # noqa: F401
    _COMPILE_MULTI_ERROR_TIMEOUT,  # noqa: F401
    _RECENT_ERRORS_MAX,
    ROCQ_MAX_SOURCE_SIZE,  # noqa: F401
    ROCQ_WORKSPACE,  # noqa: F401  (import-compat; internal reads use config.ROCQ_WORKSPACE)
    _default_max_pet_rss_mb,  # noqa: F401
)
from rocq_mcp.diag import (
    _DIAG_LIVE_STATES_CAP,  # noqa: F401  (accessed as _server._DIAG_LIVE_STATES_CAP in tests)
    _build_diag_snapshot,
    _sample_pet_rss_mb,  # noqa: F401  (accessed as _server._sample_pet_rss_mb in tests)
)

# The failure-reason taxonomy and the envelope/degradation helpers moved
# to leaf modules (single source of truth; no import cycle).  The names
# below stay bound on this module because submodules and tests access
# them as ``_server.<name>`` — see rocq_mcp/taxonomy.py and
# rocq_mcp/envelope.py for the definitions.
from rocq_mcp.envelope import (
    _RECENT_ERROR_MESSAGE_LIMIT,  # noqa: F401  (re-export for tests)
    _fail,
    _no_ctx_fail,
    _notify,  # noqa: F401  (import-compat)
    _progress,  # noqa: F401  (import-compat)
    _record_error,
)
from rocq_mcp.health import (
    _SWITCH_ENV_KEYS,
    _detect_switch,
    _resolve_binary,
    build_health_snapshot,
    compute_switch_env,
    list_switches,
)
from rocq_mcp.interactive import (
    run_assumptions,
    run_check,
    run_goal,
    run_notations,
    run_query,
    run_search,
    run_start,
    run_step_multi,
    run_toc,
)

# Façade re-exports for import-and-call compatibility (tests do
# ``from rocq_mcp.server import _kill_pet`` etc.).  The two REBOUND
# mutable globals (_pet_lock, _pet_semaphore) are deliberately NOT
# re-exported — a from-import copy goes stale the moment
# _force_release_pet_lock replaces the lock; access them as
# ``pet_runtime._pet_lock`` / ``pet_runtime._pet_semaphore`` only.
from rocq_mcp.pet_runtime import (  # noqa: F401
    _PYTANQUE_NOT_INSTALLED_HINT,
    _build_memory_abort_response,
    _ensure_pet,
    _force_release_pet_lock,
    _get_pet_semaphore,
    _handle_pet_failure,
    _invalidate_pet,
    _kill_pet,
    _memory_watchdog,
    _merge_partial_state,
    _pet_alive,
    _pet_invalidation_hooks,
    _PetLockTimeout,
    _run_with_pet,
    _set_workspace_if_needed,
    _try_close_pet,
)
from rocq_mcp.schemas import (
    CHECK_OUTPUT_SCHEMA,
    COMPILE_FILE_OUTPUT_SCHEMA,
    SEARCH_OUTPUT_SCHEMA,
    STEP_MULTI_OUTPUT_SCHEMA,
)
from rocq_mcp.taxonomy import (
    RECENT_ERROR_REASONS as _RECENT_ERROR_REASONS,  # noqa: F401
)

# Façade re-exports: tests import-and-call these via rocq_mcp.server, and
# submodules still read some as ``_server.<NAME>``.  Server-internal code
# never uses these bindings (it calls ``_workspace.<NAME>``), so a
# monkeypatch on rocq_mcp.workspace is authoritative for every code path.
from rocq_mcp.workspace import (  # noqa: F401
    _CLEANUP_EXTENSIONS,
    _PROJECT_MARKERS,
    _VO_SCAN_FILE_CAP,
    _cleanup_coqc_artifacts,
    _count_sessions_in_workspace,
    _diff_vo_mtimes,
    _find_dune_root,
    _find_project_root_from_file,
    _maybe_vo_rebuild_warning,
    _maybe_workspace_warning,
    _parse_dune_flags,
    _parse_project_flags,
    _path_within,
    _pick_v_file,
    _resolve_file_in_workspace,
    _snapshot_vo_mtimes,
    _validate_workspace,
    _workspace_has_project_marker,
)


def _check_timeout_config(pet_timeout: float, cap: int) -> str | None:
    """Return a warning if config.ROCQ_PET_TIMEOUT exceeds config.ROCQ_QUERY_TIMEOUT_CAP.

    The cap is documented in the README as the upper bound for the
    per-call timeout, but config.ROCQ_PET_TIMEOUT is the fallback when no
    per-call timeout is given.  If an operator misconfigures the pair
    so the fallback exceeds the cap, the lock can park longer than the
    cap promise — silently violating the documented invariant.
    """
    if pet_timeout > cap:
        return (
            f"ROCQ_PET_TIMEOUT={pet_timeout} exceeds ROCQ_QUERY_TIMEOUT_CAP={cap}; "
            f"calls without a per-call timeout= will park the pet lock longer "
            f"than ROCQ_QUERY_TIMEOUT_CAP claims."
        )
    return None


_timeout_config_msg = _check_timeout_config(
    config.ROCQ_PET_TIMEOUT, config.ROCQ_QUERY_TIMEOUT_CAP
)
if _timeout_config_msg:
    warnings.warn(_timeout_config_msg, RuntimeWarning, stacklevel=2)


# _PYTANQUE_NOT_INSTALLED_HINT moved to rocq_mcp.pet_runtime.


def _check_pet_availability() -> str | None:
    """Return a warning message when pet (pytanque + ``pet`` binary) is missing.

    The interactive tools and the multi-error / state-capture enrichment on
    ``rocq_compile_file`` all route through pet.  Falling back to coqc-only
    operation is a substantial reduction in capability, so the operator
    deserves an up-front signal at server boot rather than discovering it
    only when an agent dispatches the first interactive tool call and gets
    ``reason="unavailable"`` back.

    Returns ``None`` when both halves of the install are present.
    """
    pytanque_missing = False
    try:
        import pytanque  # noqa: F401
    except ImportError:
        pytanque_missing = True
    pet_binary_missing = shutil.which("pet") is None
    if not (pytanque_missing or pet_binary_missing):
        return None
    parts = []
    if pytanque_missing:
        parts.append("the pytanque Python binding is not importable")
    if pet_binary_missing:
        parts.append("the `pet` binary is not on PATH")
    return (
        "pet not detected: " + " and ".join(parts) + ". "
        "Interactive tools (rocq_start / rocq_check / rocq_step_multi / "
        "rocq_query / rocq_assumptions / rocq_toc / rocq_notations) and "
        "proof-state enrichment on rocq_compile_file will return "
        'reason="unavailable". '
        "Petanque (the `pet` binary and the matching pytanque Python "
        "binding) ships with coq-lsp; both halves must be installed "
        "together.  `pip` / `uv` cannot install petanque on their own — "
        "see https://github.com/ejgallego/coq-lsp for install "
        "instructions appropriate to your environment."
    )


_pet_availability_msg = _check_pet_availability()
if _pet_availability_msg:
    warnings.warn(_pet_availability_msg, RuntimeWarning, stacklevel=2)


# ---------------------------------------------------------------------------
# Lifespan
# ---------------------------------------------------------------------------


@lifespan
async def app_lifespan(server: Any) -> Any:
    """Server lifespan. Pet is spawned lazily on first pytanque call."""
    state: dict[str, Any] = {
        "pet_client": None,
        # The server's event loop — lets worker threads schedule MCP
        # notifications (progress / log) via run_coroutine_threadsafe.
        "event_loop": asyncio.get_running_loop(),
        "workspace": config.ROCQ_WORKSPACE,
        "pet_timeout": config.ROCQ_PET_TIMEOUT,
        "current_workspace": None,
        # Diagnostics (rocq_diag tool, see _build_diag_snapshot).
        "pet_started_at": None,
        # Count of successful spawns; pet_restarts is derived as
        # max(0, total_spawns - 1).  Counting only successful spawns
        # ensures a fresh server reports 0 restarts even if the very
        # first spawn attempt raised.
        "total_spawns": 0,
        "peak_pet_rss_mb": 0.0,
        "pet_generation": 0,
        "recent_errors": collections.deque(maxlen=_RECENT_ERRORS_MAX),
        # Degraded-enrichment counters (rocq_mcp.envelope.attach_degraded)
        # and pet-lock contention telemetry — surfaced by rocq_diag.
        "enrichment_failures": {},
        "lock_wait_ms_last": 0.0,
        "lock_wait_ms_max": 0.0,
        "lock_contended_total": 0,
    }
    try:
        yield state
    finally:
        client = state.get("pet_client")
        if client:
            _pet_runtime._kill_pet(client)
        # Clean up cache file
        ws = state.get("workspace")
        if ws:
            cache_file = Path(ws) / f"rocq_mcp_cache_{os.getpid()}_.v"
            _workspace._cleanup_coqc_artifacts(str(cache_file))


# Always-visible server guidance.  With deferred tool loading (the default
# in Claude Code) tool descriptions may not be in context until a tool is
# looked up — these instructions are the one place cross-tool knowledge is
# guaranteed to be visible.  Budget: keep under ~2,200 characters.
_SERVER_INSTRUCTIONS = """\
Rocq/Coq proof tools: coqc-based batch compile/verify plus a held \
interactive session (pet/coq-lsp) that keeps imports warm across calls.

Core proof loop: rocq_start (returns a state_id) -> rocq_step_multi to \
explore candidate tactics (read-only) -> rocq_check to commit the winner \
(returns a new state_id) -> write the finished proof into the .v file -> \
rocq_compile_file + rocq_verify (and rocq_assumptions for an axiom audit) \
to finish. Never iterate by re-running coqc on a scratch file: coqc \
reloads every import per call; the interactive session does not.

State rules: rocq_check and rocq_step_multi require an explicit \
from_state (a state_id from rocq_start or a previous rocq_check). States \
live in a process-global LRU table; states you keep using stay alive. If \
a state_id goes missing, restart the session with rocq_start.

Failures: every failure response is {success: false, error, reason}. \
Dispatch on reason, not on message text; reason is one of: validation, \
not_found, timeout, crashed, memory_exhausted, lock_contended, \
unavailable, tactic_failed, query_rejected, compile_error, \
axiom_dependency, type_mismatch. When a response carries pet_restarted: true, call \
rocq_diag to see what happened.

Timeouts: timeout=0 means "use the server default". On session/query \
tools larger per-call values are clamped to a server cap and the \
response then carries clamped_timeout; compile/verify timeouts are \
used as-is.

Deep reference (MCP resources, fetch on demand): rocq://guide/workflows \
(tool selection + proof patterns — read before a proof campaign), \
rocq://guide/failures (recovery playbook), rocq://guide/concurrency \
(sharing this server between agents), rocq://guide/responses \
(field-level reference).
"""

mcp = FastMCP(
    "rocq-mcp",
    instructions=_SERVER_INSTRUCTIONS,
    version=rocq_mcp.__version__,
    lifespan=app_lifespan,
)

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Workspace resolution / project flags / artifact hygiene -> rocq_mcp.workspace
# ---------------------------------------------------------------------------
# Moved verbatim to rocq_mcp/workspace.py.  Names are re-bound below
# because tests and submodules read them as ``_server.<NAME>``; internal
# server code calls through ``_workspace.<NAME>`` (attribute access) so a
# monkeypatch on rocq_mcp.workspace is seen by every caller.


def _resolve_call_timeout(
    timeout: int | float | None,
) -> tuple[float | None, bool]:
    """Resolve a per-call timeout against ``config.ROCQ_QUERY_TIMEOUT_CAP``.

    Returns ``(effective_timeout, clamped)``:

    - When *timeout* is ``None``, 0, or negative: ``(None, False)`` —
      caller falls back to ``config.ROCQ_PET_TIMEOUT``.
    - Otherwise: ``(float(min(timeout, cap)), timeout > cap)``.

    Shared by every pet-routed wrapper so the clamp behaviour and
    ``clamped_timeout`` echo stay in lockstep.
    """
    if timeout is None or timeout <= 0:
        return None, False
    clamped = timeout > config.ROCQ_QUERY_TIMEOUT_CAP
    return float(min(timeout, config.ROCQ_QUERY_TIMEOUT_CAP)), clamped


# ---------------------------------------------------------------------------
# Pet subprocess management -> rocq_mcp.pet_runtime (decomposition cluster B)
# ---------------------------------------------------------------------------


def _resolve_tool_envelope(
    *,
    tool: str,
    ctx: Any,
    workspace: str,
    file: str | None = None,
    timeout: int | float | None = None,
    timeout_default: int | None = None,
    ctx_optional: bool = False,
) -> dict[str, Any] | tuple[str, dict[str, Any] | None, str | None, bool, float | None]:
    """Resolve the shared envelope steps for ``@mcp.tool`` wrappers.

    Runs the boilerplate every pet-routed / coqc-routed wrapper repeats:

    1. ctx-check first — for pet-routed tools, a missing context is a
       programmer error and is reported as the no-ctx envelope without
       touching the workspace (``_no_ctx_fail``).  Pins the order so a
       bad workspace + no-ctx caller gets the no-ctx envelope, not a
       silent validation failure that ``recent_errors`` never sees.
       Coqc-routed tools (``rocq_compile`` / ``rocq_compile_file`` /
       ``rocq_verify``) pass ``ctx_optional=True``: they can run without
       an MCP context — ``lifespan_state`` falls through as ``None`` and
       the ``recent_errors`` recording is silently skipped.
    2. Workspace resolution: explicit > project-marker walk-up from
       *file* (when *file* is non-empty) > ``config.ROCQ_WORKSPACE``.
    3. Timeout resolution.  *timeout_default* is the wrapper's
       compile/verify fallback (seconds): when set, the helper
       falls back to it for ``timeout<=0`` and does not clamp; when
       ``None`` the helper routes through :func:`_resolve_call_timeout`
       (the per-call cap that returns a ``clamped`` flag).
    4. ``_workspace._validate_workspace`` against the resolved workspace; on
       failure returns a :func:`_fail` envelope with the *already
       resolved* lifespan_state so the failure lands in
       ``recent_errors``.
    5. ``_workspace._maybe_workspace_warning`` against the resolved workspace.

    Returns either a failure envelope (caller returns it verbatim) or
    the tuple ``(workspace, lifespan_state, ws_warning, clamped,
    effective_timeout)``.
    """
    if ctx is None:
        if not ctx_optional:
            return _no_ctx_fail(tool)
        lifespan_state: dict[str, Any] | None = None
    else:
        lifespan_state = ctx.lifespan_context

    explicit_workspace = bool(workspace)
    if file:
        workspace = (
            workspace
            or _workspace._find_project_root_from_file(file)
            or config.ROCQ_WORKSPACE
        )
    else:
        workspace = workspace or config.ROCQ_WORKSPACE

    effective_timeout: float | None
    if timeout_default is not None:
        effective_timeout = (
            float(timeout)
            if timeout is not None and timeout > 0
            else float(timeout_default)
        )
        clamped = False
    else:
        effective_timeout, clamped = _resolve_call_timeout(timeout)

    err = _workspace._validate_workspace(workspace)
    if err:
        return _fail(lifespan_state, tool, err, "validation")

    ws_warning = _workspace._maybe_workspace_warning(
        workspace, explicit=explicit_workspace, file_provided=bool(file)
    )
    return workspace, lifespan_state, ws_warning, clamped, effective_timeout


def _finalize_tool_envelope(
    result: Any, *, clamped: bool, ws_warning: str | None
) -> Any:
    """Merge trailing envelope keys onto *result*.

    Mirrors the trailing 3-line block of every wrapper:

    - ``clamped_timeout``: echoes the cap value when the per-call
      timeout was clamped by :func:`_resolve_call_timeout`.
    - ``workspace_warning``: the advisory from
      :func:`_workspace._maybe_workspace_warning`, when set.

    Both merges are no-ops if *result* is not a ``dict`` so an
    implementation that returns a non-dict (unexpected) passes through
    untouched.
    """
    if not isinstance(result, dict):
        return result
    if clamped:
        result["clamped_timeout"] = config.ROCQ_QUERY_TIMEOUT_CAP
    if ws_warning:
        result["workspace_warning"] = ws_warning
    return result


# ---------------------------------------------------------------------------
# Tool: rocq_compile
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Compile Rocq source (coqc)",
        readOnlyHint=False,
        destructiveHint=False,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_compile(
    source: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    ctx: Context = None,
) -> dict[str, Any]:
    """Compile Rocq source from a string buffer via coqc.

    For files on disk use ``rocq_compile_file``; for iterating on a proof
    use ``rocq_start`` + ``rocq_check`` (coqc reloads every import per
    call, the interactive session does not).

    On failure: ``error_positions``, a ``hint`` naming the next call, and
    (with coq-lsp available) ``state_capture_status`` — ``"ok"`` means the
    response carries a live ``state_id`` to continue from via
    ``rocq_check(from_state=...)``.  Full recovery matrix:
    ``rocq://guide/failures``.

    Args:
        source: Complete .v file content, including imports.
        workspace: Workspace directory; default ROCQ_WORKSPACE env var
            (see rocq://guide/responses for workspace resolution).
        timeout: Seconds; 0 = ROCQ_COQC_TIMEOUT default.
        include_warnings: False drops warning-severity output.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_compile",
        ctx=ctx,
        workspace=workspace,
        timeout=timeout,
        timeout_default=config.ROCQ_COQC_TIMEOUT,
        ctx_optional=True,
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    # timeout_default was passed to _resolve_tool_envelope,
    # so effective_timeout is non-None here.
    assert effective_timeout is not None
    result = await run_compile_with_state(
        source=source,
        workspace=workspace,
        timeout=effective_timeout,
        include_warnings=include_warnings,
        lifespan_state=lifespan_state,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_compile_file
# ---------------------------------------------------------------------------


@mcp.tool(
    output_schema=COMPILE_FILE_OUTPUT_SCHEMA,
    annotations=ToolAnnotations(
        title="Compile a .v file (coqc)",
        readOnlyHint=False,
        destructiveHint=False,
        idempotentHint=True,
        openWorldHint=False,
    ),
)
async def rocq_compile_file(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    keep_vo: bool = False,
    mode: Literal["full", "vos"] = "full",
    timing: bool = False,
    ctx: Context = None,
) -> dict[str, Any]:
    """Compile a .v file on disk via coqc — whole-file check and final verification.

    Prefer this over ``rocq_compile`` for files on disk (the source is not
    resent over the transport); prefer ``rocq_start`` + ``rocq_check`` for
    scratch iteration.  The file's ``.vo``/``.vok``/``.vos`` artifacts
    (including pre-existing ones) are overwritten and then deleted
    unless ``keep_vo=True``; the source file is preserved.

    On failure: ``error_positions`` + ``hint``; with coq-lsp also
    ``state_capture_status`` (``"ok"`` → a live ``state_id`` to continue
    from) and ``errors`` — a per-declaration multi-error list for the
    whole file (may be present-and-empty, meaning "no additional errors
    found").  May carry ``vo_rebuild_warning`` when the compile rewrites
    ``.vo`` files under active interactive sessions.  Recovery matrix:
    ``rocq://guide/failures``; field details: ``rocq://guide/responses``.

    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Auto-detected from project markers when omitted
            (rocq://guide/responses).
        timeout: Seconds; 0 = ROCQ_COQC_TIMEOUT default.
        include_warnings: False drops warning-severity output.
        keep_vo: Keep .vo/.vok/.vos after the compile (for sibling
            Require Import).  Footgun: with mode="vos" only a .vos is
            produced and downstream full-mode imports fail — pair keep_vo
            with mode="full".
        mode: "full" (default) elaborates every proof; "vos" skips proof
            bodies ENTIRELY — a fast statement/import pre-pass that accepts
            any proof body, so always finish with "full".
        timing: Attach per-sentence timing {total_sentences, top_slowest,
            last_completed}; on timeout the error names the last completed
            sentence.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_compile_file",
        ctx=ctx,
        workspace=workspace,
        file=file,
        timeout=timeout,
        timeout_default=config.ROCQ_COQC_TIMEOUT,
        ctx_optional=True,
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    # timeout_default was passed to _resolve_tool_envelope,
    # so effective_timeout is non-None here.
    assert effective_timeout is not None
    result = await run_compile_file_with_state(
        file=file,
        workspace=workspace,
        timeout=effective_timeout,
        include_warnings=include_warnings,
        lifespan_state=lifespan_state,
        keep_vo=keep_vo,
        mode=mode,
        timing=timing,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_verify
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Verify a proof matches its statement",
        readOnlyHint=False,
        destructiveHint=False,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_verify(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    ctx: Context = None,
) -> dict[str, Any]:
    """Verify a proof proves the original statement — sandboxed admit/axiom/statement check.

    Wraps the proof in a Module M sandbox: catches type redefinition,
    Admitted/Abort, custom axioms, and statement mismatches; standard
    library axioms (classical logic, Reals, ...) are accepted.  Run after
    a successful compile.  This is the *trust decision*;
    ``rocq_assumptions`` is the raw axiom listing.

    Failure ``reason`` values: ``compile_error``, ``axiom_dependency``
    (Admitted/admit or a non-whitelisted axiom), ``type_mismatch``,
    ``timeout``, ``validation``; pet-side ``crashed`` /
    ``memory_exhausted`` can surface from the internal structure
    lookup (then with ``pet_restarted: true``).  On success
    ``verification_method``
    reports the phase used (``module_m``, ``shared_defs``, ``direct`` —
    the last has weaker guarantees; see the README security model).

    Args:
        proof: Complete proof file content, including imports.
        problem_name: Unqualified theorem name (e.g. "add_comm").
        problem_statement: The original problem file content (with
            Admitted/Abort).
        workspace: Workspace directory; default ROCQ_WORKSPACE.
        timeout: Seconds; 0 = ROCQ_VERIFY_TIMEOUT default (budget is
            shared across phases; worst case ~2x when a sandbox phase
            times out and direct verification retries).
        include_warnings: False drops warning-severity output.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_verify",
        ctx=ctx,
        workspace=workspace,
        timeout=timeout,
        timeout_default=config.ROCQ_VERIFY_TIMEOUT,
        ctx_optional=True,
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    # timeout_default was passed to _resolve_tool_envelope,
    # so effective_timeout is non-None here.
    assert effective_timeout is not None
    result = await run_verify(
        proof=proof,
        problem_name=problem_name,
        problem_statement=problem_statement,
        workspace=workspace,
        timeout=effective_timeout,
        include_warnings=include_warnings,
        lifespan_state=lifespan_state,
    )
    # Record verification failures (success=False with an error message)
    # so rocq_diag surfaces them.  Pet-level crashes routed through
    # run_verify -> _pet_runtime._run_with_pet (Phase 2 toc lookup) are already
    # recorded inside that helper, so skip when ``pet_restarted=True``
    # to avoid the double-record bug — the prior entry already carries
    # tool="rocq_verify" with the right reason because _extract_problem_structure
    # passes that tool name to _pet_runtime._run_with_pet.
    if (
        isinstance(result, dict)
        and result.get("success") is False
        and result.get("error")
        and not result.get("pet_restarted")
    ):
        _record_error(
            lifespan_state,
            "rocq_verify",
            str(result["error"]),
            reason=str(result.get("reason") or "validation"),
        )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_query
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Query the Rocq environment",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_query(
    command: str,
    preamble: str = "",
    file: str = "",
    workspace: str = "",
    max_results: int | None = None,
    include_warnings: bool = True,
    timeout: int = 0,
    from_state: int | None = None,
    ctx: Context = None,
) -> dict[str, Any]:
    """Run a raw Rocq query (Check / Print / About / Locate / Search) and return its output.

    For lemma search prefer ``rocq_search`` (structured hits, filters,
    pagination); this tool is the raw-vernacular escape hatch.
    Read-only; modifies no proof state.  Context comes from one of three
    modes: ``preamble=`` (import/scope commands as a string — Require
    Import, Open Scope, Set/Unset belong HERE, never in ``command=``,
    where each statement runs in isolation), ``file=`` (a .v whose
    definitions are in scope), or ``from_state=`` (a live state_id —
    Search sees hypotheses, opened scopes, and local definitions; the
    query runs on a discarded child state, the parent is untouched).
    Prefer ``from_state`` over ``rocq_check(body="Search ...")`` for pure
    queries.  Patterns: ``rocq://guide/workflows``.

    Args:
        command: The query to run, e.g. "Search (_ + _ = _ + _).".
        preamble: Import/scope lines for context.
        file: .v path whose definitions should be in scope (mutually
            exclusive with preamble / from_state).
        workspace: Auto-detected from project markers when omitted.
        max_results: Cap Search hits (recommended for broad patterns).
        include_warnings: False drops warning-severity feedback.
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT; clamped to
            ROCQ_QUERY_TIMEOUT_CAP.
        from_state: Live state_id to query against (mutually exclusive
            with file).
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_query", ctx=ctx, workspace=workspace, file=file, timeout=timeout
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_query(
        command=command,
        preamble=preamble,
        workspace=workspace,
        lifespan_state=lifespan_state,
        file=file,
        max_results=max_results,
        include_warnings=include_warnings,
        timeout=effective_timeout,
        from_state=from_state,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_assumptions
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Audit a theorem's axioms",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_assumptions(
    name: str,
    file: str,
    workspace: str = "",
    timeout: int = 0,
    include_raw: bool = False,
    ctx: Context = None,
) -> dict[str, Any]:
    """List the axioms a theorem depends on (Print Assumptions), parsed.

    Pure introspection — no trust classification; use ``rocq_verify`` for
    a sandboxed admit-free / axiom-policy verdict.  The theorem must be
    defined in *file*, which sets up the exact environment so the right
    name resolves.  Returns ``assumptions: list["name : type"]`` (empty =
    closed under the global context; Admitted and Axiom/Parameter appear
    here indistinguishably); ``include_raw=True`` adds ``raw_output``.

    Timeout trap: the first call fetches opaque proofs from .vo files
    (slow on heavy imports) and a pet restart wipes that progress — set
    ``timeout`` high on the FIRST call, not on a retry
    (``rocq://guide/failures``).  On a typo the ``not_found`` response
    carries ``available_in_file`` for fuzzy matching.

    Args:
        name: Theorem/lemma name to audit (e.g. "add_comm").
        file: .v file where the theorem is defined (relative to
            workspace).
        workspace: Auto-detected from project markers when omitted.
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT; set 180+ up front on
            heavy imports.
        include_raw: True additionally returns raw_output (the Print
            Assumptions text, opaque-proof loader notices stripped;
            redundant with the parsed list).
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_assumptions",
        ctx=ctx,
        workspace=workspace,
        file=file,
        timeout=timeout,
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_assumptions(
        name=name,
        file=file,
        workspace=workspace,
        lifespan_state=lifespan_state,
        timeout=effective_timeout,
        include_raw=include_raw,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_toc
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Outline a .v file",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_toc(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Outline a .v file: definitions, lemmas, theorems, and sections as a hierarchy.

    No session needed.  Use it to find theorem names before
    ``rocq_start`` / ``rocq_assumptions``, or to orient in an unfamiliar
    file.  Output is a plain-text outline capped at 8,000 characters
    (a truncation marker reports the total).

    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Auto-detected from project markers when omitted.
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT; raise for heavy imports.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_toc", ctx=ctx, workspace=workspace, file=file, timeout=timeout
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_toc(
        file=file,
        workspace=workspace,
        lifespan_state=lifespan_state,
        timeout=effective_timeout,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_notations
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Explain notations in a statement",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_notations(
    statement: str,
    preamble: str = "",
    workspace: str = "",
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Resolve every notation in a statement: which notation, scope, and module.

    Debugs notation ambiguity (is ``+`` in nat_scope or Z_scope?).  Pass
    the statement part after the colon of a Lemma/Theorem declaration — a
    proposition or type, not an arbitrary term.

    Args:
        statement: The proposition/type to analyze, e.g.
            "forall n, n + 0 = n".
        preamble: Import lines for context (e.g. "Require Import QArith.").
        workspace: Workspace directory; default ROCQ_WORKSPACE.
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_notations", ctx=ctx, workspace=workspace, timeout=timeout
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_notations(
        statement=statement,
        preamble=preamble,
        workspace=workspace,
        lifespan_state=lifespan_state,
        timeout=effective_timeout,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_start
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        # destructiveHint covers the force_restart=True path, which kills
        # pet and clears the state table for every caller of this server.
        title="Start or resume a proof session",
        readOnlyHint=False,
        destructiveHint=True,
        idempotentHint=False,
        openWorldHint=False,
    )
)
async def rocq_start(
    file: str = "",
    theorem: str = "",
    workspace: str = "",
    line: int | None = None,
    character: int | None = None,
    preamble: str = "",
    force_restart: bool = False,
    timeout: int = 0,
    goals_format: Literal["pretty", "structured", "names_only"] = "pretty",
    ctx: Context = None,
) -> dict[str, Any]:
    """Open an interactive proof session; returns a state_id plus the goals there.

    The session keeps imports warm across calls — this is the entry point
    of the core loop (then ``rocq_step_multi`` to explore, ``rocq_check``
    to commit).  Three modes, precedence theorem > position > preamble:
    (1) file+theorem — prove a named theorem; (2) file+line+character —
    inspect goals anywhere in a file (0-indexed; the cursor rounds
    FORWARD through its sentence: pointing at a tactic yields the state
    after it, whitespace before it yields the state before it — full rule
    in ``rocq://guide/workflows``); (3) preamble — imports-only scratch
    session, preferred for iteration without a project.

    The file is read once at start: later edits make held states stale
    (``stale_warning``; rocq_start again after edits).  On an unknown
    theorem the ``not_found`` response carries ``available_in_file`` for
    typo recovery.

    Args:
        file: .v path (relative to workspace) for modes 1-2.
        theorem: Theorem name to prove (mode 1).
        workspace: Auto-detected from project markers when omitted.
        line: 0-based line (mode 2; see position semantics above).
        character: 0-based character offset (mode 2).
        preamble: Import commands for mode 3, e.g. "Require Import Lia.".
        force_restart: DESTRUCTIVE — kills pet and clears every caller's
            states before starting.  Recovery-only (repeated state expiry,
            RAM bloat); never routine (rocq://guide/concurrency).
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT; raise for heavy imports.
        goals_format: Goals representation — "pretty" (default),
            "structured", or "names_only".
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_start", ctx=ctx, workspace=workspace, file=file, timeout=timeout
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_start(
        file=file,
        theorem=theorem,
        workspace=workspace,
        lifespan_state=lifespan_state,
        line=line,
        character=character,
        preamble=preamble,
        force_restart=force_restart,
        timeout=effective_timeout,
        goals_format=goals_format,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi
# ---------------------------------------------------------------------------


@mcp.tool(
    output_schema=STEP_MULTI_OUTPUT_SCHEMA,
    annotations=ToolAnnotations(
        title="Try tactics without committing",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    ),
)
async def rocq_step_multi(
    tactics: list[str],
    from_state: int,
    include_warnings: bool = True,
    timeout: int = 0,
    goals_format: Literal["pretty", "structured", "names_only"] = "pretty",
    timeouts: list[float] | None = None,
    preset: Literal["", "auto"] = "",
    ctx: Context = None,
) -> dict[str, Any]:
    """Try up to 20 tactics against one state; report each outcome without committing.

    Read-only exploration — the state table is untouched; commit the
    winner with ``rocq_check(from_state=<same state>, body=<tactic>)``.
    Each entry carries ``success`` and ``time_ms``; successes add
    ``proof_finished`` and ``goals_count``, the first entry per
    distinct outcome adds ``goals``/``focus_depth`` (repeats carry
    ``same_outcome_as``), failed tactics carry ``error`` (and
    ``feedback`` when a tactic prints).  Advance a
    confident prefix with ``rocq_check`` FIRST, then branch from the new
    state — do not repeat the prefix inside every entry.  Tactic
    batteries and patterns: ``rocq://guide/workflows``.

    Args:
        tactics: Tactics to try (max 20), e.g.
            ["auto.", "lia.", "induction n."].
        from_state: State to branch from (a state_id from rocq_start or
            rocq_check).  Required; there is no implicit current state.
        include_warnings: False drops warning-severity feedback.
        timeout: Whole-batch seconds; each tactic gets
            timeout/len(tactics).  0 = ROCQ_PET_TIMEOUT.
        goals_format: Goals representation for full entries — "pretty"
            (default), "structured", or "names_only".  Identical
            outcomes are deduplicated: repeats carry same_outcome_as
            instead of goals; the response carries distinct_outcomes
            and a summary (tried/succeeded/finished/best).
        timeouts: Optional per-tactic budgets in seconds (one per
            tactic); the batch wall-clock is their sum.  Each entry
            also reports time_ms.
        preset: "auto" appends the standard automation battery
            (trivial ... firstorder, cheapest first) after your
            tactics, deduplicated, capped at 20.
    """
    if ctx is None:
        return _no_ctx_fail("rocq_step_multi")

    effective_timeout, clamped = _resolve_call_timeout(timeout)

    result = await run_step_multi(
        tactics=tactics,
        lifespan_state=ctx.lifespan_context,
        from_state=from_state,
        include_warnings=include_warnings,
        timeout=effective_timeout,
        goals_format=goals_format,
        timeouts=timeouts,
        preset=preset,
    )
    if clamped:
        result["clamped_timeout"] = config.ROCQ_QUERY_TIMEOUT_CAP
    return result


# ---------------------------------------------------------------------------
# Tool: rocq_check
# ---------------------------------------------------------------------------


@mcp.tool(
    output_schema=CHECK_OUTPUT_SCHEMA,
    annotations=ToolAnnotations(
        # Additive, never destructive: allocates a fresh state_id and
        # leaves existing states untouched.  Not idempotent (each call
        # creates a new state).
        title="Run proof commands from a state",
        readOnlyHint=False,
        destructiveHint=False,
        idempotentHint=False,
        openWorldHint=False,
    ),
)
async def rocq_check(
    body: str,
    from_state: int,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    goals_format: Literal[
        "pretty", "structured", "names_only", "diff", "none"
    ] = "pretty",
    ctx: Context = None,
) -> dict[str, Any]:
    """Run proof commands from a held state; returns a new state_id — the commit step.

    Imports stay cached across calls, so this is the fast inner loop (vs
    coqc, which reloads everything).  On success: ``goals``, new
    ``state_id``, ``focus_depth``; commands that print return
    ``feedback`` pairs.  On a rejected tactic (reason ``tactic_failed``):
    ``last_valid_state_id`` and ``failed_command`` — continue from
    ``last_valid_state_id`` immediately, no restart needed.  On
    ``proof_finished``: ``proof_tactics`` (root-to-leaf) plus a hint to
    assemble and validate the final .v — or the ``proof_tactics_status``
    family when the chain broke (``rocq://guide/failures``).
    ``stale_warning`` fires if the file changed since rocq_start.

    Args:
        body: One or more Rocq sentences to execute.
        from_state: State to execute from (a state_id from rocq_start or
            a previous rocq_check).  Required; no implicit current state.
        workspace: Accepted for compatibility; unused (the workspace
            comes from the state entry).
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT; raise for
            vm_compute/native_compute.
        include_warnings: False drops warning-severity feedback.
        goals_format: Goals representation — "pretty" (default string),
            "structured" (hyps as {names, type} + conclusion),
            "names_only", "diff" (delta vs the from_state parent;
            returns goals_diff instead of goals), or "none" (omit).
    """
    # Note: workspace param is accepted for API compatibility but unused;
    # the active workspace comes from the state entry set by rocq_start.
    effective_timeout, clamped = _resolve_call_timeout(timeout)

    if ctx is None:
        return _no_ctx_fail("rocq_check")

    result = await run_check(
        body=body,
        lifespan_state=ctx.lifespan_context,
        from_state=from_state,
        timeout=effective_timeout,
        include_warnings=include_warnings,
        goals_format=goals_format,
    )
    if clamped and isinstance(result, dict):
        result["clamped_timeout"] = config.ROCQ_QUERY_TIMEOUT_CAP
    return result


@mcp.tool(
    annotations=ToolAnnotations(
        title="Server runtime diagnostics",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_diag(ctx: Context = None) -> dict[str, Any]:
    """Server runtime diagnostics: pet health, memory, lock contention, recent errors.

    Call after any ``pet_restarted: true`` (why did pet die?), before a
    long ``vm_compute`` (memory headroom vs ``max_rss_mb_threshold``), or
    between sub-agent dispatches when sharing one server (foreign
    ``live_states`` entries, ``lock.contended_total``,
    ``enrichment_failures``).  Does not spawn pet.  ``rocq_health`` is
    the toolchain-side counterpart.  Full response shape:
    ``rocq://guide/responses``; recovery playbook:
    ``rocq://guide/failures``.
    """
    if ctx is None:
        return _no_ctx_fail("rocq_diag")
    return _build_diag_snapshot(ctx.lifespan_context)


# ---------------------------------------------------------------------------
# Tool: rocq_health
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Toolchain health check",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_health(ctx: Context = None) -> dict[str, Any]:
    """Toolchain health: is coqc resolvable, and which opam switch is this server on?

    An MCP server inherits PATH / opam environment from whatever launched
    it — which can differ from your interactive shell.  Call this first
    when coqc behaves like the wrong version or a previously-building
    proof fails.  Reports ``ok``, ``switch`` (+ prefix/source),
    ``toolchain`` (coqc / pet paths and versions), ``pet`` liveness, and
    ``warnings``.  Read-only; does not spawn pet.  ``rocq_diag`` is the
    runtime-side counterpart; ``rocq_switch`` changes the switch (with
    sharp caveats).
    """
    if ctx is None:
        return _no_ctx_fail("rocq_health")
    # build_health_snapshot probes `coqc --print-version` / `pet --version`
    # via subprocess; run off the event-loop thread.
    return await asyncio.to_thread(build_health_snapshot, ctx.lifespan_context)


# ---------------------------------------------------------------------------
# Tool: rocq_switch
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        # Process-global: kills pet, clears every caller's state table,
        # and may leave .vo artifacts ABI-incompatible.
        title="Change opam switch (process-global)",
        readOnlyHint=False,
        destructiveHint=True,
        idempotentHint=True,
        openWorldHint=False,
    ),
    meta={"anthropic/requiresUserInteraction": True},
)
async def rocq_switch(name: str = "", ctx: Context = None) -> dict[str, Any]:
    """Switch the running server to another opam switch — process-global and destructive.

    Applies the new switch environment to the live process and kills pet;
    the next call respawns under the new switch.  Costs: ALL live
    state_ids are discarded (rocq_start again), .vo files built under the
    old switch may be ABI-incompatible (recompile), and every agent
    sharing this server is moved.  In shared sessions check
    ``rocq_diag``'s ``live_states`` first.  For a stable setup prefer
    pinning the switch at launch — register the server command as
    ``opam exec --switch=<name> -- rocq-mcp``
    (``rocq://guide/concurrency``).

    On failure: ``not_found`` carries ``available_switches`` (typo
    recovery); ``validation`` = empty name or opam unavailable;
    ``lock_contended`` = pet busy, nothing was changed — retry once
    in-flight calls settle.

    Args:
        name: Installed opam switch to activate (e.g. "rocq9"); see
            rocq_health / `opam switch list`.
    """
    if ctx is None:
        return _no_ctx_fail("rocq_switch")
    lifespan_state = ctx.lifespan_context

    if not name or not name.strip():
        return _fail(
            lifespan_state,
            "rocq_switch",
            "rocq_switch requires a non-empty `name` (the opam switch to "
            "activate, e.g. 'rocq9').",
            reason="validation",
        )
    name = name.strip()

    previous = _detect_switch(_resolve_binary(config.ROCQ_COQC_BINARY))["switch"]

    env, error = await asyncio.to_thread(compute_switch_env, name)
    if env is None:
        extra: dict[str, Any] = {}
        switches = await asyncio.to_thread(list_switches)
        name_unknown = switches is not None and name not in switches
        if name_unknown:
            extra["available_switches"] = switches
        # A syntactically-fine name that does not resolve to an installed
        # switch is a name-resolution failure ("not_found", paired with
        # available_switches for typo recovery), matching rocq_start.  The
        # empty-name guard above stays "validation" (input-shape).
        return _fail(
            lifespan_state,
            "rocq_switch",
            error or "switch change failed",
            reason="not_found" if name_unknown else "validation",
            **extra,
        )

    # Apply the new environment + kill pet under _pet_runtime._pet_lock so the mutation
    # cannot interleave with a concurrent _pet_runtime._ensure_pet spawn (which holds the
    # same lock and would otherwise adopt a pet started on the OLD env, then
    # survive our _pet_runtime._invalidate_pet on a live process — no broken pipe, no
    # respawn).  Serializing here guarantees the next spawn sees the new env.
    # The semaphore matches every other pet-mutating path's `async with sem`.
    lock_timeout = (lifespan_state.get("pet_timeout") or config.ROCQ_PET_TIMEOUT) * 0.8

    def _apply_switch() -> bool:
        lock = (
            _pet_runtime._pet_lock
        )  # local ref survives a _pet_runtime._force_release_pet_lock swap
        if not lock.acquire(timeout=lock_timeout):
            return False
        try:
            # Apply the new switch's env, then drop any switch-scoped keys the
            # new switch does NOT set.  update() alone only overwrites keys
            # present in the new env; a key the old switch set but the new one
            # omits (e.g. a stale CAML_LD_LIBRARY_PATH / OPAM_LAST_ENV) would
            # otherwise linger and mis-resolve a later lookup.  Compute both
            # sets first so the mutation window a lock-free reader (rocq_health)
            # can observe stays as narrow as possible.
            new_env = {k: env[k] for k in _SWITCH_ENV_KEYS if k in env}
            stale = [k for k in _SWITCH_ENV_KEYS if k not in env and k in os.environ]
            os.environ.update(new_env)
            for key in stale:
                del os.environ[key]
            # Kill pet + clear the state table + invalidate the import cache
            # (via _pet_runtime._pet_invalidation_hooks).  The next pet-routed call lazily
            # respawns pet under the new environment.
            _pet_runtime._invalidate_pet(lifespan_state)
            return True
        finally:
            lock.release()

    async with _pet_runtime._get_pet_semaphore():
        applied = await asyncio.to_thread(_apply_switch)
    if not applied:
        return _fail(
            lifespan_state,
            "rocq_switch",
            "rocq_switch: pet is busy (lock contention); the switch was not "
            "applied. Retry once in-flight pet calls settle.",
            reason="lock_contended",
        )

    snapshot = await asyncio.to_thread(build_health_snapshot, lifespan_state)
    snapshot["switched"] = True
    snapshot["previous_switch"] = previous
    snapshot["note"] = (
        f"Switched to {snapshot['switch']!r}. pet was killed and the state "
        "table cleared — restart any interactive session with rocq_start. "
        ".vo artifacts built under the previous switch may be "
        "ABI-incompatible; recompile dependencies as needed."
    )
    return snapshot


# ---------------------------------------------------------------------------
# Tool: rocq_search
# ---------------------------------------------------------------------------


@mcp.tool(
    output_schema=SEARCH_OUTPUT_SCHEMA,
    annotations=ToolAnnotations(
        title="Search for lemmas and definitions",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    ),
)
async def rocq_search(
    pattern: str = "",
    patterns: list[str] | None = None,
    kind: str = "",
    inside: list[str] | None = None,
    outside: list[str] | None = None,
    preamble: str = "",
    file: str = "",
    workspace: str = "",
    from_state: int | None = None,
    max_results: int = 30,
    offset: int = 0,
    include_types: bool = True,
    include_warnings: bool = True,
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Search the environment for lemmas/definitions matching a pattern — structured hits.

    Returns ``hits: [{name, type}]`` with ``total`` / ``truncated`` and
    pagination — prefer this over raw ``Search`` through ``rocq_query``
    (one joined string).  Multiple ``patterns`` fan out and merge: each
    hit then carries ``matched_patterns`` (hits matching several
    patterns are the strongest premise candidates).  Same context modes
    as rocq_query: preamble | file | from_state (live proof context).
    A pattern Coq rejects returns ``reason: "query_rejected"``.

    Args:
        pattern: Coq Search pattern, e.g. "(_ + _ = _ + _)" or
            '"comm" (_ * _)'.  Trailing dot optional.
        patterns: Fan-out mode — additional patterns to merge (max 8
            total).
        kind: Restrict via Coq's is: filter, e.g. "Lemma",
            "Definition", "Instance".
        inside: Only results from these modules.
        outside: Exclude results from these modules.
        preamble: Import/scope lines for context.
        file: .v path whose definitions should be in scope (mutually
            exclusive with preamble / from_state).
        workspace: Auto-detected from project markers when omitted.
        from_state: Live state_id to search against (sees hypotheses
            and opened scopes).
        max_results: Page size (default 30).
        offset: Pagination offset into the merged hit list.
        include_types: False returns names only (token-lean for broad
            queries).
        include_warnings: False drops warning-severity feedback.
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT; clamped to
            ROCQ_QUERY_TIMEOUT_CAP.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_search", ctx=ctx, workspace=workspace, file=file, timeout=timeout
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_search(
        pattern=pattern,
        workspace=workspace,
        lifespan_state=lifespan_state,
        patterns=patterns,
        kind=kind,
        inside=inside,
        outside=outside,
        preamble=preamble,
        file=file,
        from_state=from_state,
        max_results=max_results,
        offset=offset,
        include_types=include_types,
        include_warnings=include_warnings,
        timeout=effective_timeout,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_goal
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        title="Show goals at a state or position",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_goal(
    from_state: int | None = None,
    file: str = "",
    line: int | None = None,
    character: int | None = None,
    workspace: str = "",
    goals_format: Literal["pretty", "structured", "names_only"] = "pretty",
    diff_from: int | None = None,
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Show proof goals at a live state_id or a file position — registers no state.

    Pure inspection: unlike ``rocq_start`` (which allocates a session
    state), this leaves the state table untouched — use it to peek at
    goals mid-file or re-read a held state without allocating a new
    entry (reading refreshes the state's LRU recency).
    Position mode uses rocq_start's cursor semantics (0-indexed, rounds
    forward through the sentence — rocq://guide/workflows).
    ``diff_from`` compares two live states (returns ``goals_diff``
    instead of ``goals``) — e.g. two exploration branches.

    Args:
        from_state: Live state_id to inspect (mutually exclusive with
            the file position).
        file: .v path (with line+character) for position mode.
        line: 0-based line (position mode).
        character: 0-based character offset (position mode).
        workspace: Auto-detected from project markers when omitted.
        goals_format: "pretty" (default), "structured", or
            "names_only".
        diff_from: Another live state_id to diff against (requires
            from_state).
        timeout: Seconds; 0 = ROCQ_PET_TIMEOUT.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_goal",
        ctx=ctx,
        workspace=workspace,
        file=file or None,
        timeout=timeout,
    )
    if not isinstance(resolved, tuple):
        return resolved
    workspace, lifespan_state, ws_warning, clamped, effective_timeout = resolved

    result = await run_goal(
        lifespan_state=lifespan_state,
        from_state=from_state,
        file=file,
        line=line,
        character=character,
        workspace=workspace,
        goals_format=goals_format,
        diff_from=diff_from,
        timeout=effective_timeout,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Guides (MCP resources) and workflow prompts
# ---------------------------------------------------------------------------
#
# The tool descriptions carry the per-call contracts; the deep reference
# (recovery matrices, position semantics, concurrency model, verbose
# field docs) lives in markdown guides served as MCP resources — fetched
# only when needed, @-mentionable in Claude Code, zero standing context
# cost.  Content files ship as package data under rocq_mcp/guides/.

_GUIDES_DIR = Path(__file__).parent / "guides"


def _read_guide(name: str) -> str:
    return (_GUIDES_DIR / f"{name}.md").read_text(encoding="utf-8")


@mcp.resource(
    "rocq://guide/workflows",
    name="rocq-workflows",
    mime_type="text/markdown",
    description=(
        "Choosing-a-tool table, the core proof loop, multi-tactic "
        "exploration patterns, rocq_query import/scope rules, scratch "
        "iteration, position semantics, sub-agent briefing."
    ),
)
def guide_workflows() -> str:
    return _read_guide("workflows")


@mcp.resource(
    "rocq://guide/failures",
    name="rocq-failures",
    mime_type="text/markdown",
    description=(
        "Failure recovery playbook: the reason taxonomy with per-reason "
        "recovery, state_capture_status, multi-error entries, "
        "available_in_file, proof_tactics_status, the pet_restarted "
        "diag playbook, and the degraded field."
    ),
)
def guide_failures() -> str:
    return _read_guide("failures")


@mcp.resource(
    "rocq://guide/concurrency",
    name="rocq-concurrency",
    mime_type="text/markdown",
    description=(
        "Sharing one rocq-mcp between agents: LRU state protection, "
        "force_restart recovery, rocq_diag monitoring, per-sub-agent "
        "server + worktree isolation patterns, rocq_switch caveats."
    ),
)
def guide_concurrency() -> str:
    return _read_guide("concurrency")


@mcp.resource(
    "rocq://guide/responses",
    name="rocq-responses",
    mime_type="text/markdown",
    description=(
        "Field-level response reference: optional envelope fields, "
        "truncation caps, compile-file options (keep_vo/mode/timing), "
        "workspace auto-detection, diag/health shapes, size controls."
    ),
)
def guide_responses() -> str:
    return _read_guide("responses")


@mcp.prompt(
    name="prove_theorem",
    description=(
        "Briefing for proving one theorem with the rocq-mcp interactive "
        "loop (start -> step_multi -> check -> compile+verify)."
    ),
)
def prove_theorem(file: str, theorem: str) -> str:
    """Drive the full interactive proof loop for one theorem."""
    return f"""\
Prove the theorem `{theorem}` in `{file}` using the rocq-mcp tools.

Method — use the held interactive session, never a coqc loop:
1. Read `rocq://guide/workflows` if you have not already.
2. `rocq_toc(file="{file}")` if you need to confirm the theorem name.
3. `s = rocq_start(file="{file}", theorem="{theorem}")` — read the goals.
4. Explore with `rocq_step_multi(from_state=s, tactics=[...],
   preset="auto")` — the preset appends the full automation battery
   (deduped, capped at 20; see rocq://guide/workflows).  Add
   structural steps ("intros.", "induction x.", "destruct x.",
   "simpl.") as the goals demand.
5. Commit each winning step with `rocq_check(from_state=..., body=...)`
   and continue from the returned state_id.  On tactic_failed, continue
   from last_valid_state_id — do not restart.
6. When proof_finished is true: write the finished proof into the file
   (imports + statement + Proof. + the proof_tactics + Qed.), then run
   `rocq_compile_file` and `rocq_verify`, and audit axioms with
   `rocq_assumptions(name="{theorem}", file="{file}")`.

Report: the final proof script, the verification verdict, and any
axioms the proof depends on."""


@mcp.prompt(
    name="debug_compile_error",
    description=(
        "Briefing for fixing a .v file that does not compile, using "
        "compile-error state capture and the interactive session."
    ),
)
def debug_compile_error(file: str) -> str:
    """Diagnose and fix a failing .v file."""
    return f"""\
The file `{file}` fails to compile.  Diagnose and fix it with rocq-mcp.

Method:
1. `rocq_compile_file(file="{file}")` — read `reason`,
   `error_positions`, and (if present) the per-declaration `errors`
   list to see every failing declaration, not just the first.
2. If the response carries `state_capture_status: "ok"`, continue
   directly from the captured proof state:
   `rocq_step_multi(from_state=<state_id>, tactics=[...])` /
   `rocq_check(from_state=<state_id>, ...)`.  Otherwise open the error
   position yourself: `rocq_start(file="{file}", line=<line>,
   character=<char>)` (0-indexed; see rocq://guide/failures).
3. Find a working replacement for the broken step, edit the file, and
   recompile.  Repeat for each entry in `errors`.
4. Finish with a clean `rocq_compile_file` run — and `rocq_verify` if
   the fix touched a proof of a stated problem.

Report: each error found, the fix applied, and the final compile
status."""


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> None:
    """Run the MCP server."""
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
