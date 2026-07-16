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
import re
import shutil
import signal
import subprocess
import threading
import time
import warnings
from pathlib import Path
from typing import Any, Callable, Literal

import psutil
from fastmcp import FastMCP, Context
from fastmcp.server.lifespan import lifespan
from mcp.types import ToolAnnotations

import rocq_mcp

# ---------------------------------------------------------------------------
# Configuration (env vars with defaults)
# ---------------------------------------------------------------------------
# Env-derived configuration lives in rocq_mcp.config (single definition
# site).  The names are re-bound here because submodules read them as
# ``_server.<NAME>`` and tests monkeypatch them on this module — both
# work against these bindings, since server code reads its own globals.
from rocq_mcp.config import (
    _COMPILE_MULTI_ERROR_CAP,
    _COMPILE_MULTI_ERROR_TIMEOUT,
    _MEMORY_WATCHDOG_INTERVAL,
    _RECENT_ERRORS_MAX,
    _ROCQ_WORKSPACE_EXPLICIT,
    ROCQ_COQC_BINARY,
    ROCQ_COQC_TIMEOUT,
    ROCQ_MAX_PET_RSS_MB,
    ROCQ_MAX_SOURCE_SIZE,
    ROCQ_PET_TIMEOUT,
    ROCQ_QUERY_TIMEOUT_CAP,
    ROCQ_VERIFY_TIMEOUT,
    ROCQ_WORKSPACE,
    _default_max_pet_rss_mb,
)


def _check_timeout_config(pet_timeout: float, cap: int) -> str | None:
    """Return a warning if ROCQ_PET_TIMEOUT exceeds ROCQ_QUERY_TIMEOUT_CAP.

    The cap is documented in the README as the upper bound for the
    per-call timeout, but ROCQ_PET_TIMEOUT is the fallback when no
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


_timeout_config_msg = _check_timeout_config(ROCQ_PET_TIMEOUT, ROCQ_QUERY_TIMEOUT_CAP)
if _timeout_config_msg:
    warnings.warn(_timeout_config_msg, RuntimeWarning, stacklevel=2)


# Single source of truth for the per-call "pytanque ImportError" envelope hint.
# Used by _ensure_pet, _run_with_pet, run_check, and run_step_multi — all of
# which surface this string in the ``error`` field of their {success:false,
# reason:"unavailable"} envelope.  Centralized so future copy churn cannot
# resurrect a phantom ``pip install 'rocq-mcp[interactive]'`` recipe (no
# ``[interactive]`` extra exists; petanque ships with coq-lsp).
_PYTANQUE_NOT_INSTALLED_HINT = (
    "pytanque is not installed. Petanque (the `pet` binary and the matching "
    "pytanque Python binding) ships with coq-lsp — see "
    "https://github.com/ejgallego/coq-lsp for install instructions "
    "appropriate to your environment."
)


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
        "workspace": ROCQ_WORKSPACE,
        "pet_timeout": ROCQ_PET_TIMEOUT,
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
            _kill_pet(client)
        # Clean up cache file
        ws = state.get("workspace")
        if ws:
            cache_file = Path(ws) / f"rocq_mcp_cache_{os.getpid()}_.v"
            _cleanup_coqc_artifacts(str(cache_file))


# Always-visible server guidance.  With deferred tool loading (the default
# in Claude Code) tool descriptions may not be in context until a tool is
# looked up — these instructions are the one place cross-tool knowledge is
# guaranteed to be visible.  Budget: keep under ~2,200 characters (enforced
# by tests/test_mcp_surface.py).
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
unavailable, tactic_failed, compile_error, axiom_dependency, \
type_mismatch. When a response carries pet_restarted: true, call \
rocq_diag to see what happened.

Timeouts: timeout=0 means "use the server default"; larger per-call \
values are clamped to a server cap and the response then carries \
clamped_timeout.

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

# Full set of artifacts cleaned around coqc invocations on temp files
# (see :func:`_cleanup_coqc_artifacts`).  The user-file path in
# :func:`rocq_mcp.compile._run_coqc_file` consumes this set too but
# additionally honours ``keep_vo=True`` via the ``_VO_FAMILY`` subset
# defined alongside that helper in ``compile.py``.
_CLEANUP_EXTENSIONS: tuple[str, ...] = (
    ".v",
    ".vo",
    ".vok",
    ".vos",
    ".glob",
    ".aux",
    ".vio",
    ".timing",
    ".coqaux",
)


def _path_within(needle: Path, haystack: Path) -> bool:
    """Return True if *needle* is *haystack* or a path inside it.

    Both arguments must already be resolved/absolute; this function
    does NOT call ``resolve()`` itself (callers sometimes need
    different resolution semantics, e.g. avoiding symlink-following).
    Single source of truth for the path-containment security boundary.
    """
    return needle == haystack or str(needle).startswith(str(haystack) + os.sep)


def _validate_workspace(workspace: str) -> str | None:
    """Return error message if workspace is invalid, None if OK."""
    ws = Path(workspace).resolve()
    # Only enforce containment when ROCQ_WORKSPACE was explicitly set
    if _ROCQ_WORKSPACE_EXPLICIT:
        root = Path(ROCQ_WORKSPACE).resolve()
        if not _path_within(ws, root):
            return f"Workspace must be within {root}"
    if not ws.is_dir():
        return f"Workspace directory does not exist: {ws}"
    if not os.access(ws, os.W_OK):
        return f"Workspace directory is not writable: {ws}"
    return None


def _resolve_call_timeout(
    timeout: int | float | None,
) -> tuple[float | None, bool]:
    """Resolve a per-call timeout against ``ROCQ_QUERY_TIMEOUT_CAP``.

    Returns ``(effective_timeout, clamped)``:

    - When *timeout* is ``None``, 0, or negative: ``(None, False)`` —
      caller falls back to ``ROCQ_PET_TIMEOUT``.
    - Otherwise: ``(float(min(timeout, cap)), timeout > cap)``.

    Shared by every pet-routed wrapper so the clamp behaviour and
    ``clamped_timeout`` echo stay in lockstep.
    """
    if timeout is None or timeout <= 0:
        return None, False
    clamped = timeout > ROCQ_QUERY_TIMEOUT_CAP
    return float(min(timeout, ROCQ_QUERY_TIMEOUT_CAP)), clamped


def _cleanup_coqc_artifacts(tmp_path: str) -> None:
    """Remove all coqc output artifacts for a temp file."""
    base = Path(tmp_path).with_suffix("")
    for ext in _CLEANUP_EXTENSIONS:
        base.with_suffix(ext).unlink(missing_ok=True)


# Allowlisted -arg values for _CoqProject / _RocqProject parsing.
# Only exact matches or prefix matches are allowed; everything else is
# silently dropped to prevent coqc flag injection (e.g. -load-vernac-source).
_SAFE_COQC_ARGS: frozenset[str] = frozenset(
    {
        "-noinit",
        "-indices-matter",
        "-impredicative-set",
        "-allow-rewrite-rules",
        "-allow-sprop",
        "-cumulative-sprop",
    }
)
_SAFE_COQC_ARG_PREFIXES: tuple[str, ...] = ("-w ",)


def _is_safe_arg(value: str) -> bool:
    """Check if an -arg value is in the allowlist."""
    return value in _SAFE_COQC_ARGS or any(
        value.startswith(p) for p in _SAFE_COQC_ARG_PREFIXES
    )


def _check_path_containment(ws: Path, dir_arg: str) -> str | None:
    """Resolve dir_arg relative to ws and return it if within ws, else None."""
    if os.path.isabs(dir_arg):
        return None
    if _path_within((ws / dir_arg).resolve(), ws.resolve()):
        return dir_arg
    return None


def _resolve_file_in_workspace(file: str, workspace: str) -> str:
    """Resolve *file* relative to *workspace* and verify containment.

    Returns the resolved absolute path as a string.

    Raises:
        ValueError: If the resolved path escapes the workspace.
        FileNotFoundError: If the file does not exist on disk.
    """
    ws_resolved = Path(workspace).resolve()
    resolved = (ws_resolved / file).resolve()
    if not _path_within(resolved, ws_resolved):
        raise ValueError("File path must be within workspace.")
    if not resolved.is_file():
        raise FileNotFoundError(f"File not found: {file}")
    return str(resolved)


_PROJECT_MARKERS: tuple[str, ...] = ("_RocqProject", "_CoqProject", "dune-project")


def _find_project_root_from_file(file: str | None) -> str | None:
    """Walk up from *file* looking for a Rocq project marker.

    Walks UP from the file's directory; returns the deepest directory
    containing any of :data:`_PROJECT_MARKERS` (``_RocqProject``,
    ``_CoqProject``, ``dune-project``), or ``None`` if no marker is
    found before the filesystem root.  Depth wins: a higher directory's
    marker never overrides a deeper directory's marker, regardless of
    marker type.  Tuple order on :data:`_PROJECT_MARKERS` is the
    tiebreaker only when a single directory contains more than one
    marker.

    Used by file-accepting tools to auto-detect ``workspace`` when the
    caller does not pass one explicitly; for monorepos with nested
    project files, callers can still pass ``workspace=`` to override.

    Relative paths are resolved against ``ROCQ_WORKSPACE``; symlinks
    are not followed.
    """
    if not file:
        return None
    try:
        p = Path(file)
        if not p.is_absolute():
            p = Path(ROCQ_WORKSPACE) / p
        # Lexical absolute path -- avoids following symlinks so the walk
        # stays in the user-provided namespace.
        p = p.absolute()
    except (OSError, ValueError):
        return None
    if p.is_file():
        p = p.parent
    while True:
        for marker in _PROJECT_MARKERS:
            if (p / marker).is_file():
                return str(p)
        if p.parent == p:
            return None
        p = p.parent


def _find_dune_root(ws: Path) -> Path | None:
    """Walk up from *ws* looking for ``dune-project``.  Returns the
    directory containing it, or ``None`` if none is found before /."""
    check = ws.resolve()
    while True:
        if (check / "dune-project").is_file():
            return check
        parent = check.parent
        if parent == check:
            return None
        check = parent


def _workspace_has_project_marker(ws: Path) -> bool:
    """True iff *ws* (or an ancestor, for dune) has a project marker.

    Existence check only — does not return *which* marker matched.  Marker
    tuple order in :data:`_PROJECT_MARKERS` is irrelevant here; this helper
    short-circuits on the first match in *ws* itself, then falls back to
    the dune ancestor walk.

    Mirrors both paths _parse_project_flags consults before falling through
    to the synthetic ["-Q", ws, "Test"] last resort:

    - direct file match: ``_RocqProject``, ``_CoqProject``, or
      ``dune-project`` in *ws* itself; and
    - dune ancestor match: ``_find_dune_root`` walks UP from *ws* looking
      for a ``dune-project``, matching ``_parse_dune_flags``'s upward
      walk via ``dune coq top``.  This prevents spurious warnings on a
      subdir of a dune project (e.g. ``mathcomp/theories/algebra/``)
      that has no local marker file of its own.
    """
    if any((ws / m).is_file() for m in _PROJECT_MARKERS):
        return True
    # Mirror _parse_project_flags's second path: dune detection walks up.
    return _find_dune_root(ws) is not None


# Advisory warning attached when the resolved workspace has no project
# marker — the user likely passed an ancestor of the project root, and
# _parse_project_flags will fall through to synthetic ["-Q", ws, "Test"]
# flags that don't carry the project's library aliases.  Surfaced to
# agents so they have an actionable hint instead of opaque coq-lsp
# "not found" errors.
_WORKSPACE_NO_MARKER_WARNING = (
    "No _RocqProject / _CoqProject / dune-project found in workspace '{ws}'. "
    "Library aliases (-R / -Q) are unset; unqualified library references "
    "(e.g. names from your project's -R / -Q aliases) may fail to resolve. "
    "If you have a `file=` argument, omit `workspace=` to auto-detect from "
    "the file's location; otherwise pass `workspace=` pointing at the "
    "directory containing a _RocqProject / _CoqProject / dune-project file."
)


def _maybe_workspace_warning(
    workspace: str, *, explicit: bool, file_provided: bool
) -> str | None:
    """Return an advisory warning when *workspace* lacks a project marker.

    Fires when the resolved workspace has no marker AND one of:

    - the user explicitly passed ``workspace=`` (likely picked an
      ancestor of the actual project root — the bug from the workspace
      no-marker field report), or
    - a ``file=`` argument was provided and the upward walk from it
      still didn't find a marker (auto-detect returned ``None`` and
      we fell back to ``ROCQ_WORKSPACE``, which itself has no marker).

    Stays quiet for the markerless-by-design case: tools that don't
    take ``file=`` (e.g. ``rocq_compile`` with source-string, default
    ``rocq_notations``) running against a markerless ``ROCQ_WORKSPACE``
    — that's a legitimate one-off / scratch workflow, not a config bug.
    """
    if _workspace_has_project_marker(Path(workspace)):
        return None
    if not (explicit or file_provided):
        return None
    return _WORKSPACE_NO_MARKER_WARNING.format(ws=workspace)


# Advisory warning attached when ``rocq_compile_file`` rewrites ``.vo``
# files in a workspace that has active interactive sessions.  Multi-agent
# setups can otherwise hit confusing failures: pet keeps memo-serving the
# pre-rebuild dependency, and downstream errors look like phantom name
# resolution / type mismatches.  Tells the affected agent to restart.
_VO_REBUILD_WARNING = (
    "rocq_compile_file rebuilt {n} .vo file(s) in workspace '{ws}'. "
    "{m} interactive session(s) in this workspace may be holding stale "
    "dependency state — call rocq_start again to refresh."
)


# Bound on how many .vo paths we will mtime-snapshot per call.  Cheap
# insurance against pathological workspaces (e.g. a vendored opam switch
# accidentally pointed at as the workspace root).  Workspaces above this
# cap stay quiet rather than slow down every compile.
_VO_SCAN_FILE_CAP: int = 5000


# Directory names skipped during the .vo walk: VCS metadata and common
# cache / build areas that won't carry interactively-loaded dependencies
# we care about for staleness.
_VO_SCAN_SKIP_DIRS: frozenset[str] = frozenset(
    {".git", ".hg", ".svn", ".cache", "__pycache__", "node_modules"}
)


def _snapshot_vo_mtimes(workspace: Path) -> dict[str, float] | None:
    """Walk *workspace* for ``.vo`` files and return ``{abspath: mtime}``.

    Returns ``None`` (sentinel for "unscanned") when the workspace exceeds
    :data:`_VO_SCAN_FILE_CAP` or when the walk hits an :class:`OSError` —
    better to stay quiet than to emit a half-truth warning.  Does not
    follow symlinks for directory descent; prunes hidden / build / cache
    dirs.

    Uses :func:`os.scandir` so the per-file ``stat`` is served from the
    ``DirEntry`` cache — at the file cap, that's the difference between
    one and two syscalls per ``.vo``.
    """
    try:
        ws_abs = workspace.resolve()
    except OSError:
        return None
    result: dict[str, float] = {}
    stack: list[str] = [str(ws_abs)]
    try:
        while stack:
            cur = stack.pop()
            with os.scandir(cur) as it:
                for entry in it:
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            if entry.name not in _VO_SCAN_SKIP_DIRS:
                                stack.append(entry.path)
                            continue
                        if not entry.name.endswith(".vo"):
                            continue
                        # follow_symlinks=False keeps the DirEntry stat cache hot;
                        # symlinked .vo files are rare in real Rocq projects.
                        st = entry.stat(follow_symlinks=False)
                    except OSError:
                        # A racing rebuild may have replaced the file mid-walk;
                        # skip rather than abort the whole scan.
                        continue
                    result[os.path.abspath(entry.path)] = st.st_mtime
                    if len(result) > _VO_SCAN_FILE_CAP:
                        return None
    except OSError:
        return None
    return result


def _diff_vo_mtimes(before: dict[str, float], after: dict[str, float]) -> list[str]:
    """Return abspaths whose mtime changed or that are newly present.

    Deletions (in ``before`` but not ``after``) are not counted: they
    cannot make a held pet session stale on their own — only rewrites
    and new compiled artifacts can.
    """
    changed: list[str] = []
    for path, mtime in after.items():
        prev = before.get(path)
        if prev is None or prev != mtime:
            changed.append(path)
    return changed


def _count_sessions_in_workspace(workspace: Path) -> int:
    """Number of state-table entries with a resolved file under *workspace*.

    Function-body import of ``_state_table`` to avoid the circular import
    that would land if ``server.py`` pulled ``interactive`` in at module
    load (server defines shared infra ``interactive`` consumes).  Mirrors
    the pattern used by ``compile_enrichment._capture_compile_error_state``.
    """
    from rocq_mcp.interactive import _state_table

    try:
        ws_abs = workspace.resolve()
    except OSError:
        return 0
    count = 0
    for entry in _state_table.values():
        rf = entry.resolved_file
        if rf is None:
            continue
        try:
            rf_path = Path(rf).resolve()
        except OSError:
            continue
        if _path_within(rf_path, ws_abs):
            count += 1
    return count


def _maybe_vo_rebuild_warning(
    workspace: str,
    *,
    before_mtimes: dict[str, float] | None,
    after_mtimes: dict[str, float] | None,
) -> str | None:
    """Return an advisory warning when rebuilt .vo files coincide with
    active interactive sessions in the same workspace.

    Quiet when either snapshot is ``None`` (workspace too large to scan
    or an I/O error during the walk), when no ``.vo`` was rewritten, or
    when no interactive session in this workspace would be affected.
    """
    if before_mtimes is None or after_mtimes is None:
        return None
    rebuilt = _diff_vo_mtimes(before_mtimes, after_mtimes)
    if not rebuilt:
        return None
    sessions = _count_sessions_in_workspace(Path(workspace))
    if sessions == 0:
        return None
    return _VO_REBUILD_WARNING.format(n=len(rebuilt), m=sessions, ws=workspace)


_DUNE_HEADER = "# Auto-generated by rocq-mcp from dune\n"


_COQ_THEORY_RE = re.compile(r"^\s*\(coq\.theory\b", re.MULTILINE)


def _pick_v_file(directory: Path) -> Path | None:
    """Return a representative ``.v`` file under *directory*, preferring
    shallow source files and skipping ``_build/``.

    After ``dune build`` the build dir contains ``.v`` artifacts under
    ``_build/default/<theory>/``; feeding one of those to
    ``dune coq top`` confuses dune.  Shallow ``*.v`` covers the common
    case quickly; the recursive fallback handles
    ``(include_subdirs qualified)`` layouts.
    """
    for candidate in directory.glob("*.v"):
        return candidate
    for candidate in directory.glob("**/*.v"):
        if "_build" in candidate.parts:
            continue
        return candidate
    return None


def _find_coq_theory_dirs(ws: Path) -> list[Path]:
    """Return all directories under *ws* whose ``dune`` file declares a
    ``(coq.theory ...)`` stanza.

    Anchored regex: the stanza must begin a line (optionally indented)
    with ``(coq.theory`` followed by a word boundary.  This avoids
    false positives in line comments (``; (coq.theory ...)``) while
    matching every well-formed top-level stanza.  Used only to
    *enumerate* theory roots so we know how many ``dune coq top``
    calls to make; the returned flags themselves still come from
    ``dune coq top`` (the source of truth for paths and flags).
    """
    dirs: list[Path] = []
    for dune_file in ws.glob("**/dune"):
        try:
            content = dune_file.read_text()
        except OSError:
            continue
        if _COQ_THEORY_RE.search(content):
            dirs.append(dune_file.parent)
    return dirs


def _run_dune_coq_top(
    v_rel: str, dune_root: Path, timeout: int = 10
) -> list[str] | None:
    """Run ``dune coq top --toplevel echo --no-build <v_rel>`` from
    *dune_root* and return the parsed shell args, or ``None`` on
    subprocess failure / nonzero exit / parse error."""
    try:
        result = subprocess.run(
            ["dune", "coq", "top", "--toplevel", "echo", "--no-build", v_rel],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(dune_root),
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    import shlex

    try:
        return shlex.split(result.stdout.strip())
    except ValueError:
        return None


def _dune_path_to_ws_relative(dir_arg: str, ws: Path, dune_root: Path) -> str | None:
    """Validate a path from ``dune coq top`` output and make it relative to *ws*.

    Accepts paths within the dune project root.  Returns a relative
    path string (relative to *ws*) or ``None`` if the path is outside
    the project root.
    """
    if os.path.isabs(dir_arg):
        resolved = Path(dir_arg).resolve()
        resolved_str = str(resolved)
        # Must be within the dune project root.
        if resolved_str != str(dune_root) and not resolved_str.startswith(
            str(dune_root) + os.sep
        ):
            return None
        try:
            return str(resolved.relative_to(ws.resolve()))
        except ValueError:
            # Outside ws but within dune_root -- use os.path.relpath.
            return os.path.relpath(str(resolved), str(ws.resolve()))
    if _check_path_containment(ws, dir_arg) is not None:
        return dir_arg
    return None


def _select_representative_v_files(ws: Path) -> list[Path]:
    """Pick one ``.v`` per ``(coq.theory ...)`` directory under *ws*.

    Falls back to a single arbitrary ``.v`` from *ws* when 0 or 1
    theory roots are found, preserving the original single-query
    behavior for non-multi-theory dune projects.  Returns an empty
    list if no usable ``.v`` files exist.
    """
    rep_files: list[Path] = []
    theory_dirs = _find_coq_theory_dirs(ws)
    if len(theory_dirs) >= 2:
        for theory_dir in theory_dirs:
            v_file = _pick_v_file(theory_dir)
            if v_file is not None:
                rep_files.append(v_file)
    if not rep_files:
        v_file = _pick_v_file(ws)
        if v_file is not None:
            rep_files = [v_file]
    return rep_files


def _parse_dune_args(
    args: list[str], ws: Path, dune_root: Path
) -> tuple[list[str], list[str]]:
    """Parse a flat list of ``dune coq top`` args, deduping by semantic key.

    Returns ``(coqc_flags, rocqproject_lines)`` -- the first is what
    we hand to ``coqc``; the second is what we write to ``_RocqProject``
    so coq-lsp picks up the same load paths.

    Dedup keys: ``(-Q|-R, dir, name)`` / ``(-I, dir)`` / ``(-w, spec)`` /
    ``(-noinit,)``.  Required because running ``dune coq top`` against
    multiple theories returns shared stdlib / ``-w`` flags every time.
    """
    seen: set[tuple] = set()
    flags: list[str] = []
    lines: list[str] = []

    def _emit(key: tuple, flag_args: list[str], line: str) -> None:
        if key in seen:
            return
        seen.add(key)
        flags.extend(flag_args)
        lines.append(line)

    i = 0
    while i < len(args):
        a = args[i]
        if a in ("-R", "-Q") and i + 2 < len(args):
            rel = _dune_path_to_ws_relative(args[i + 1], ws, dune_root)
            if rel is not None:
                logical = args[i + 2]
                _emit((a, rel, logical), [a, rel, logical], f"{a} {rel} {logical}")
            i += 3
        elif a == "-I" and i + 1 < len(args):
            rel = _dune_path_to_ws_relative(args[i + 1], ws, dune_root)
            if rel is not None:
                _emit(("-I", rel), ["-I", rel], f"-I {rel}")
            i += 2
        elif a == "-w" and i + 1 < len(args):
            spec = args[i + 1]
            # _CoqProject ``-arg`` takes a single argument per line.
            _emit(("-w", spec), ["-w", spec], f"-arg -w\n-arg {spec}")
            i += 2
        elif a == "-noinit":
            _emit(("-noinit",), ["-noinit"], "-arg -noinit")
            i += 1
        else:
            i += 1
    return flags, lines


def _parse_dune_flags(ws: Path) -> list[str] | None:
    """Extract coqc flags from a dune project via ``dune coq top``.

    If a ``dune-project`` file exists in *ws* (or a parent), discovers
    every ``(coq.theory ...)`` directory under *ws*, runs ``dune coq
    top --toplevel echo --no-build <file.v>`` once per theory (using a
    representative ``.v`` from each), and unions the resulting flags
    (deduplicated).  This is required for dune workspaces with multiple
    coq theories: querying a single theory yields flags for that theory
    only, leaving cross-theory imports silently broken.

    On success, writes a ``_RocqProject`` file in *ws* so that both
    coqc and coq-lsp (interactive tools) use the correct load paths.
    Existing user-created ``_RocqProject`` or ``_CoqProject`` files
    are never overwritten.  The generated file stays in the workspace
    and should be added to ``.gitignore``.

    Returns a list of coqc flags, or ``None`` if dune detection fails
    (no dune-project, no .v files, dune not installed, etc.).

    Security: paths are validated to stay within the dune project root
    (the directory containing ``dune-project``).  Absolute paths outside
    the project root (e.g. system stdlib) are silently dropped since
    coqc already knows about them.  Accepted absolute paths are
    converted to relative paths (relative to *ws*) in the generated
    ``_RocqProject``.
    """
    dune_root = _find_dune_root(ws)
    if dune_root is None:
        return None

    rep_files = _select_representative_v_files(ws)
    if not rep_files:
        return None

    # Run dune coq top once per representative file and union the args.
    all_args: list[str] = []
    for v_file in rep_files:
        try:
            v_rel = v_file.resolve().relative_to(dune_root)
        except ValueError:
            continue
        args = _run_dune_coq_top(str(v_rel), dune_root)
        if args is not None:
            all_args.extend(args)
    if not all_args:
        return None

    flags, lines = _parse_dune_args(all_args, ws, dune_root)
    if not flags:
        return None

    # Write _RocqProject in ws so coq-lsp also picks up the load paths.
    if not (ws / "_RocqProject").is_file() and not (ws / "_CoqProject").is_file():
        try:
            (ws / "_RocqProject").write_text(_DUNE_HEADER + "\n".join(lines) + "\n")
        except OSError:
            pass  # Non-fatal: coqc tools still work via returned flags.

    return flags


def _parse_project_flags(ws: Path) -> list[str]:
    """Parse _RocqProject or _CoqProject and return coqc flags.

    Looks for ``_RocqProject`` first, then ``_CoqProject`` as fallback.
    If neither exists, tries to detect a dune project via
    ``dune coq top``.  If that also fails, returns
    ``["-Q", str(ws), "Test"]`` as a last resort.

    Recognised directives: ``-Q``, ``-R``, ``-I``, ``-arg``.
    Comment lines (starting with ``#``), ``.v`` file entries, and bare
    directory names are silently skipped.

    Security:
    - ``-arg`` values are checked against an allowlist to prevent
      coqc flag injection (e.g. ``-load-vernac-source``).
    - Directory paths in ``-Q``/``-R``/``-I`` are validated to stay
      within the workspace (absolute paths and ``../`` escapes rejected).
    """
    for name in ("_RocqProject", "_CoqProject"):
        proj = ws / name
        if proj.is_file():
            break
    else:
        # No project file — try dune detection.
        dune_flags = _parse_dune_flags(ws)
        if dune_flags is not None:
            return dune_flags
        return ["-Q", str(ws), "Test"]

    flags: list[str] = []
    lines = proj.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if not line or line.startswith("#"):
            i += 1
            continue
        if line == "-arg" and i + 1 < len(lines):
            value = lines[i + 1].strip()
            if _is_safe_arg(value):
                flags.extend(value.split(None, 1))
            i += 2
        elif line.startswith("-arg "):
            value = line[len("-arg ") :].strip()
            if _is_safe_arg(value):
                flags.extend(value.split(None, 1))
            i += 1
        elif line.startswith(("-R ", "-Q ")):
            parts = line.split(None, 2)
            if len(parts) == 3 and _check_path_containment(ws, parts[1]) is not None:
                flags.extend(parts)
            i += 1
        elif line.startswith("-I "):
            parts = line.split(None, 1)
            if len(parts) == 2 and _check_path_containment(ws, parts[1]) is not None:
                flags.extend(parts)
            i += 1
        else:
            i += 1
    return flags


# ---------------------------------------------------------------------------
# Pet subprocess management
# ---------------------------------------------------------------------------

# Global lock for ALL pytanque operations. Pytanque's stdio pipe is
# single-duplex -- concurrent reads/writes corrupt JSON-RPC framing.
# NOTE: _pet_lock may be replaced after a timeout (see _force_release_pet_lock).
# All _execute functions must capture a local reference before acquiring.
_pet_lock = threading.Lock()

# Callbacks invoked when pet is invalidated (crash, timeout).
# interactive.py registers _invalidate_import_cache and _state_invalidate_all
# here to break the circular dependency (server -> interactive -> server).
_pet_invalidation_hooks: list[Callable[[], None]] = []


class _PetLockTimeout(Exception):
    """Lock acquisition timed out (distinct from asyncio.TimeoutError).

    On Python 3.11+, TimeoutError *is* asyncio.TimeoutError. Using a
    private class prevents lock contention from being caught by the
    asyncio.wait_for timeout handler, which would incorrectly kill pet
    and destroy the proof session.
    """


async def _force_release_pet_lock() -> None:
    """Recover from a deadlocked _pet_lock after timeout.

    After _invalidate_pet kills the pet process, the orphaned thread's
    blocking pet.run() should fail and release the lock.  We wait briefly
    for this natural release.  If the lock is still held after a grace
    period, replace the global lock with a fresh one so subsequent
    operations can proceed.

    This is safe because every _execute function captures a local
    reference to the lock before acquiring it, so the orphaned thread
    releases its own (now-discarded) lock object.

    Runs the blocking acquire in a thread to avoid stalling the event loop.
    """

    def _try_reacquire() -> bool:
        lock = _pet_lock  # capture local ref
        if lock.acquire(timeout=2):
            lock.release()
            return True
        return False

    global _pet_lock
    if await asyncio.to_thread(_try_reacquire):
        return
    # Orphaned thread still holds the lock -- replace with fresh lock
    _pet_lock = threading.Lock()


def _ensure_pet(lifespan_state: dict[str, Any]) -> Any:
    """Lazy-initialize pet subprocess. Must be called with _pet_lock held."""
    try:
        from pytanque import Pytanque, PytanqueMode
    except ImportError:
        raise ImportError(_PYTANQUE_NOT_INSTALLED_HINT)

    pet = lifespan_state.get("pet_client")
    if pet is None or not _pet_alive(pet):
        if pet is not None:
            _kill_pet(pet)  # Full cleanup: kill + wait + close FDs
            for hook in _pet_invalidation_hooks:
                hook()
        pet = Pytanque(mode=PytanqueMode.STDIO)
        pet.connect()
        # Attempt process group setup for clean kill.
        # May fail on macOS if child already exec'd -- that's OK,
        # os.getpgid at kill time handles it.
        if pet.process:
            try:
                os.setpgid(pet.process.pid, pet.process.pid)
                pet._own_pgrp = True
            except OSError:
                pet._own_pgrp = False
        else:
            pet._own_pgrp = False
        # Count *only* successful spawns so a fresh server reports
        # pet_restarts=0 even if a previous spawn raised before reaching
        # this point.  The bookkeeping below is the canonical "spawn
        # succeeded" point.
        prev_spawns: int = int(lifespan_state.get("total_spawns", 0))
        if prev_spawns > 0:
            # Reset peak RSS so "headroom before vm_compute" reflects the
            # live pet, not a long-dead predecessor that may have pushed
            # the peak high.  Reset *before* assigning ``pet_client`` so
            # the watchdog cannot sample the new pet's RSS, write it to
            # ``peak_pet_rss_mb``, and then have us wipe it.
            lifespan_state["peak_pet_rss_mb"] = 0.0
        lifespan_state["pet_client"] = pet
        lifespan_state["pet_started_at"] = time.time()
        lifespan_state["total_spawns"] = prev_spawns + 1
    return pet


def _pet_alive(pet: Any) -> bool:
    """Check if the pet subprocess is still running."""
    return pet is not None and pet.process is not None and pet.process.poll() is None


def _kill_pet(pet: Any) -> None:
    """Kill pet and its entire process group.

    If the pet has its own process group (_own_pgrp=True), uses os.killpg
    to kill the whole group (pet + coq-lsp). Otherwise falls back to
    process.terminate()/kill() to avoid killing our own process group.
    """
    if pet is None or pet.process is None:
        return
    # If process already exited, just close FDs — no signals needed.
    # This avoids PID-reuse races where os.killpg could kill an unrelated process.
    if pet.process.poll() is not None:
        _try_close_pet(pet)
        return
    try:
        if getattr(pet, "_own_pgrp", False):
            # Safe: pet has its own process group
            pgid = os.getpgid(pet.process.pid)
            os.killpg(pgid, signal.SIGTERM)
        else:
            # Fallback: only kill the direct child
            pet.process.terminate()
        try:
            pet.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            if getattr(pet, "_own_pgrp", False):
                pgid = os.getpgid(pet.process.pid)
                os.killpg(pgid, signal.SIGKILL)
            else:
                pet.process.kill()
            pet.process.wait(timeout=3)
    except (OSError, ChildProcessError, subprocess.TimeoutExpired):
        # Process already dead, group doesn't exist, or refused to die
        pass
    # Close pipe file descriptors
    _try_close_pet(pet)


def _try_close_pet(pet: Any) -> None:
    """Close pytanque's pipe file descriptors without killing."""
    if pet is None or pet.process is None:
        return
    for stream in [pet.process.stdin, pet.process.stdout, pet.process.stderr]:
        try:
            if stream:
                stream.close()
        except Exception:
            # Best-effort FD cleanup -- the pipe may already be closed,
            # the peer may be dead, or the buffer may be in any state.
            # Any further error here is uninteresting; we only care that
            # we tried to close every FD we hold.
            pass


def _invalidate_pet(lifespan_state: dict[str, Any]) -> None:
    """Kill pet and set to None so next call respawns.

    Does NOT acquire _pet_lock — this is intentional. After a timeout,
    an orphaned thread may still hold the lock. The OS-level kill is safe
    to call without the lock (it's a signal, not a protocol operation).
    The next _ensure_pet call (under _pet_lock) will see the dead process
    and respawn.

    Note: there is a brief race window where a concurrent _ensure_pet
    call may have already read pet_client before this function sets it
    to None.  The stale pet object will fail with a broken-pipe error,
    which is caught by the caller's broad exception handler and triggers
    a respawn on the next call.
    """
    pet = lifespan_state.get("pet_client")
    if pet:
        _kill_pet(pet)
    lifespan_state["pet_client"] = None
    lifespan_state["current_workspace"] = None
    lifespan_state["pet_generation"] = lifespan_state.get("pet_generation", 0) + 1
    for hook in _pet_invalidation_hooks:
        hook()


def _set_workspace_if_needed(
    pet: Any, workspace: str, lifespan_state: dict[str, Any]
) -> None:
    """Set pet workspace, skipping if already set to the same directory.

    Side-effect: invokes :func:`_parse_project_flags` before
    ``pet.set_workspace`` so that any dune-derived ``_RocqProject`` is
    materialised on disk *before* coq-lsp indexes the workspace.
    Without this, pet-based tools on a fresh dune workspace would see a
    workspace with no project file, falling back to single-theory load
    paths and breaking cross-theory imports (pytanque issue #17).
    """
    ws = str(Path(workspace).resolve())
    if lifespan_state.get("current_workspace") != ws:
        _parse_project_flags(Path(ws))
        pet.set_workspace(debug=False, dir=ws)
        lifespan_state["current_workspace"] = ws


# ---------------------------------------------------------------------------
# Semaphore (shared by interactive tools)
# ---------------------------------------------------------------------------

# Async-level serialization to prevent deadlock on timeout.
# Unlike threading.Lock, asyncio.Semaphore is released even when the
# thread is orphaned by asyncio.wait_for timeout.
# Shared across ALL pet operations (step + query) because pytanque's
# stdio pipe is single-duplex.
_pet_semaphore: asyncio.Semaphore | None = None


def _get_pet_semaphore() -> asyncio.Semaphore:
    """Lazy-init the semaphore (must be created inside a running event loop)."""
    global _pet_semaphore
    if _pet_semaphore is None:
        _pet_semaphore = asyncio.Semaphore(1)
    return _pet_semaphore


def _merge_partial_state(resp: dict[str, Any], partial: dict[str, Any]) -> None:
    """Merge *partial* into *resp* without overwriting control keys.

    Keys like ``"success"``, ``"error"``, and ``"pet_restarted"`` are set by
    the error handler and must not be clobbered by user-provided partial state.
    """
    for k, v in partial.items():
        if k not in resp:
            resp[k] = v


# The failure-reason taxonomy and the envelope/degradation helpers moved
# to leaf modules (single source of truth; no import cycle).  The names
# below stay bound on this module because submodules and tests access
# them as ``_server.<name>`` — see rocq_mcp/taxonomy.py and
# rocq_mcp/envelope.py for the definitions.
from rocq_mcp.envelope import (  # noqa: E402
    _RECENT_ERROR_MESSAGE_LIMIT,  # noqa: F401  (re-export for tests)
    _fail,
    _no_ctx_fail,
    _record_error,
)
from rocq_mcp.taxonomy import (  # noqa: E402
    RECENT_ERROR_REASONS as _RECENT_ERROR_REASONS,  # noqa: F401
)


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
       *file* (when *file* is non-empty) > ``ROCQ_WORKSPACE``.
    3. Timeout resolution.  *timeout_default* is the wrapper's
       compile/verify fallback (seconds): when set, the helper
       falls back to it for ``timeout<=0`` and does not clamp; when
       ``None`` the helper routes through :func:`_resolve_call_timeout`
       (the per-call cap that returns a ``clamped`` flag).
    4. ``_validate_workspace`` against the resolved workspace; on
       failure returns a :func:`_fail` envelope with the *already
       resolved* lifespan_state so the failure lands in
       ``recent_errors``.
    5. ``_maybe_workspace_warning`` against the resolved workspace.

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
        workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    else:
        workspace = workspace or ROCQ_WORKSPACE

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

    err = _validate_workspace(workspace)
    if err:
        return _fail(lifespan_state, tool, err, "validation")

    ws_warning = _maybe_workspace_warning(
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
      :func:`_maybe_workspace_warning`, when set.

    Both merges are no-ops if *result* is not a ``dict`` so an
    implementation that returns a non-dict (unexpected) passes through
    untouched.
    """
    if not isinstance(result, dict):
        return result
    if clamped:
        result["clamped_timeout"] = ROCQ_QUERY_TIMEOUT_CAP
    if ws_warning:
        result["workspace_warning"] = ws_warning
    return result


async def _build_memory_abort_response(
    lifespan_state: dict[str, Any],
    tool: str,
    on_timeout: Callable[[], None] | None,
    partial_state: dict[str, Any] | None,
    *,
    auto_record: bool = True,
) -> dict[str, Any]:
    """Run the memory-abort recovery path and return the response dict.

    Thin wrapper around :func:`_handle_pet_failure` that supplies the
    memory-specific error message; the recovery scaffold (invalidate
    pet, release lock, fire on_timeout, merge partial, record error)
    is shared with every other killed-pet path.  When *auto_record* is
    False, the ``recent_errors`` push is suppressed so the caller can
    classify the failure at its own layer.
    """
    return await _handle_pet_failure(
        lifespan_state,
        tool,
        reason="memory_exhausted",
        error=(
            f"{tool} aborted: pet RSS exceeded "
            f"{ROCQ_MAX_PET_RSS_MB} MB. The proof state was lost; "
            "pet has been restarted. Retry with a smaller term, "
            "avoid vm_compute on large inputs, or split the work."
        ),
        killed_pet=True,
        on_timeout=on_timeout,
        auto_record=auto_record,
        partial_state=partial_state,
    )


async def _memory_watchdog(
    lifespan_state: dict[str, Any],
    max_rss_mb: int,
    main_task: asyncio.Task,
    event: asyncio.Event,
    interval: float | None = None,
) -> None:
    """Sample pet RSS; on threshold breach, set *event* and cancel *main_task*.

    Runs concurrently with ``_run_with_pet``'s main thread.  When the pet
    subprocess RSS exceeds ``max_rss_mb`` MB, signals memory exhaustion via
    *event* and cancels the main task so the existing timeout-class recovery
    path can reclaim the lock and respawn pet.

    Tolerates:
    - ``psutil`` not installed -- exits silently (no monitoring).
    - pet not yet spawned (``lifespan_state["pet_client"] is None``) --
      keeps polling.
    - pet exits between samples (``psutil.NoSuchProcess``) -- treated as
      transient; keeps polling.
    """
    if interval is None:
        interval = _MEMORY_WATCHDOG_INTERVAL

    try:
        while not main_task.done():
            await asyncio.sleep(interval)
            if main_task.done():
                return
            client = lifespan_state.get("pet_client")
            if client is None or client.process is None:
                continue
            try:
                pid = client.process.pid
                rss_bytes = psutil.Process(pid).memory_info().rss
            except (psutil.Error, AttributeError, OSError):
                # psutil.Error covers NoSuchProcess / AccessDenied / ZombieProcess;
                # OSError catches raw ProcessLookupError if pet died between
                # Process() construction and memory_info().
                continue
            rss_mb = rss_bytes // (1024 * 1024)
            if rss_mb > lifespan_state.get("peak_pet_rss_mb", 0):
                lifespan_state["peak_pet_rss_mb"] = float(rss_mb)
            if rss_mb > max_rss_mb:
                event.set()
                main_task.cancel()
                return
    except asyncio.CancelledError:
        return


async def _handle_pet_failure(
    lifespan_state: dict[str, Any],
    tool: str,
    *,
    reason: str,
    error: str,
    killed_pet: bool = False,
    on_timeout: Callable[[], None] | None = None,
    partial_state: dict[str, Any] | None = None,
    auto_record: bool = True,
) -> dict[str, Any]:
    """Build a unified failure response for ``_run_with_pet``'s except arms.

    When *killed_pet* is True (timeout / dead PetanqueError / BrokenPipe /
    ConnectionError), invalidates the pet client, force-releases the
    pet lock, optionally invokes the caller's *on_timeout* hook, and
    tags the response with ``pet_restarted: True``.  When False
    (lock contention / live PetanqueError / FileNotFoundError /
    unexpected OSError-class exception), leaves the pet alone.

    Both paths merge *partial_state* (if any) into the response and
    record the failure into ``recent_errors`` so ``rocq_diag`` surfaces
    it.  When *auto_record* is False, the ``_record_error`` call is
    skipped; the recovery side-effects (invalidate / lock release /
    on_timeout) still fire so the pet stays healthy.  Used by callers
    that need to classify the failure at their own layer (e.g.
    ``run_assumptions`` distinguishing ``not_found`` from generic crash).
    """
    if killed_pet:
        _invalidate_pet(lifespan_state)
        await _force_release_pet_lock()
        if on_timeout is not None:
            on_timeout()
    resp: dict[str, Any] = {"success": False, "error": error, "reason": reason}
    if killed_pet:
        resp["pet_restarted"] = True
    if partial_state:
        _merge_partial_state(resp, partial_state)
    if auto_record:
        _record_error(lifespan_state, tool, error, reason=reason)
    return resp


async def _run_with_pet(
    fn: Callable[[Any], Any],
    lifespan_state: dict[str, Any],
    tool: str,
    on_timeout: Callable[[], None] | None = None,
    timeout: float | None = None,
    partial_state: dict[str, Any] | None = None,
    *,
    auto_record: bool = True,
) -> Any:
    """Run *fn(pet)* with the pet client, handling lock/semaphore/timeout/errors.

    The helper encapsulates the full boilerplate shared by every pytanque
    operation that follows the simple "acquire lock, ensure pet, do work"
    pattern:

    1. PetanqueError import check
    2. _pet_lock acquisition with timeout
    3. _ensure_pet (lazy-init the pet subprocess)
    4. asyncio.Semaphore + asyncio.wait_for (async-level timeout)
    5. All standard exception handlers

    *fn* receives the live pet client and must return the desired result.
    It runs inside a background thread with _pet_lock held; the lock is
    released automatically when *fn* returns or raises.

    *tool* is the canonical MCP tool name (e.g. ``"rocq_check"``) and is
    used both as the prefix in user-facing error messages
    (``"rocq_check timed out after 30s."``) and as the ``tool`` field on
    ``recent_errors`` entries.  Pass exactly the public tool name, not a
    human phrase.

    When pet crashes (timeout, broken pipe), the return dict includes
    ``"pet_restarted": True`` so callers can decide whether to retry.

    If *partial_state* is given (a mutable dict), *fn* can populate it
    with intermediate results.  On timeout or error the dict contents
    are merged into the error response so partial work is not lost.

    When *auto_record* is False (default True), failure paths still
    return the same failure-envelope dict but skip the ``_record_error``
    push into ``recent_errors``.  Callers that need to classify the
    failure at their own layer (e.g. ``run_assumptions`` distinguishing
    ``not_found`` from a generic ``rocq_query/crashed``) pass
    ``auto_record=False`` to avoid the double-record / compensating-pop
    dance.

    The return type is left as ``Any`` because the dict shape varies by
    failure mode (success path, ``pet_restarted``-tagged crashes,
    ``partial_state`` merges, etc.) and a TypedDict would be unwieldy.
    The ``"reason"`` key, when present on a failure, is a
    :data:`compile_enrichment._StateCaptureStatus` (one of ``"timeout"``, ``"crashed"``,
    ``"memory_exhausted"``, ``"lock_contended"``, ``"unavailable"``).
    """
    try:
        from pytanque import PetanqueError
    except ImportError:
        return _fail(
            lifespan_state if auto_record else None,
            tool,
            _PYTANQUE_NOT_INSTALLED_HINT,
            "unavailable",
        )

    _timeout: float = timeout if timeout is not None else lifespan_state["pet_timeout"]
    # Lock acquire uses a shorter timeout than wait_for so that
    # _PetLockTimeout fires before asyncio.TimeoutError on contention.
    # This avoids unnecessarily killing pet when the issue is just
    # lock contention, not a pet hang.
    lock_timeout = _timeout * 0.8

    def _execute() -> Any:
        lock = _pet_lock  # capture local ref (survives _force_release_pet_lock)
        wait_started = time.monotonic()
        if not lock.acquire(timeout=lock_timeout):
            raise _PetLockTimeout("Could not acquire pet lock")
        # Contention telemetry for rocq_diag: how long this call parked
        # on the (globally serializing) pet lock.  Dict writes are
        # GIL-atomic; last-writer-wins races are fine for diagnostics.
        wait_ms = (time.monotonic() - wait_started) * 1000.0
        lifespan_state["lock_wait_ms_last"] = wait_ms
        if wait_ms > lifespan_state.get("lock_wait_ms_max", 0.0):
            lifespan_state["lock_wait_ms_max"] = wait_ms
        try:
            pet = _ensure_pet(lifespan_state)
            return fn(pet)
        finally:
            lock.release()

    sem = _get_pet_semaphore()
    async with sem:
        main_task = asyncio.create_task(asyncio.to_thread(_execute))
        mem_event = asyncio.Event()
        monitor_task = asyncio.create_task(
            _memory_watchdog(lifespan_state, ROCQ_MAX_PET_RSS_MB, main_task, mem_event)
        )
        try:
            try:
                result = await asyncio.wait_for(main_task, timeout=_timeout)
                return result
            finally:
                if not monitor_task.done():
                    monitor_task.cancel()
                    try:
                        await monitor_task
                    except asyncio.CancelledError:
                        pass
        except asyncio.CancelledError:
            # If mem_event is set, the watchdog cancelled main_task because
            # pet RSS exceeded the threshold; otherwise this is an external
            # cancel that should propagate.
            if mem_event.is_set():
                return await _build_memory_abort_response(
                    lifespan_state,
                    tool,
                    on_timeout,
                    partial_state,
                    auto_record=auto_record,
                )
            raise
        except asyncio.TimeoutError:
            # If the wait_for timer and the watchdog raced, mem_event may
            # already be set; prefer the more specific memory_exhausted label.
            if mem_event.is_set():
                return await _build_memory_abort_response(
                    lifespan_state,
                    tool,
                    on_timeout,
                    partial_state,
                    auto_record=auto_record,
                )
            return await _handle_pet_failure(
                lifespan_state,
                tool,
                reason="timeout",
                error=(
                    f"{tool} timed out after {_timeout}s. "
                    f"Retry with `{tool}(..., timeout=<seconds>)` "
                    f"(e.g. `timeout=180` for files with heavy library imports). "
                    f"Server-side defaults: ROCQ_PET_TIMEOUT (base, default 30s), "
                    f"ROCQ_QUERY_TIMEOUT_CAP (cap, default 300s). "
                    f"If the response also includes `clamped_timeout`, you have "
                    f"hit `ROCQ_QUERY_TIMEOUT_CAP`; call `rocq_diag` for memory "
                    f"headroom and consider `rocq_start(..., force_restart=True)` "
                    f"instead of bumping further."
                ),
                killed_pet=True,
                on_timeout=on_timeout,
                partial_state=partial_state,
                auto_record=auto_record,
            )
        except _PetLockTimeout:
            lifespan_state["lock_contended_total"] = (
                int(lifespan_state.get("lock_contended_total", 0)) + 1
            )
            return await _handle_pet_failure(
                lifespan_state,
                tool,
                reason="lock_contended",
                error=f"{tool}: pet is busy (lock contention). Try again.",
                auto_record=auto_record,
            )
        except PetanqueError as e:
            if not _pet_alive(lifespan_state.get("pet_client")):
                return await _handle_pet_failure(
                    lifespan_state,
                    tool,
                    reason="crashed",
                    error=f"Pet process died: {e.message}",
                    killed_pet=True,
                    partial_state=partial_state,
                    auto_record=auto_record,
                )
            return await _handle_pet_failure(
                lifespan_state,
                tool,
                reason="crashed",
                error=e.message,
                auto_record=auto_record,
            )
        except (BrokenPipeError, ConnectionError) as e:
            return await _handle_pet_failure(
                lifespan_state,
                tool,
                reason="crashed",
                error=f"Pet process died: {e}",
                killed_pet=True,
                on_timeout=on_timeout,
                partial_state=partial_state,
                auto_record=auto_record,
            )
        except FileNotFoundError:
            return await _handle_pet_failure(
                lifespan_state,
                tool,
                reason="unavailable",
                error="pet binary not found on PATH. Install coq-lsp.",
                auto_record=auto_record,
            )
        except (OSError, RuntimeError, ValueError, TypeError) as e:
            return await _handle_pet_failure(
                lifespan_state,
                tool,
                reason="crashed",
                error=f"Unexpected error: {e}",
                partial_state=partial_state,
                auto_record=auto_record,
            )


# ---------------------------------------------------------------------------
# Import implementation functions from submodules
# ---------------------------------------------------------------------------
# These imports MUST come at the bottom of this module: ``compile`` /
# ``interactive`` / ``diag`` / ``compile_enrichment`` all import server
# at module load time (for shared infrastructure: locks, _record_error,
# config), so server cannot in turn import them at the top without a
# cycle.  Only re-export symbols that are actually accessed via
# ``rocq_mcp.server`` from tests or from sibling modules — every dead
# re-export is a test-monkeypatch trap waiting to happen.

from rocq_mcp.compile import (  # noqa: E402
    run_compile,
    run_compile_file,
    run_verify,
)
from rocq_mcp.interactive import (  # noqa: E402
    run_assumptions,
    run_query,
    run_start,
    run_check,
    run_step_multi,
    run_toc,
    run_notations,
)
from rocq_mcp.diag import (  # noqa: E402
    _DIAG_LIVE_STATES_CAP,
    _build_diag_snapshot,
    _sample_pet_rss_mb,
)
from rocq_mcp.health import (  # noqa: E402
    build_health_snapshot,
    compute_switch_env,
    list_switches,
    _detect_switch,
    _resolve_binary,
    _SWITCH_ENV_KEYS,
)
from rocq_mcp.compile_enrichment import (  # noqa: E402
    run_compile_file_with_state,
    run_compile_with_state,
)

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
        timeout_default=ROCQ_COQC_TIMEOUT,
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
    annotations=ToolAnnotations(
        title="Compile a .v file (coqc)",
        readOnlyHint=False,
        destructiveHint=False,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_compile_file(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    keep_vo: bool = False,
    mode: str = "full",
    timing: bool = False,
    ctx: Context = None,
) -> dict[str, Any]:
    """Compile a .v file on disk via coqc — whole-file check and final verification.

    Prefer this over ``rocq_compile`` for files on disk (the source is not
    resent over the transport); prefer ``rocq_start`` + ``rocq_check`` for
    scratch iteration.  Compilation artifacts are cleaned up by default;
    the source file is preserved.

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
        timeout_default=ROCQ_COQC_TIMEOUT,
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
    ``timeout``, ``validation``.  On success ``verification_method``
    reports the phase used (``module_m``, ``shared_defs``, ``direct`` —
    the last has weaker guarantees; see the README security model).

    Args:
        proof: Complete proof file content, including imports.
        problem_name: Unqualified theorem name (e.g. "add_comm").
        problem_statement: The original problem file content (with
            Admitted/Abort).
        workspace: Workspace directory; default ROCQ_WORKSPACE.
        timeout: Seconds; 0 = ROCQ_VERIFY_TIMEOUT default (budget spans
            all verification phases).
        include_warnings: False drops warning-severity output.
    """
    resolved = _resolve_tool_envelope(
        tool="rocq_verify",
        ctx=ctx,
        workspace=workspace,
        timeout=timeout,
        timeout_default=ROCQ_VERIFY_TIMEOUT,
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
    # run_verify -> _run_with_pet (Phase 2 toc lookup) are already
    # recorded inside that helper, so skip when ``pet_restarted=True``
    # to avoid the double-record bug — the prior entry already carries
    # tool="rocq_verify" with the right reason because _extract_problem_structure
    # passes that tool name to _run_with_pet.
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
    """Run a Rocq query (Search / Check / Print / About / Locate) and return its output.

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
    here indistinguishably) plus ``raw_output``.

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
        include_raw: True additionally returns raw_output (the verbatim
            Print Assumptions text; redundant with the parsed list).
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
    file.  Output capped at 500 names (overflow is flagged in the
    response).

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
    annotations=ToolAnnotations(
        title="Try tactics without committing",
        readOnlyHint=True,
        idempotentHint=True,
        openWorldHint=False,
    )
)
async def rocq_step_multi(
    tactics: list[str],
    from_state: int,
    include_warnings: bool = True,
    timeout: int = 0,
    goals_format: Literal["pretty", "structured", "names_only"] = "pretty",
    ctx: Context = None,
) -> dict[str, Any]:
    """Try up to 20 tactics against one state; report each outcome without committing.

    Read-only exploration — the state table is untouched; commit the
    winner with ``rocq_check(from_state=<same state>, body=<tactic>)``.
    Each result entry carries ``success``, ``goals``, ``proof_finished``,
    ``focus_depth`` (and ``feedback`` when a tactic prints).  Advance a
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
            instead of goals; the response carries distinct_outcomes.
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
    )
    if clamped:
        result["clamped_timeout"] = ROCQ_QUERY_TIMEOUT_CAP
    return result


# ---------------------------------------------------------------------------
# Tool: rocq_check
# ---------------------------------------------------------------------------


@mcp.tool(
    annotations=ToolAnnotations(
        # Additive, never destructive: allocates a fresh state_id and
        # leaves existing states untouched.  Not idempotent (each call
        # creates a new state).
        title="Run proof commands from a state",
        readOnlyHint=False,
        destructiveHint=False,
        idempotentHint=False,
        openWorldHint=False,
    )
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
        result["clamped_timeout"] = ROCQ_QUERY_TIMEOUT_CAP
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

    previous = _detect_switch(_resolve_binary(ROCQ_COQC_BINARY))["switch"]

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

    # Apply the new environment + kill pet under _pet_lock so the mutation
    # cannot interleave with a concurrent _ensure_pet spawn (which holds the
    # same lock and would otherwise adopt a pet started on the OLD env, then
    # survive our _invalidate_pet on a live process — no broken pipe, no
    # respawn).  Serializing here guarantees the next spawn sees the new env.
    # The semaphore matches every other pet-mutating path's `async with sem`.
    lock_timeout = (lifespan_state.get("pet_timeout") or ROCQ_PET_TIMEOUT) * 0.8

    def _apply_switch() -> bool:
        lock = _pet_lock  # local ref survives a _force_release_pet_lock swap
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
            # (via _pet_invalidation_hooks).  The next pet-routed call lazily
            # respawns pet under the new environment.
            _invalidate_pet(lifespan_state)
            return True
        finally:
            lock.release()

    async with _get_pet_semaphore():
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
4. Explore with `rocq_step_multi(from_state=s, tactics=[...])`.  Start
   with the automation battery: ["trivial.", "reflexivity.",
   "assumption.", "auto.", "eauto.", "tauto.", "intuition.", "lia.",
   "lra.", "ring.", "firstorder."] (lia/lra/ring need the matching
   imports), then structural steps ("intros.", "induction x.",
   "destruct x.", "simpl.") as the goals demand.
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
