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
import signal
import subprocess
import threading
import time
import warnings
from pathlib import Path
from typing import Any, Callable

import psutil
from fastmcp import FastMCP, Context
from fastmcp.server.lifespan import lifespan

# ---------------------------------------------------------------------------
# Configuration (env vars with defaults)
# ---------------------------------------------------------------------------

ROCQ_WORKSPACE: str = os.environ.get("ROCQ_WORKSPACE", os.getcwd())
_ROCQ_WORKSPACE_EXPLICIT: bool = "ROCQ_WORKSPACE" in os.environ
ROCQ_COQC_TIMEOUT: int = int(os.environ.get("ROCQ_COQC_TIMEOUT", "60"))
ROCQ_VERIFY_TIMEOUT: int = int(os.environ.get("ROCQ_VERIFY_TIMEOUT", "120"))
ROCQ_PET_TIMEOUT: float = float(os.environ.get("ROCQ_PET_TIMEOUT", "30"))
ROCQ_QUERY_TIMEOUT_CAP: int = int(os.environ.get("ROCQ_QUERY_TIMEOUT_CAP", "300"))
ROCQ_COQC_BINARY: str = os.environ.get("ROCQ_COQC_BINARY", "coqc")
ROCQ_MAX_SOURCE_SIZE: int = int(os.environ.get("ROCQ_MAX_SOURCE_SIZE", "1000000"))


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


def _default_max_pet_rss_mb() -> int:
    """Default pet RSS cap: 50% of system RAM, hard-capped at 16 GB.

    Tuned to fire well above legitimate ``vm_compute`` ceilings (~2-4 GB)
    but well below the OOM-killer / swap-thrash zone.  On a 32 GB Mac
    this resolves to 16 GB; on a 16 GB host, 8 GB; on a 64 GB+ host the
    16 GB cap kicks in.
    """
    total_mb = psutil.virtual_memory().total // (1024 * 1024)
    return min(int(0.50 * total_mb), 16_384)


ROCQ_MAX_PET_RSS_MB: int = int(
    os.environ.get("ROCQ_MAX_PET_RSS_MB", str(_default_max_pet_rss_mb()))
)
_MEMORY_WATCHDOG_INTERVAL: float = 0.5
_RECENT_ERRORS_MAX: int = 20

# Multi-error walker tunables for ``rocq_compile_file``.  When CAP is 0
# the feature is disabled and no ``errors`` field is added to the
# response.  TIMEOUT is the per-``pet.run`` budget inside the walker.
_COMPILE_MULTI_ERROR_CAP: int = int(
    os.environ.get("ROCQ_COMPILE_MULTI_ERROR_CAP", "20")
)
_COMPILE_MULTI_ERROR_TIMEOUT: float = float(
    os.environ.get("ROCQ_COMPILE_MULTI_ERROR_TIMEOUT", "5.0")
)

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


mcp = FastMCP("rocq-mcp", lifespan=app_lifespan)

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
    # Prefer .mcp-workspace/ subdirectory if it contains a project file.
    # This allows projects to maintain a separate _CoqProject for MCP/coq-lsp
    # without modifying the main build's _CoqProject.
    mcp_ws = ws / ".mcp-workspace"
    for name in ("_RocqProject", "_CoqProject"):
        p = mcp_ws / name
        if p.is_file():
            ws = mcp_ws  # redirect to the MCP workspace
            break

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
        raise ImportError(
            "pytanque is not installed. Install with: pip install 'rocq-mcp[interactive]'"
        )

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


_RECENT_ERROR_MESSAGE_LIMIT: int = 500

# Failure reasons emitted by ``_run_with_pet``'s except arms — the
# intersection of :data:`rocq_mcp.interactive._TRANSPORT_FAILURE_REASONS`
# and the failure subset of
# :data:`rocq_mcp.compile_enrichment._StateCaptureStatus`.  Single source
# of truth so the three reason-sets cannot drift apart silently.
_PET_SIDE_FAILURE_REASONS: frozenset[str] = frozenset(
    {
        "timeout",
        "crashed",
        "memory_exhausted",
        "lock_contended",
        "unavailable",
    }
)

# Allowed values for the ``reason`` field on ``recent_errors`` entries.
# A superset of :data:`compile_enrichment._StateCaptureStatus`'s failure modes plus
# ``"validation"`` for early-return validation failures, ``"not_found"``
# for name-resolution failures (rocq_start / rocq_assumptions typos),
# and the rocq_verify-specific reasons.
_RECENT_ERROR_REASONS: frozenset[str] = _PET_SIDE_FAILURE_REASONS | frozenset(
    {
        "validation",
        "not_found",
        # rocq_check mid-batch failure (a tactic was rejected by Coq).
        "tactic_failed",
        # rocq_verify-specific reasons (see compile.run_verify).
        "compile_error",
        "axiom_dependency",
        "type_mismatch",
    }
)

assert _PET_SIDE_FAILURE_REASONS <= _RECENT_ERROR_REASONS


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

    *reason* is one of :data:`_RECENT_ERROR_REASONS` — typically a
    :data:`compile_enrichment._StateCaptureStatus` value for pet-level failures, or
    ``"validation"`` for early-return validation failures.

    Long *message* strings are truncated to
    ``_RECENT_ERROR_MESSAGE_LIMIT`` chars + ``"..."`` to keep the
    ``rocq_diag`` payload bounded; the full message is preserved in the
    immediate response of the failing tool call.

    Tolerates ``lifespan_state is None`` (no recording) and missing
    ``recent_errors`` key (no recording) — both happen when the failing
    tool call has no MCP context.

    Asserts that *reason* is in :data:`_RECENT_ERROR_REASONS`.  Without
    this guard a typo'd reason would silently appear in ``rocq_diag``
    output and break agent dispatch logic — mirrors
    :data:`compile_enrichment._VALID_STATE_CAPTURE_STATUSES` which is used the same way
    in ``compile_enrichment``.
    """
    assert (
        reason in _RECENT_ERROR_REASONS
    ), f"unknown error reason {reason!r}; add it to _RECENT_ERROR_REASONS"
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
        msg = (
            "pytanque is not installed. "
            "Install with: pip install 'rocq-mcp[interactive]'"
        )
        return _fail(
            lifespan_state if auto_record else None,
            tool,
            msg,
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
        if not lock.acquire(timeout=lock_timeout):
            raise _PetLockTimeout("Could not acquire pet lock")
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
from rocq_mcp.compile_enrichment import (  # noqa: E402
    run_compile_file_with_state,
    run_compile_with_state,
)

# ---------------------------------------------------------------------------
# Tool: rocq_compile
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_compile(
    source: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    ctx: Context = None,
) -> dict[str, Any]:
    """Compile a finished .v file via coqc.

    For *scratch iteration* on a single proof, prefer the interactive tools:

    - ``rocq_start`` opens a held session (imports stay warm across
      attempts).
    - ``rocq_check`` runs a candidate proof body against a held state.
    - ``rocq_step_multi`` tries several tactics at once against a held
      state and reports which succeeded.

    Use ``rocq_compile`` for finished proofs, axiom audits, and final
    verification — coqc reloads all imports per call (often several
    seconds on heavy library imports).

    On failure, the result includes ``error_positions`` and a ``hint``.
    When coq-lsp is available in the active MCP session, the result
    also includes ``state_capture_status``:

      - ``"ok"``: proof state was captured at the error position; the
        result also includes ``state_id``, ``goals``, ``file``,
        ``theorem``, and ``proof_finished``.  Recover via
        ``rocq_check(from_state=state_id)`` or
        ``rocq_step_multi(from_state=state_id)``.
      - ``"outside_proof"``: error is outside any open proof; no
        ``state_id`` is returned.  Follow the original ``hint``.
      - ``"timeout"`` / ``"crashed"`` / ``"lock_contended"`` /
        ``"unavailable"`` / ``"memory_exhausted"`` /
        ``"no_position"``: enrichment did not
        succeed; follow the original ``hint`` (typically
        ``rocq_start(file=..., line=..., character=...)``).

    Args:
        source: Complete Rocq (.v) file content to compile.
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Compilation timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
        include_warnings: If True (default), include deduplicated warnings
            before the error in the output.  Set to False to get only the
            error diagnostic, which keeps context compact.

    On ``pet_restarted: True`` (state-capture path crashed pet), call
    ``rocq_diag`` for memory headroom and recent error history.
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


@mcp.tool
async def rocq_compile_file(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    keep_vo: bool = False,
    ctx: Context = None,
) -> dict[str, Any]:
    """Compile a finished .v file on disk via coqc.

    For *scratch iteration* on a single proof, prefer the interactive tools:

    - ``rocq_start`` opens a held session (imports stay warm across
      attempts).
    - ``rocq_check`` runs a candidate proof body against a held state.
    - ``rocq_step_multi`` tries several tactics at once against a held
      state and reports which succeeded.

    Use ``rocq_compile_file`` for whole-file verification, axiom audits,
    and final compile — coqc reloads all imports per call (often several
    seconds on heavy library imports).  Preferred over ``rocq_compile``
    for large files because the source stays on disk (avoids transmitting
    the full text through the MCP transport).

    On failure, the result includes ``error_positions`` and a ``hint``.
    When coq-lsp is available in the active MCP session, the result
    also includes ``state_capture_status``:

      - ``"ok"``: proof state was captured at the error position; the
        result also includes ``state_id``, ``goals``, ``file``,
        ``theorem``, and ``proof_finished``.  Recover via
        ``rocq_check(from_state=state_id)`` or
        ``rocq_step_multi(from_state=state_id)``.
      - ``"outside_proof"``: error is outside any open proof; no
        ``state_id`` is returned.  Follow the original ``hint``.
      - ``"timeout"`` / ``"crashed"`` / ``"lock_contended"`` /
        ``"unavailable"`` / ``"memory_exhausted"`` /
        ``"no_position"``: enrichment did not
        succeed; follow the original ``hint`` (typically
        ``rocq_start(file=..., line=..., character=...)``).

    On a ``compile_error`` failure with coq-lsp available, the result
    may also include ``errors``: a list of per-proof errors discovered
    by walking the file through pet (one entry per failing chunk).
    Each entry is ``{proof_name, kind, start_line, end_line, code,
    message}``.  Complements ``error_positions`` — the latter is
    coqc's raw parse of the first diagnostic, while ``errors`` is
    pet's structured walk of the whole file.  The field may be
    *present and empty* (``errors: []``) when the walker ran but pet
    did not reproduce the coqc-reported failure — treat this as "no
    additional errors found" rather than "no errors at all."  Absent
    on success, when coq-lsp is unavailable, when the walker could
    not run, and when ``ROCQ_COMPILE_MULTI_ERROR_CAP=0`` (feature
    disabled).  Tune via ``ROCQ_COMPILE_MULTI_ERROR_CAP`` (default 20,
    max entries) and ``ROCQ_COMPILE_MULTI_ERROR_TIMEOUT`` (default
    5.0s, per-``pet.run`` budget inside the walker).

    Compilation artifacts (``.vo``/``.vok``/``.vos``/``.glob``/``.aux``)
    are cleaned up by default; the source file is preserved.  Set
    ``keep_vo=True`` to retain the compiled-artifact family
    (``.vo``/``.vok``/``.vos``) while still cleaning the diagnostic
    artifacts (``.glob``/``.aux``/``.vio``/``.timing``/``.coqaux``).
    Typical use: compiling a file whose ``.vo`` will be imported by a
    sibling ``.v`` in the same workspace, or incremental compile loops
    that want to avoid rebuilding unchanged dependencies.

    When the call rewrites ``.vo`` files in a workspace that has active
    interactive sessions, the result also includes ``vo_rebuild_warning``:
    a soft advisory naming the workspace and the count of potentially
    affected sessions, with a hint to call ``rocq_start`` again to refresh
    held dependency state.  Quiet when no ``.vo`` changed, when no
    interactive session in this workspace exists, or when the workspace
    exceeds ``_VO_SCAN_FILE_CAP`` (.vo paths).  Setting ``keep_vo=True``
    makes this warning *more likely to fire* on subsequent
    ``rocq_compile_file`` calls in the same workspace: the produced
    ``.vo`` now persists between calls, so any later compile that
    rewrites it is observable as a fresh mtime delta.

    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Workspace directory.  If omitted, auto-detected by walking
            up from *file* looking for ``_RocqProject`` / ``_CoqProject`` /
            ``dune-project``; falls back to the ``ROCQ_WORKSPACE`` env var
            (default: cwd).
        timeout: Compilation timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
        include_warnings: If True (default), include deduplicated warnings
            before the error in the output.  Set to False to get only the
            error diagnostic, which keeps context compact.
        keep_vo: If True, preserve the ``.vo``/``.vok``/``.vos`` outputs
            after coqc returns (diagnostic artifacts are still cleaned).
            Default False matches today's "clean everything but the
            source" behavior.  Useful when a sibling file in the same
            workspace will ``Require Import`` the result.

    On ``pet_restarted: True`` (state-capture path crashed pet), call
    ``rocq_diag`` for memory headroom and recent error history.
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

    result = await run_compile_file_with_state(
        file=file,
        workspace=workspace,
        timeout=effective_timeout,
        include_warnings=include_warnings,
        lifespan_state=lifespan_state,
        keep_vo=keep_vo,
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_verify
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_verify(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    ctx: Context = None,
) -> dict[str, Any]:
    """Verify that a proof actually proves the original statement.

    Wraps the proof in a Module M sandbox and checks that the theorem
    matches the original problem_statement. Catches type redefinition,
    Admitted/Abort, custom axioms, and statement mismatches. Standard
    mathematical axioms (classical logic, Reals, etc.) are accepted.

    Run this after rocq_compile succeeds to confirm correctness.

    Args:
        proof: The complete proof file content (including imports).
        problem_name: The unqualified theorem name (e.g., "add_comm", not "Nat.add_comm").
        problem_statement: The original problem file content (with Admitted/Abort).
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Verification timeout in seconds (default: ROCQ_VERIFY_TIMEOUT env var).
        include_warnings: If True (default), include deduplicated warnings
            before the error in the output.  Set to False for compact errors.

    Returns the unified envelope ``{success, error, reason, ...}``.
    On failure, ``reason`` is one of:
        - ``"validation"``: invalid identifier, oversize source, malformed input.
        - ``"compile_error"``: the proof failed to compile.
        - ``"axiom_dependency"``: the proof relies on Admitted, ``admit``, or
          a custom (non-standard) axiom.
        - ``"type_mismatch"``: Phase 3 found that the proof's type differs
          from the problem's type.
        - ``"timeout"``: verification exceeded the budget across all phases.

    On success, ``assumptions`` and ``verification_method`` describe how
    the verdict was reached (``module_m``, ``shared_defs``, ``direct``).

    On ``pet_restarted: True`` (Phase 2 ``rocq_query`` path crashed pet
    while extracting shared definitions), call ``rocq_diag`` for memory
    headroom and recent error history.
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


@mcp.tool
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
    """Search the Rocq environment — find lemmas, check types, inspect definitions.

    Does NOT modify any proof state. Use this to explore before proving:
      command="Search (nat -> nat -> nat)."  — find relevant lemmas
      command="Check Nat.add."               — check a term's type
      command="Print Nat.add."               — see a definition
      command="About plus."                  — summary of a name

    Three context modes (mutually exclusive in practice):
    - **preamble mode** (default): pass import / scope commands as a
      string.  Scope and import statements like ``Require Import``,
      ``From X Require Y``, ``Open Scope``, ``Set``, ``Unset``,
      ``Local``, and ``Section`` belong here — NOT inside ``command=``.
      ``command=`` runs each statement in isolation, so e.g. an
      ``Open Scope`` placed in ``command`` would not propagate to a
      following ``Search``.  See README "Recommended usage patterns →
      Imports and scopes in rocq_query".
    - **file mode**: pass a ``.v`` file path; the query runs with all
      definitions from that file in scope.  More reliable than preamble
      because it captures ``Open Scope``, ``Set`` options, etc., in the
      exact order the file declares them.
    - **from_state mode**: pass a ``state_id`` from a live ``rocq_check``
      session to query against the live proof context — opened scopes,
      hypotheses, and local definitions are all visible to ``Search`` /
      ``Print`` / ``About`` / ``Locate``.  The query runs against a
      transient child state which is discarded; the parent state is
      unchanged.  Canonical pattern::

          state_id = (await rocq_check(body=..., from_state=...))["state_id"]
          await rocq_query(command="Search _.", from_state=state_id)

      Prefer this over ``rocq_check(from_state=N, body="Search ...")``
      for pure queries — no new ``state_id`` is allocated and the
      state-table is not polluted.

    Args:
        command: The Rocq query command to execute.
        preamble: Optional import lines needed for the query context
                  (e.g., "Require Import Reals.\\nOpen Scope R_scope.").
        file: Path to a .v file (relative to workspace) whose definitions
            should be in scope. Mutually exclusive with preamble and
            from_state.
        workspace: Workspace directory.  If omitted, auto-detected by walking
            up from *file* looking for ``_RocqProject`` / ``_CoqProject`` /
            ``dune-project``; falls back to the ``ROCQ_WORKSPACE`` env var
            (default: cwd).
        max_results: Optional maximum number of results to return.
            Useful for broad Search patterns. If omitted, all results are
            returned (subject to character limit).
        include_warnings: If True (default), include all feedback returned
            by the query.  If False, drop entries at LSP Warning severity
            so warning noise does not crowd out tool output.
        timeout: Per-call timeout in seconds for expensive computations
            like ``Time Eval vm_compute in ...``.  ``0`` (default) means
            use ``ROCQ_PET_TIMEOUT``.  Clamped to ``ROCQ_QUERY_TIMEOUT_CAP``
            (default 300s); when clamping fires the response includes
            ``clamped_timeout: <cap>`` so the caller can diagnose unexpected
            timeouts.
        from_state: A live state_id (from ``rocq_start`` / ``rocq_check`` /
            ``rocq_step_multi``) to query against.  Mutually exclusive with
            *file*.  When set, *preamble* is ignored.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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


@mcp.tool
async def rocq_assumptions(
    name: str,
    file: str,
    workspace: str = "",
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """List the axioms a theorem depends on.

    Runs ``Print Assumptions`` on the given theorem/lemma name and returns
    the resulting assumption list verbatim.  No classification is performed
    — this tool is pure introspection; the agent decides what's safe to
    trust.  Use ``rocq_verify`` for an admit-free / sandboxed trust
    decision on a candidate proof.

    The theorem must be defined in the given file.  The tool reads the file
    to set up the full Rocq environment (imports, scopes, definitions),
    ensuring the correct theorem is resolved even when names are reused
    across sections.

    Args:
        name: The theorem/lemma name to check (e.g., "add_comm").
        file: Path to the .v file where the theorem is defined (relative to workspace).
        workspace: Workspace directory.  If omitted, auto-detected by walking
            up from *file* looking for ``_RocqProject`` / ``_CoqProject`` /
            ``dune-project``; falls back to the ``ROCQ_WORKSPACE`` env var
            (default: cwd).
        timeout: Per-call timeout in seconds for the ``Print Assumptions``
            query.  Default 0 uses ``ROCQ_PET_TIMEOUT`` (env var, default
            30).  Raise this when the theorem's opaque-proof fetch from
            ``.vo`` files is slow.  Clamped to ``ROCQ_QUERY_TIMEOUT_CAP``
            (default 300s) so a stray large value cannot park the pet
            lock indefinitely; when clamping fires the response includes
            ``clamped_timeout: <cap>`` so the caller can diagnose
            unexpected timeouts.

            **Tip:** ``Print Assumptions`` triggers ``.vo`` opaque-proof
            fetching on first call (often 40+ modules on heavy library
            imports).  A pet restart from a timeout wipes Fleche, so a
            retry with the *same* timeout pays the same opaque-fetch
            cost from scratch and will time out again — the cost
            survives ``pet_restarted: True``.  Set ``timeout=`` high on
            the *first* call rather than relying on a retry after
            restart.

    Returns (key fields):
        success:     bool.
        theorem:     the cleaned theorem name.
        assumptions: list[str] of ``"name : type"`` pairs from
                     ``Print Assumptions``.  Empty when the theorem is closed
                     under the global context.  ``Print Assumptions`` does
                     not distinguish ``Admitted`` from ``Axiom`` / ``Parameter``
                     / ``Conjecture``, so admits and user axioms appear here
                     side-by-side.
        raw_output:  full raw ``Print Assumptions`` output.

    On theorem-not-found errors: response includes ``available_in_file:
    list[str]`` with the file's defined names (sorted, capped — see
    ``available_in_file_limit`` in the response when truncated).  When the
    file has more names than the cap, ``available_in_file_truncated:
    true``, ``available_in_file_total: <int>`` (uncapped count), and
    ``available_in_file_limit: <int>`` (the active cap) are also
    included; call ``rocq_toc`` for the full list.  Agents can fuzzy-
    match the requested name against this list to recover from typos.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_toc
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_toc(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Get the structure of a Rocq file: all definitions, lemmas, theorems, and sections.

    Returns a hierarchical outline showing what is defined in the file.
    Useful for understanding a file before working with it, or finding
    the name of a theorem to prove.

    Does NOT require a rocq_start session.

    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Workspace directory.  If omitted, auto-detected by walking
            up from *file* looking for ``_RocqProject`` / ``_CoqProject`` /
            ``dune-project``; falls back to the ``ROCQ_WORKSPACE`` env var
            (default: cwd).
        timeout: Per-call timeout in seconds for the ``pet.toc`` lookup.
            Default 0 uses ``ROCQ_PET_TIMEOUT`` (env var, default 30).
            Raise this for very large files with heavy library imports.
            Clamped to ``ROCQ_QUERY_TIMEOUT_CAP`` (default 300s) so a
            stray large value cannot park the pet lock indefinitely;
            when clamping fires the response includes ``clamped_timeout:
            <cap>`` so the caller can diagnose unexpected timeouts.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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


@mcp.tool
async def rocq_notations(
    statement: str,
    preamble: str = "",
    workspace: str = "",
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """List all notations in a Rocq statement and how they resolve.

    Helps debug notation ambiguity (e.g., which scope does "+" resolve to?
    Is "=" Leibniz equality or Qeq?).

    Pass the statement part of a Lemma/Theorem declaration (after the colon).
    For example, for "Lemma foo : forall n, n + 0 = n", pass
    statement="forall n, n + 0 = n".

    NOTE: Only works on statements (propositions/types), not arbitrary terms.

    Args:
        statement: The proposition/type to analyze.
        preamble: Import lines for context (e.g., "Require Import QArith.").
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
        timeout: Per-call timeout in seconds for the notation lookup.
            Default 0 uses ``ROCQ_PET_TIMEOUT`` (env var, default 30).
            Raise this for statements that require heavy library imports.
            Clamped to ``ROCQ_QUERY_TIMEOUT_CAP`` (default 300s) so a
            stray large value cannot park the pet lock indefinitely;
            when clamping fires the response includes ``clamped_timeout:
            <cap>`` so the caller can diagnose unexpected timeouts.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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


@mcp.tool
async def rocq_start(
    file: str = "",
    theorem: str = "",
    workspace: str = "",
    line: int | None = None,
    character: int | None = None,
    preamble: str = "",
    force_restart: bool = False,
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Start an interactive proof session — see goals, explore tactics.

    Returns a state_id for use with rocq_check and rocq_step_multi.
    Also returns the current proof goals at the starting position,
    so this tool can be used to inspect goals at any point in a file.

    Three start modes (precedence: theorem > position > preamble):
    1. By theorem: file + theorem — start proving a specific theorem.
       Tip: for a scratch file under ``/tmp`` that needs the project's
       load path, keep the file name stable across iterations (e.g.
       ``/tmp/probe.v``) — Fleche caches per file path, so rotating
       probe names defeats the warmth.
    2. By position: file + line + character — jump to any position in
       a file and see the proof goals there.  Useful for inspecting
       proof state at a specific point, or recovering from an error
       position returned by rocq_compile.
    3. From imports: preamble — set up an import context only.
       **Preferred for scratch iteration** (no project files needed,
       preferred over ``coqc /tmp/foo.v``): call
       ``rocq_start(preamble='Require Import ...')`` once, then iterate
       with rocq_check / rocq_step_multi against the returned state_id.
       The import set is content-hashed and warm across iterations even
       if you change the lemma body (see
       ``interactive.py:_get_or_create_import_state``).

    **Important:** The interactive session reads the file at start time and
    does not track subsequent edits. If another process or agent modifies the
    file while a session is active, the proof state becomes stale and tactics
    may fail or produce wrong results. To avoid this, work on a **copy** of
    the file for interactive proving, or restart the session after edits.

    Args:
        file: Path to the .v file (relative to workspace).
        theorem: Name of the theorem to prove.
        workspace: Workspace directory.  If omitted, auto-detected by walking
            up from *file* looking for ``_RocqProject`` / ``_CoqProject`` /
            ``dune-project``; falls back to the ``ROCQ_WORKSPACE`` env var
            (default: cwd).
        line: 0-based line number for position-based start.
        character: 0-based character offset for position-based start.
        preamble: Import commands for preamble mode (e.g., "Require Import Lia.").
        force_restart: If True, kill pet, clear the state table, and
            respawn before starting.  Recovery primitive for the rare
            cases where the shared pet is in a bad state: accumulated
            RAM bloat after long shared use, indexing corruption, or a
            "State N expired" that repeats after a plain ``rocq_start``
            retry (suggesting a peer caller is also force-restarting).
            Actively-used states survive peer churn via LRU eviction —
            ``force_restart=True`` is *not* needed as routine insurance
            and is unhelpful when a recent response already carried
            ``pet_restarted: True`` (pet is already fresh).  See README
            "Concurrency model".  Default: False.
        timeout: Per-call timeout in seconds for opening the session.
            Default 0 uses ``ROCQ_PET_TIMEOUT`` (env var, default 30).
            Raise this for files with heavy library imports.
            Clamped to ``ROCQ_QUERY_TIMEOUT_CAP`` (default 300s) so a stray
            large value cannot park the pet lock indefinitely; when
            clamping fires the response includes ``clamped_timeout:
            <cap>`` so the caller can diagnose unexpected timeouts.

    On theorem-not-found errors: response includes ``available_in_file:
    list[str]`` with the file's defined names (sorted, capped — see
    ``available_in_file_limit`` in the response when truncated).  When the
    file has more names than the cap, ``available_in_file_truncated:
    true``, ``available_in_file_total: <int>`` (uncapped count), and
    ``available_in_file_limit: <int>`` (the active cap) are also
    included; call ``rocq_toc`` for the full list.  Agents can fuzzy-
    match the requested name against this list to recover from typos.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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
    )
    return _finalize_tool_envelope(result, clamped=clamped, ws_warning=ws_warning)


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_step_multi(
    tactics: list[str],
    from_state: int,
    include_warnings: bool = True,
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Try multiple tactics at once — find what works without guessing.

    Tests each tactic against a specific proof state and returns all
    results. Does NOT advance the state — commit the winner with
    rocq_check.

    Use this whenever you're unsure which tactic to apply:
      tactics=["auto.", "lia.", "lra.", "ring.", "tauto.", "firstorder."]

    Or to auto-solve a subgoal, try the standard automation battery:
      tactics=["trivial.", "reflexivity.", "assumption.", "exact I.",
               "auto.", "eauto.", "tauto.", "intuition.", "lia.", "lra.",
               "nia.", "nra.", "ring.", "field.", "decide equality.",
               "firstorder."]
    Note: lia/lra/ring/field require the .v file to import Lia/Lra/Ring/Field.

    Or to explore proof structure:
      tactics=["destruct n.", "induction n.", "case_eq n."]

    Each result entry includes a ``feedback`` field (truncated string)
    when the tactic produces visible output (e.g., ``Print``, ``Search``).

    **Canonical exploration pattern:** if the first few steps of a proof
    are a confident prefix, advance with ``rocq_check`` first and pass
    the resulting ``state_id`` as ``from_state`` here — don't repeat the
    prefix inside every entry of ``tactics``.  See README
    "Recommended usage patterns → Multi-tactic exploration".

    Args:
        tactics: List of tactics to try (max 20).
        from_state: State ID to try the tactics from.  Required — use the
            ``state_id`` returned by ``rocq_start`` or a previous
            ``rocq_check``.  There is no implicit "current state"
            fallback (avoids cross-agent state confusion when peers
            share this rocq-mcp process).
        include_warnings: If True (default), per-tactic ``feedback`` includes
            all severities.  If False, drop entries at LSP Warning severity.
        timeout: Per-call timeout in seconds for the whole batch.  The
            per-tactic budget is ``timeout / len(tactics)`` (subject to the
            usual ``Timeout`` eligibility rules).  Default 0 uses
            ``ROCQ_PET_TIMEOUT`` (env var, default 30).  Raise this when
            individual tactics in the batch are expensive.  Clamped to
            ``ROCQ_QUERY_TIMEOUT_CAP``
            (default 300s) so a stray large value cannot park the pet
            lock indefinitely; when clamping fires the response includes
            ``clamped_timeout: <cap>`` so the caller can diagnose
            unexpected timeouts.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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
    )
    if clamped:
        result["clamped_timeout"] = ROCQ_QUERY_TIMEOUT_CAP
    return result


# ---------------------------------------------------------------------------
# Tool: rocq_check
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_check(
    body: str,
    from_state: int,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    ctx: Context = None,
) -> dict[str, Any]:
    """Run proof commands from cached imports — fast iterative checking.

    Much faster than rocq_compile for iterative proof development:
    imports are cached (first call processes them, subsequent calls skip), and on error
    returns the last valid state for immediate interactive recovery
    via rocq_check(from_state=...) or rocq_step_multi(from_state=...).

    When proof_finished=True, also returns proof_tactics (ordered list of
    all tactics from root to current state) and proof_hint (instructions
    for assembling the final .v file).  On a broken walk (an ancestor
    state was LRU-evicted, or a cycle was detected), proof_tactics and
    proof_hint are omitted; the response carries ``proof_tactics_status``
    (``"ancestor_evicted"`` or ``"cycle"``), ``proof_tactics_broken_at``
    (the state id where the walk gave up), and ``proof_tactics_hint``
    instead — clients that ignore these keys see no half-chain at all.

    Recommended workflow (each step threads ``state_id`` explicitly):
    1. ``s0 = rocq_start(file=..., theorem=...)["state_id"]``
    2. ``s1 = rocq_check(from_state=s0, body="intros. simpl.")["state_id"]``
    3. If stuck: ``rocq_step_multi(from_state=s1, tactics=[...])`` to explore
    4. ``rocq_check(from_state=s1, body="winning_tactic.")`` to commit

    When commands produce visible output (e.g., ``Print``, ``Check``,
    ``vm_compute``, ``native_compute``), a ``feedback`` field is included
    as a list of ``[command, output]`` pairs (truncated per step at 50K
    chars).  Omitted when no command produces output.

    **Note:** If the underlying .v file is modified after rocq_start, the
    session state becomes stale. A ``stale_warning`` field is returned when
    this is detected. Restart the session with rocq_start after file edits.

    Args:
        body: Commands to execute (one or more Rocq sentences).
        from_state: State ID to execute from.  Required — use the
            ``state_id`` returned by ``rocq_start`` or a previous
            ``rocq_check``.  There is no implicit "current state"
            fallback (avoids cross-agent state confusion when peers
            share this rocq-mcp process).
        workspace: Accepted for API compatibility but unused; the
            active workspace comes from the state entry set by
            ``rocq_start``.
        timeout: Per-call timeout in seconds for the batch of commands.
            Default 0 uses ``ROCQ_PET_TIMEOUT`` (env var, default 30).
            Raise this for compute-heavy tactics (``vm_compute``,
            ``native_compute``).  Clamped to ``ROCQ_QUERY_TIMEOUT_CAP``
            (default 300s) so a stray large value cannot park the pet
            lock indefinitely; when clamping fires the response includes
            ``clamped_timeout: <cap>`` so the caller can diagnose
            unexpected timeouts.
        include_warnings: If True (default), per-step ``feedback`` includes
            all severities.  If False, drop entries at LSP Warning severity.

    On ``pet_restarted: True``, call ``rocq_diag`` for memory headroom and
    recent error history.
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
    )
    if clamped and isinstance(result, dict):
        result["clamped_timeout"] = ROCQ_QUERY_TIMEOUT_CAP
    return result


@mcp.tool
async def rocq_diag(ctx: Context = None) -> dict[str, Any]:
    """Operational diagnostics: pet health, memory headroom, recent errors.

    Use this when:
    - A tool returned ``pet_restarted: True`` and you want to see what
      happened.
    - You're considering a long ``vm_compute`` and want to check memory
      headroom against ``max_rss_mb_threshold``.
    - You want to know which proof states are currently live in pet's
      state table.
    - You suspect another agent is sharing this rocq-mcp process.
      Heuristic: compare ``live_states[*].file`` against the files you
      opened this session — entries you did not create signal a foreign
      caller (works only when agents are on disjoint files).  Actively
      used states are LRU-protected against peer churn, so sharing is
      mostly a latency and RAM concern; if repeated state expiries
      survive that floor, ``rocq_start(..., force_restart=True)`` is
      the recovery — see README "Concurrency model".

    Does NOT spawn pet if it's not running; just reports state.

    Response shape:

    - ``server_version``: the rocq-mcp package version (from
      ``importlib.metadata``).  Include in bug reports.
    - ``pet``: ``{pid, uptime_seconds, restarts, generation}``
    - ``memory``: ``{pet_rss_mb, peak_pet_rss_mb, max_rss_mb_threshold,
      sample_status}`` where ``sample_status`` is one of ``"ok"`` /
      ``"no_pet"`` / ``"psutil_error"`` and disambiguates a ``None``
      ``pet_rss_mb``.
    - ``live_states``: capped at 50 most-recent entries (by
      ``created_at``) to keep the payload bounded.  Each entry has
      ``{state_id, parent, file, theorem, age_seconds}``.
    - ``live_states_total``: full count of entries in the state table
      (use this to detect that ``live_states`` was truncated).
    - ``recent_errors``: ring buffer of the last 20 errors, each
      ``{tool, message, reason, ago_seconds}``.  ``reason`` is one of:

      - **Pet-side** (set by ``_run_with_pet``): ``"timeout"``,
        ``"crashed"``, ``"memory_exhausted"``, ``"lock_contended"``,
        ``"unavailable"``.
      - **Validation / lookup** (set by tools before pet): ``"validation"``,
        ``"not_found"`` (rocq_start / rocq_assumptions on a typo).
      - **rocq_check mid-batch**: ``"tactic_failed"`` (a tactic was
        rejected by Coq — distinct from a transport-level ``"crashed"``).
      - **rocq_verify-specific**: ``"compile_error"``,
        ``"axiom_dependency"``, ``"type_mismatch"``.

      The full set is :data:`_RECENT_ERROR_REASONS`.
    """
    if ctx is None:
        return _no_ctx_fail("rocq_diag")
    return _build_diag_snapshot(ctx.lifespan_context)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> None:
    """Run the MCP server."""
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
