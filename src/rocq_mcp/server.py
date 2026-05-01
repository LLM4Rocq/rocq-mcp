"""Rocq MCP Server — tools for Rocq/Coq proof development.

This is the main entry point.  It defines the MCP application, shared
infrastructure (configuration, workspace validation, pet subprocess
management), and thin ``@mcp.tool`` wrappers that delegate to
implementation functions in :mod:`rocq_mcp.compile` and
:mod:`rocq_mcp.interactive`.
"""

from __future__ import annotations

import asyncio
import os
import re
import signal
import subprocess
import tempfile
import threading
from pathlib import Path
from typing import Any, Callable, Literal, TypedDict, get_args

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
ROCQ_COQC_BINARY: str = os.environ.get("ROCQ_COQC_BINARY", "coqc")
ROCQ_MAX_SOURCE_SIZE: int = int(os.environ.get("ROCQ_MAX_SOURCE_SIZE", "1000000"))

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


def _validate_workspace(workspace: str) -> str | None:
    """Return error message if workspace is invalid, None if OK."""
    ws = Path(workspace).resolve()
    # Only enforce containment when ROCQ_WORKSPACE was explicitly set
    if _ROCQ_WORKSPACE_EXPLICIT:
        root = Path(ROCQ_WORKSPACE).resolve()
        if ws != root and not str(ws).startswith(str(root) + os.sep):
            return f"Workspace must be within {root}"
    if not ws.is_dir():
        return f"Workspace directory does not exist: {ws}"
    if not os.access(ws, os.W_OK):
        return f"Workspace directory is not writable: {ws}"
    return None


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
    resolved = (ws / dir_arg).resolve()
    ws_resolved = ws.resolve()
    if resolved == ws_resolved or str(resolved).startswith(str(ws_resolved) + os.sep):
        return dir_arg
    return None


def _resolve_file_in_workspace(file: str, workspace: str) -> str:
    """Resolve *file* relative to *workspace* and verify containment.

    Returns the resolved absolute path as a string.

    Raises:
        ValueError: If the resolved path escapes the workspace.
        FileNotFoundError: If the file does not exist on disk.
    """
    resolved = str((Path(workspace).resolve() / file).resolve())
    ws_resolved = str(Path(workspace).resolve())
    if not resolved.startswith(ws_resolved + os.sep) and resolved != ws_resolved:
        raise ValueError("File path must be within workspace.")
    if not Path(resolved).is_file():
        raise FileNotFoundError(f"File not found: {file}")
    return resolved


_PROJECT_MARKERS: tuple[str, ...] = ("_RocqProject", "_CoqProject", "dune-project")


def _find_project_root_from_file(file: str | None) -> str | None:
    """Walk up from *file* looking for a Rocq project marker.

    Returns the directory of the innermost ``_RocqProject``,
    ``_CoqProject``, or ``dune-project`` (in that priority order),
    or ``None`` if no marker is found before the filesystem root.
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


_DUNE_HEADER = "# Auto-generated by rocq-mcp from dune\n"


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
        lifespan_state["pet_client"] = pet
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


async def _run_with_pet(
    fn: Callable[[Any], Any],
    lifespan_state: dict[str, Any],
    description: str,
    on_timeout: Callable[[], None] | None = None,
    timeout: float | None = None,
    partial_state: dict[str, Any] | None = None,
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

    When pet crashes (timeout, broken pipe), the return dict includes
    ``"pet_restarted": True`` so callers can decide whether to retry.

    If *partial_state* is given (a mutable dict), *fn* can populate it
    with intermediate results.  On timeout or error the dict contents
    are merged into the error response so partial work is not lost.

    The return type is left as ``Any`` because the dict shape varies by
    failure mode (success path, ``pet_restarted``-tagged crashes,
    ``partial_state`` merges, etc.) and a TypedDict would be unwieldy.
    The ``"reason"`` key, when present on a failure, is a
    :data:`_StateCaptureStatus` (one of ``"timeout"``, ``"crashed"``,
    ``"lock_contended"``, ``"unavailable"``).
    """
    try:
        from pytanque import PetanqueError
    except ImportError:
        return {
            "success": False,
            "error": (
                "pytanque is not installed. "
                "Install with: pip install 'rocq-mcp[interactive]'"
            ),
            "reason": "unavailable",
        }

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
        try:
            result = await asyncio.wait_for(
                asyncio.to_thread(_execute),
                timeout=_timeout,
            )
            return result
        except asyncio.TimeoutError:
            _invalidate_pet(lifespan_state)
            await _force_release_pet_lock()
            if on_timeout:
                on_timeout()
            resp = {
                "success": False,
                "error": f"{description} timed out after {_timeout}s.",
                "pet_restarted": True,
                "reason": "timeout",
            }
            if partial_state:
                _merge_partial_state(resp, partial_state)
            return resp
        except _PetLockTimeout:
            return {
                "success": False,
                "error": (f"{description}: pet is busy (lock contention). Try again."),
                "reason": "lock_contended",
            }
        except PetanqueError as e:
            if not _pet_alive(lifespan_state.get("pet_client")):
                _invalidate_pet(lifespan_state)
                await _force_release_pet_lock()
                resp = {
                    "success": False,
                    "error": f"Pet process died: {e.message}",
                    "pet_restarted": True,
                    "reason": "crashed",
                }
                if partial_state:
                    _merge_partial_state(resp, partial_state)
                return resp
            return {"success": False, "error": e.message, "reason": "crashed"}
        except (BrokenPipeError, ConnectionError) as e:
            _invalidate_pet(lifespan_state)
            await _force_release_pet_lock()
            if on_timeout:
                on_timeout()
            resp = {
                "success": False,
                "error": f"Pet process died: {e}",
                "pet_restarted": True,
                "reason": "crashed",
            }
            if partial_state:
                _merge_partial_state(resp, partial_state)
            return resp
        except FileNotFoundError:
            return {
                "success": False,
                "error": "pet binary not found on PATH. Install coq-lsp.",
                "reason": "unavailable",
            }
        except (OSError, RuntimeError, ValueError, TypeError) as e:
            resp = {
                "success": False,
                "error": f"Unexpected error: {e}",
                "reason": "crashed",
            }
            if partial_state:
                _merge_partial_state(resp, partial_state)
            return resp


# ---------------------------------------------------------------------------
# Import implementation functions from submodules
# ---------------------------------------------------------------------------
# NOTE: These imports MUST come after all shared infrastructure above is
# defined, because compile and interactive import from this module.

from rocq_mcp.compile import (  # noqa: E402
    _PROOF_FILE_LABEL,
    _first_error_from_positions,
    run_compile,
    run_compile_file,
    run_verify,
)
from rocq_mcp.interactive import (  # noqa: E402
    _state_remove,
    run_assumptions,
    run_query,
    run_start,
    run_check,
    run_step_multi,
    run_toc,
    run_notations,
)

# ---------------------------------------------------------------------------
# Compile-error-state orchestration
# ---------------------------------------------------------------------------
# These helpers wrap the coqc-only run_compile / run_compile_file with
# best-effort PET state capture at the error position.  They live here
# (not in compile.py) so compile.py stays free of any pytanque dependency
# for its core operation.

# Cap on how long enrichment may spend per call.  Coqc has already returned
# the basic error by the time we reach this code, so a stuck pet must not
# silently steal more than this from the agent.
_ENRICHMENT_TIMEOUT_CAP: float = float(
    os.environ.get("ROCQ_ENRICHMENT_TIMEOUT_CAP", "5.0")
)

# Status enum for proof-state capture on compile errors.  Used as the
# value type of the ``state_capture_status`` key returned by the
# ``run_compile_*_with_state`` orchestrators.  A subset
# (``"timeout"``, ``"crashed"``, ``"lock_contended"``, ``"unavailable"``)
# is also produced inside ``_run_with_pet`` under the dict key
# ``"reason"``; the remaining values (``"ok"``, ``"outside_proof"``,
# ``"no_position"``) are derived in the orchestrator.
_StateCaptureStatus = Literal[
    "ok",
    "outside_proof",
    "timeout",
    "crashed",
    "unavailable",
    "lock_contended",
    "no_position",
]

_VALID_STATE_CAPTURE_STATUSES: frozenset[str] = frozenset(get_args(_StateCaptureStatus))


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
    resolved_file: str | None = None,
    timeout: float | None = None,
) -> _CaptureResult:
    """Best-effort PET lookup of the proof state at a compile error.

    Returns a :class:`_CaptureResult` ``{"status": <_StateCaptureStatus>,
    "state": <dict|None>}``.  ``state`` is the captured state dict on
    ``"ok"`` / ``"outside_proof"``, ``None`` otherwise.
    """
    # Lazy import: defensive against a future split where rocq_mcp.interactive
    # becomes optional. In current packaging this branch is unreachable; the
    # realistic "unavailable" case fires from _run_with_pet via
    # reason="unavailable".
    try:
        from rocq_mcp.interactive import capture_position_state as _cps
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
            state_result = await _cps(
                file=file_label,
                resolved_file=lookup_file,
                workspace=workspace,
                lifespan_state=lifespan_state,
                line=line,
                character=character,
                description="Compile error state capture",
                track_staleness=resolved_file is not None,
                timeout=timeout,
            )
        except Exception:
            # PetanqueError (or any other exception) escaping capture_position_state
            # is treated as a crash so the caller can surface ``state_capture_status``.
            return {"status": "crashed", "state": None}
    finally:
        if temp_path is not None:
            _cleanup_coqc_artifacts(temp_path)

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
    pet_timeout = lifespan_state.get("pet_timeout", ROCQ_PET_TIMEOUT)
    return min(float(pet_timeout), _ENRICHMENT_TIMEOUT_CAP)


async def _enrich_compile_failure(
    result: dict[str, Any],
    *,
    source: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    file_label: str,
    resolved_file: str | None = None,
) -> dict[str, Any]:
    """Apply state-capture enrichment to a failed compile result.

    Mutates *result* in place and returns it.  Sets ``state_capture_status``
    (a :data:`_StateCaptureStatus`) on every path: ``"no_position"`` when
    there is no usable error position, otherwise the status returned by
    :func:`_capture_compile_error_state`.

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
    if lifespan_state is None or result.get("success"):
        return result
    return await _enrich_compile_failure(
        result,
        source=source,
        workspace=workspace,
        lifespan_state=lifespan_state,
        file_label=_PROOF_FILE_LABEL,
    )


async def run_compile_file_with_state(
    file: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
    lifespan_state: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Async wrapper for run_compile_file that enriches failures with PET state."""
    try:
        resolved_file = _resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError):
        resolved_file = None

    result = run_compile_file(file, workspace, timeout, include_warnings)
    if lifespan_state is None or result.get("success"):
        return result
    if resolved_file is None:
        result["state_capture_status"] = "no_position"
        return result
    return await _enrich_compile_failure(
        result,
        source="",
        workspace=workspace,
        lifespan_state=lifespan_state,
        file_label=file,
        resolved_file=resolved_file,
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
    """Compile Rocq source code and return structured errors.

    Batch-compiles a complete .v file via coqc. Best for checking a
    finished proof. For iterative proof development, prefer
    rocq_check (faster, cached imports, returns state for recovery)
    or rocq_step_multi (try multiple tactics at once).

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
        ``"unavailable"`` / ``"no_position"``: enrichment did not
        succeed; follow the original ``hint`` (typically
        ``rocq_start(file=..., line=..., character=...)``).

    Args:
        source: Complete Rocq (.v) file content to compile.
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Compilation timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
        include_warnings: If True (default), include deduplicated warnings
            before the error in the output.  Set to False to get only the
            error diagnostic, which keeps context compact.
    """
    workspace = workspace or ROCQ_WORKSPACE
    timeout = timeout if timeout is not None and timeout > 0 else ROCQ_COQC_TIMEOUT

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    return await run_compile_with_state(
        source=source,
        workspace=workspace,
        timeout=timeout,
        include_warnings=include_warnings,
        lifespan_state=ctx.lifespan_context if ctx else None,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_compile_file
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_compile_file(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
    ctx: Context = None,
) -> dict[str, Any]:
    """Compile a Rocq (.v) file on disk and return structured errors.

    Like rocq_compile but takes a file path instead of source string.
    More efficient for large files (avoids transmitting full source).
    The file must already exist within the workspace.

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
        ``"unavailable"`` / ``"no_position"``: enrichment did not
        succeed; follow the original ``hint`` (typically
        ``rocq_start(file=..., line=..., character=...)``).

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
    """
    # Workspace precedence: explicit arg > project marker walk-up > env default.
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    timeout = timeout if timeout is not None and timeout > 0 else ROCQ_COQC_TIMEOUT

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    return await run_compile_file_with_state(
        file=file,
        workspace=workspace,
        timeout=timeout,
        include_warnings=include_warnings,
        lifespan_state=ctx.lifespan_context if ctx else None,
    )


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
    """
    workspace = workspace or ROCQ_WORKSPACE
    timeout = timeout if timeout is not None and timeout > 0 else ROCQ_VERIFY_TIMEOUT

    err = _validate_workspace(workspace)
    if err:
        return {"verified": False, "error": err}

    return await run_verify(
        proof=proof,
        problem_name=problem_name,
        problem_statement=problem_statement,
        workspace=workspace,
        timeout=timeout,
        include_warnings=include_warnings,
        lifespan_state=ctx.lifespan_context if ctx else None,
    )


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
    ctx: Context = None,
) -> dict[str, Any]:
    """Search the Rocq environment — find lemmas, check types, inspect definitions.

    Does NOT modify any proof state. Use this to explore before proving:
      command="Search (nat -> nat -> nat)."  — find relevant lemmas
      command="Check Nat.add."               — check a term's type
      command="Print Nat.add."               — see a definition
      command="About plus."                  — summary of a name

    Two context modes (mutually exclusive):
    - **preamble mode** (default): pass import commands as a string.
    - **file mode**: pass a ``.v`` file path; the query runs with all
      definitions from that file in scope.  More reliable than preamble
      because it captures ``Open Scope``, ``Set`` options, etc.

    Args:
        command: The Rocq query command to execute.
        preamble: Optional import lines needed for the query context
                  (e.g., "Require Import Reals.\\nOpen Scope R_scope.").
        file: Path to a .v file (relative to workspace) whose definitions
            should be in scope. Mutually exclusive with preamble.
        workspace: Workspace directory.  If omitted, auto-detected by walking
            up from *file* looking for ``_RocqProject`` / ``_CoqProject`` /
            ``dune-project``; falls back to the ``ROCQ_WORKSPACE`` env var
            (default: cwd).
        max_results: Optional maximum number of results to return.
            Useful for broad Search patterns. If omitted, all results are
            returned (subject to character limit).
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_query(
        command=command,
        preamble=preamble,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
        file=file,
        max_results=max_results,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_assumptions
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_assumptions(
    name: str,
    file: str,
    workspace: str = "",
    ctx: Context = None,
) -> dict[str, Any]:
    """Check what axioms a theorem depends on.

    Runs Print Assumptions on the given theorem/lemma name and classifies
    the result. Returns whether the proof is closed (no axioms),
    uses only standard axioms (classical logic, Reals, etc.), or has
    suspicious/unproved assumptions.

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
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_assumptions(
        name=name,
        file=file,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_toc
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_toc(
    file: str,
    workspace: str = "",
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
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_toc(
        file=file,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_notations
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_notations(
    statement: str,
    preamble: str = "",
    workspace: str = "",
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
    """
    workspace = workspace or ROCQ_WORKSPACE

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_notations(
        statement=statement,
        preamble=preamble,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
    )


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
    ctx: Context = None,
) -> dict[str, Any]:
    """Start an interactive proof session — see goals, explore tactics.

    Returns a state_id for use with rocq_check and rocq_step_multi.
    Also returns the current proof goals at the starting position,
    so this tool can be used to inspect goals at any point in a file.

    Three start modes (precedence: theorem > position > preamble):
    1. By theorem: file + theorem — start proving a specific theorem
    2. By position: file + line + character — jump to any position in
       a file and see the proof goals there.  Useful for inspecting
       proof state at a specific point, or recovering from an error
       position returned by rocq_compile.
    3. From imports: preamble — set up import context only (for rocq_check)

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
        force_restart: If True, kill the current PET process and clear all
            cached state before starting.  Use when PET is alive but in a
            bad state (e.g., coq-lsp indexing corruption).  You rarely need
            this — PET auto-restarts on crash/timeout.  Default: False.
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_start(
        file=file,
        theorem=theorem,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
        line=line,
        character=character,
        preamble=preamble,
        force_restart=force_restart,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_step_multi(
    tactics: list[str],
    from_state: int | None = None,
    ctx: Context = None,
) -> dict[str, Any]:
    """Try multiple tactics at once — find what works without guessing.

    Tests each tactic against the current proof state and returns all
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

    Requires an active state from rocq_start or rocq_check (or use from_state).

    Args:
        tactics: List of tactics to try (max 20).
        from_state: Try from a specific state (default: current state).
    """
    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_step_multi(
        tactics=tactics,
        lifespan_state=ctx.lifespan_context,
        from_state=from_state,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_check
# ---------------------------------------------------------------------------


@mcp.tool
async def rocq_check(
    body: str,
    from_state: int | None = None,
    workspace: str = "",
    timeout: int = 0,
    ctx: Context = None,
) -> dict[str, Any]:
    """Run proof commands from cached imports — fast iterative checking.

    Much faster than rocq_compile for iterative proof development:
    imports are cached (first call processes them, subsequent calls skip), and on error
    returns the last valid state for immediate interactive recovery
    via rocq_check(from_state=...) or rocq_step_multi(from_state=...).

    When proof_finished=True, also returns proof_tactics (ordered list of
    all tactics from root to current state) and proof_hint (instructions
    for assembling the final .v file).

    Recommended workflow:
    1. rocq_start(file=..., theorem=...) to open the proof
    2. rocq_check(body="intros. simpl.") to advance
    3. If stuck: rocq_step_multi(tactics=[...]) to explore
    4. rocq_check(body="winning_tactic.") to commit

    When commands produce visible output (e.g., ``Print``, ``Check``,
    ``vm_compute``, ``native_compute``), a ``feedback`` field is included
    as a list of ``[command, output]`` pairs (truncated per step at 50K
    chars).  Omitted when no command produces output.

    **Note:** If the underlying .v file is modified after rocq_start, the
    session state becomes stale. A ``stale_warning`` field is returned when
    this is detected. Restart the session with rocq_start after file edits.

    Args:
        body: Commands to execute (one or more Rocq sentences).
        from_state: Execute from a specific state ID (default: current state).
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Timeout in seconds (default: ROCQ_PET_TIMEOUT env var).
    """
    # Note: workspace param is accepted for API compatibility but unused;
    # the active workspace comes from the state entry set by rocq_start.
    timeout = timeout if timeout is not None and timeout > 0 else ROCQ_PET_TIMEOUT

    if ctx is None:
        return {"success": False, "error": "Internal error: no MCP context."}

    return await run_check(
        body=body,
        timeout=float(timeout),
        lifespan_state=ctx.lifespan_context,
        from_state=from_state,
    )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> None:
    """Run the MCP server."""
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
