"""Workspace resolution, project-flag parsing, and artifact hygiene.

Everything about *where* Rocq work happens: workspace validation and
path containment, ``_RocqProject`` / ``_CoqProject`` / dune load-path
parsing (with the ``-arg`` allowlist), project-root discovery from a
file path, ``.vo`` rebuild detection for staleness warnings, and coqc
temp-artifact cleanup.

Extracted verbatim from ``server.py`` (the decomposition's first
cluster).  Imports only :mod:`rocq_mcp.config` — importable standalone,
no cycle.  ``_count_sessions_in_workspace`` reaches into
:mod:`rocq_mcp.interactive` via a function-body import (runtime only).
"""

from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

from rocq_mcp import config

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
    # Only enforce containment when config.ROCQ_WORKSPACE was explicitly set
    if config._ROCQ_WORKSPACE_EXPLICIT:
        root = Path(config.ROCQ_WORKSPACE).resolve()
        if not _path_within(ws, root):
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

    Relative paths are resolved against ``config.ROCQ_WORKSPACE``; symlinks
    are not followed.
    """
    if not file:
        return None
    try:
        p = Path(file)
        if not p.is_absolute():
            p = Path(config.ROCQ_WORKSPACE) / p
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
      we fell back to ``config.ROCQ_WORKSPACE``, which itself has no marker).

    Stays quiet for the markerless-by-design case: tools that don't
    take ``file=`` (e.g. ``rocq_compile`` with source-string, default
    ``rocq_notations``) running against a markerless ``config.ROCQ_WORKSPACE``
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
