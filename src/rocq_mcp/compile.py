"""Rocq MCP Server — coqc-based tools (compile, verify).

This module contains the implementation of all tools that use the coqc
binary directly (no pytanque dependency for core operation).  The
``_extract_problem_structure`` helper used by Phase 2 verification is
the one exception — it uses pytanque via ``_run_with_pet``.
"""

from __future__ import annotations

import os
import re
import signal
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

from rocq_mcp.verify import (
    _check_forbidden_commands,
    _rocq_scan,
    build_verification_source,
    build_shared_defs_verification_source,
    build_direct_verification_source,
    build_direct_type_check_source,
    parse_check_type,
    normalize_type_for_comparison,
    classify_toc_detail,
    DefCategory,
    DefinitionInfo,
    parse_and_classify_assumptions,
    ProblemStructure,
    verification_hint,
    _validate_rocq_identifier,
)

# Access server attributes through the module reference so that
# monkeypatching ``rocq_mcp.server.ROCQ_COQC_BINARY`` (or _run_coqc,
# etc.) in tests is visible here.  A bare ``from server import X``
# would capture the value at import time, defeating monkeypatch.
import rocq_mcp.server as _server

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_MAX_ERROR_LENGTH: int = 4000
_MAX_FORMAT_WARNINGS: int = 3
_PROOF_FILE_LABEL: str = "<proof>"


# ---------------------------------------------------------------------------
# coqc runner
# ---------------------------------------------------------------------------


def _run_build_subprocess(
    args: list[str],
    cwd: str,
    timeout: int,
) -> dict[str, Any]:
    """Run *args* under *cwd* with graceful SIGTERM → SIGKILL timeout escalation.

    Shared by :func:`_run_coqc_process` (coqc) and :func:`_run_dune_build`
    (``dune build``) — both are long-running Rocq compiles that must not
    wedge the server on a diverging tactic.  On timeout the partial output
    buffers are still returned so the last completed sentence stays
    recoverable.

    Returns dict with keys ``returncode`` / ``stdout`` / ``stderr`` /
    ``timed_out``.  A missing / unexecutable ``args[0]`` yields
    ``returncode == -1`` with the reason in ``stderr``.
    """
    try:
        proc = subprocess.Popen(
            args,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=cwd,
            start_new_session=True,
        )
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
            return {
                "returncode": proc.returncode,
                "stdout": stdout,
                "stderr": stderr,
                "timed_out": False,
            }
        except subprocess.TimeoutExpired:
            # Graceful shutdown: SIGTERM first, escalate to SIGKILL
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            except OSError:
                try:
                    proc.terminate()
                except OSError:
                    pass
            try:
                stdout, stderr = proc.communicate(timeout=3)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                except OSError:
                    try:
                        proc.kill()
                    except OSError:
                        pass
                try:
                    stdout, stderr = proc.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    stdout, stderr = "", ""
            return {
                "returncode": -1,
                "stdout": stdout or "",
                "stderr": stderr or "",
                "timed_out": True,
            }
    except (FileNotFoundError, OSError) as e:
        return {
            "returncode": -1,
            "stdout": "",
            "stderr": (
                f"{args[0]} not found or not executable: {e}"
                if isinstance(e, FileNotFoundError)
                else f"Failed to run {args[0]}: {e}"
            ),
            "timed_out": False,
        }


def _run_coqc_process(
    file_path: str,
    workspace: Path,
    timeout: int,
    mode: str = "full",
    timing: bool = False,
    output: str | None = None,
) -> dict[str, Any]:
    """Run coqc on a .v file and return the result.

    Shared subprocess management for both :func:`_run_coqc` (temp files) and
    :func:`_run_coqc_file` (user files).  Handles timeout with graceful
    SIGTERM → SIGKILL escalation.

    When ``mode == "vos"`` passes ``-vos`` to coqc, which skips proof
    bodies (produces a ``.vos`` artifact instead of ``.vo``).

    When *timing* is True, coqc is invoked with ``-time`` so per-sentence
    timing diagnostics are emitted on stdout (coqc 9.x; older builds may
    have used stderr — :func:`_parse_timing_lines` tries stdout first and
    falls back to stderr).  On timeout the partial buffers are still
    returned so the last completed sentence remains recoverable.

    When *output* is given, coqc is passed ``-o <output>`` so the compiled
    ``.vo``/``.vos`` (and its sibling ``.glob``/``.aux``) land there rather
    than next to the source — used to target a dune ``_build/default`` path
    so the source tree stays free of ``.vo`` shadows.  coqc
    derives the module's logical name from the *output* path relative to the
    ``-R``/``-Q`` roots, so the caller must place *output* under the
    load-path root that maps to the file's logical prefix.

    Returns dict with keys:
        returncode: int
        stdout: str
        stderr: str
        timed_out: bool
    """
    coqc_args: list[str] = [
        _server.ROCQ_COQC_BINARY,
        *_server._parse_project_flags(workspace),
    ]
    if mode == "vos":
        coqc_args.append("-vos")
    if timing:
        coqc_args.append("-time")
    if output is not None:
        coqc_args += ["-o", output]
    coqc_args.append(file_path)
    return _run_build_subprocess(coqc_args, str(workspace), timeout)


def _run_coqc(source: str, workspace: str, timeout: int) -> dict[str, Any]:
    """Write source to temp file, run coqc, return result dict."""
    ws = Path(workspace).resolve()
    with tempfile.NamedTemporaryFile(
        suffix=".v", mode="w", delete=False, dir=str(ws)
    ) as f:
        f.write(source)
        f.flush()
        tmp_path = f.name

    try:
        return _run_coqc_process(tmp_path, ws, timeout)
    finally:
        _server._cleanup_coqc_artifacts(tmp_path)


_VO_FAMILY: tuple[str, ...] = (".vo", ".vok", ".vos")


def _run_coqc_file(
    file_path: str,
    workspace: str,
    timeout: int,
    keep_vo: bool = False,
    mode: str = "full",
    timing: bool = False,
    output: str | None = None,
) -> dict[str, Any]:
    """Run coqc on an existing .v file, return result dict.

    Unlike :func:`_run_coqc`, does NOT create a temp file — runs coqc
    directly on the given file.  Cleans up compilation artifacts but
    preserves the source .v file.  When *keep_vo* is True, also
    preserves the ``.vo``/``.vok``/``.vos`` compiled-artifact family
    so the produced ``.vo`` is available to sibling files importing
    it; the diagnostic artifacts (``.glob``/``.aux``/``.vio``/
    ``.timing``/``.coqaux``) are still cleaned.

    When ``mode == "vos"`` passes ``-vos`` to coqc, which checks
    statements / imports / notations but skips proof bodies.  Produces
    a ``.vos`` artifact rather than a ``.vo``.

    When *timing* is True, coqc is invoked with ``-time`` and its
    per-sentence timing lines land in the returned ``stderr`` for the
    caller to parse via :func:`_parse_timing_lines`.

    When *output* is given it is forwarded to coqc as ``-o`` (see
    :func:`_run_coqc_process`).  coqc then writes *every* artifact next to
    *output* (a dune ``_build/default`` path), so the source-tree cleanup
    below finds nothing to remove — the ``_build`` artifacts are left in
    place regardless of *keep_vo* (they belong to the build dir, and after
    ``dune``-style load-path resolution siblings import them from there).
    """
    ws = Path(workspace).resolve()
    try:
        return _run_coqc_process(
            file_path, ws, timeout, mode=mode, timing=timing, output=output
        )
    finally:
        base = Path(file_path).with_suffix("")
        for ext in _server._CLEANUP_EXTENSIONS:
            if ext == ".v":
                continue
            if keep_vo and ext in _VO_FAMILY:
                continue
            base.with_suffix(ext).unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Error formatting
# ---------------------------------------------------------------------------

_COQC_POS_RE = re.compile(
    r'File "[^"]*", line (\d+), characters (\d+)-(\d+):\s*\n((?:Error|Warning):.*?)(?=File "|$)',
    re.DOTALL,
)


# Pattern → diagnostic-hint table for common configuration errors.
# Each entry pairs a compiled regex against an error string with a
# template.  Templates may reference named groups from the match
# (``{name}``) to incorporate the offending identifier into the hint.
#
# Why this exists: the bare coqc error tells the agent what failed
# but not *why* — and the why is almost always a workspace/load-path
# misconfiguration, not a proof bug.  Hints here steer the agent
# toward fixing config instead of grinding tactics.
_MISSING_LOAD_PATH_RE = re.compile(
    r"Cannot find a physical path bound to logical path\s+(?P<name>[\w.]+)",
    re.IGNORECASE,
)
_VERSION_MISMATCH_RE = re.compile(
    r"makes inconsistent assumptions over library\s+(?P<library>[\w.]+)",
    re.IGNORECASE,
)


def _diagnostic_hint_for_error(error: str | None) -> str | None:
    """Return an actionable diagnostic hint for *error*, or None.

    Pattern-matches the coqc error text against known configuration
    failure modes.  Returns a one-line hint mentioning the
    misconfigured surface (load path, Coq version) and the offending
    identifier from the error, when extractable.

    Recovery-style hints (use rocq_start at the position, etc.) are
    set elsewhere and remain in the response.  This function returns
    a *separate* string that callers can attach as
    ``diagnostic_hint`` so the agent can choose to read both.

    Returns None when:
    - *error* is empty or None
    - no pattern matched (likely a proof-level error — the existing
      recovery hint is the right guidance)
    """
    if not error:
        return None
    m = _MISSING_LOAD_PATH_RE.search(error)
    if m is not None:
        # Strip the trailing sentence period that the regex's [\w.]+
        # greedily captures — the user expects a clean logical name.
        name = m.group("name").rstrip(".")
        return (
            f"Load-path mismatch: no -Q / -R mapping for logical "
            f"path '{name}'. Check the workspace's _CoqProject "
            f"(or _RocqProject) for a line like '-Q <dir> {name}' "
            f"and verify <dir> exists and contains compiled .vo "
            f"files. If the directory lives outside the workspace, "
            f"see the path-containment rules in README.md."
        )
    m = _VERSION_MISMATCH_RE.search(error)
    if m is not None:
        library = m.group("library").rstrip(".")
        return (
            f"Probable Coq version mismatch: the workspace's .vo "
            f"files were compiled against a different Coq version "
            f"than the coqc currently in PATH (offending library: "
            f"'{library}'). Run `coqc --version` and compare with "
            f"the version that produced your dependencies, then "
            f"either install the matching Coq via opam or rebuild "
            f"the .vo files with the current coqc."
        )
    return None


def _parse_coqc_error_positions(
    stderr: str,
    *,
    include_warnings: bool = True,
) -> list[dict[str, Any]]:
    """Parse coqc stderr into structured error positions.

    coqc uses 1-based lines, 0-based characters.
    Returns 0-based line numbers (for pytanque compatibility).

    The regex matches both ``Error:`` and ``Warning:`` diagnostics; when
    ``include_warnings=False``, ``Warning:`` entries are filtered out so
    callers don't surface warning bodies via this structured channel.
    """
    positions = []
    for m in _COQC_POS_RE.finditer(stderr):
        line_1based = int(m.group(1))
        char_start = int(m.group(2))
        char_end = int(m.group(3))
        message = m.group(4).strip()
        if not include_warnings and message.startswith("Warning:"):
            continue
        positions.append(
            {
                "line": line_1based - 1,
                "character": char_start,
                "end_character": char_end,
                "message": message[:500],
            }
        )
    return positions


def _first_error_from_positions(
    positions: list[dict[str, Any]],
) -> dict[str, Any] | None:
    """Return the first Error-level entry from parsed diagnostic positions."""
    for pos in positions:
        if pos["message"].startswith("Error:"):
            return pos
    return None


# Regex to match coqc diagnostic blocks: File "path", line N, characters S-E:\n<body>
_COQC_DIAG_RE = re.compile(
    r'(File "([^"]*)", line (\d+), characters (\d+)-(\d+):\s*\n)(.*?)(?=File "|$)',
    re.DOTALL,
)

# Regex to extract Error/Warning kind from body
_KIND_RE = re.compile(r"^(Error|Warning)\b")

# Regex to replace tmp file paths with <proof>
_TMP_PATH_RE = re.compile(r'"[^"]*tmp[^"]*\.v"')

_WARNING_PREFIX = "Warning:"


def _drop_warning_lines(text: str) -> str:
    """Drop lines that begin with `Warning:` (after leading whitespace).

    Used as the unstructured fallback when a coqc stderr block has no
    `File "..."` header to anchor structured `_format_error` parsing.
    """
    return "\n".join(
        line
        for line in text.splitlines()
        if not line.lstrip().startswith(_WARNING_PREFIX)
    ).strip()


def _format_error(
    error_str: str,
    proof_str: str,
    *,
    include_warnings: bool = True,
    file_label: str = _PROOF_FILE_LABEL,
) -> str:
    """Reformat a raw coqc stderr string into LLM-friendly feedback.

    - Replaces the opaque tmp file path with ``file_label``
    - Annotates the first Error-level diagnostic with the source line
      and a caret underline marking the exact character range
    - Suppresses pure-warning outputs (they don't prevent compilation)

    Args:
        error_str: Raw coqc stderr output.
        proof_str: The Rocq source that was compiled (for source annotations).
        include_warnings: If True (default), include deduplicated warnings
            that precede the first error.  If False, return only the error
            diagnostic itself — useful when warnings would drown the context.
        file_label: Label to use in error headers instead of the temp file
            path.  Defaults to ``"<proof>"``.

    Falls back to the raw string (path-cleaned) when no structured
    location info is present (timeouts, workspace errors, etc.).
    """
    if not error_str:
        return error_str

    proof_lines = proof_str.splitlines()
    diagnostics = list(_COQC_DIAG_RE.finditer(error_str))

    if not diagnostics:
        cleaned = _TMP_PATH_RE.sub(f'"{file_label}"', error_str).strip()
        if not include_warnings:
            cleaned = _drop_warning_lines(cleaned)
        # Cap output so unstructured errors don't drown LLM context
        if len(cleaned) > _MAX_ERROR_LENGTH:
            cleaned = cleaned[-_MAX_ERROR_LENGTH:]
        return cleaned

    parsed = []
    for m in diagnostics:
        kind_m = _KIND_RE.match(m.group(6).strip())
        parsed.append(
            {
                "kind": kind_m.group(1) if kind_m else "Error",
                "line": int(m.group(3)),
                "char_start": int(m.group(4)),
                "char_end": int(m.group(5)),
                "body": m.group(6).strip(),
            }
        )

    has_errors = any(d["kind"] == "Error" for d in parsed)
    if not has_errors:
        return ""

    # Select diagnostics to include in the output.
    # Deduplicate warnings by body text — coqc often emits the same
    # deprecation notice multiple times during elaboration.
    # Cap at _MAX_FORMAT_WARNINGS unique warnings to avoid drowning
    # LLM context (large projects can emit many unique warnings).
    selected = []
    seen_warnings: set[str] = set()
    for d in parsed:
        if d["kind"] == "Warning":
            if not include_warnings:
                continue
            if d["body"] in seen_warnings:
                continue
            if len(seen_warnings) >= _MAX_FORMAT_WARNINGS:
                continue
            seen_warnings.add(d["body"])
        selected.append(d)
        if d["kind"] == "Error":
            break

    parts = []
    for d in selected:
        line_1 = d["line"]
        char_start = d["char_start"]
        char_end = d["char_end"]

        header = f"{file_label}, line {line_1}, characters {char_start}-{char_end}:"

        line_idx = line_1 - 1
        source_line = (
            proof_lines[line_idx] if 0 <= line_idx < len(proof_lines) else None
        )

        annotation = ""
        if source_line is not None:
            prefix = f"  {line_1:4d} | "
            caret_offset = len(prefix) + char_start
            caret_len = max(1, char_end - char_start)
            annotation = (
                f"\n{prefix}{source_line}\n" f"{' ' * caret_offset}{'^' * caret_len}"
            )

        parts.append(f"{header}{annotation}\n{d['body']}")

    output = "\n\n".join(parts)
    if len(output) > _MAX_ERROR_LENGTH:
        output = output[-_MAX_ERROR_LENGTH:]
    return output


# ---------------------------------------------------------------------------
# Per-sentence timing diagnostics (coqc -time)
# ---------------------------------------------------------------------------

# Default number of slowest sentences to surface in the response.
_TIMING_TOP_N: int = 5

# coqc -time emits lines of the shape
#     Chars <start> - <end> [<vernac-name>] <duration> secs (<u>u,<s>s)
# where <duration> may be ``0.``, ``0.013``, etc.  The tail in
# parentheses is optional and varies across coqc versions, so the
# regex only anchors the prefix that all versions emit.
_TIMING_LINE_RE = re.compile(
    r"^Chars\s+(\d+)\s+-\s+(\d+)\s+\[([^\]]*)\]\s+([0-9.]+)\s+secs"
)


def _char_offset_to_line(source: str, offset: int) -> int:
    """Convert a 0-based character offset to a 1-based line number.

    O(N) per call in the size of *source* up to *offset*; acceptable
    because timing-line counts are bounded by source size.  Falls
    back to line 1 when *offset* is negative or out of range.
    """
    if offset <= 0 or not source:
        return 1
    capped = min(offset, len(source))
    return source.count("\n", 0, capped) + 1


def _parse_timing_lines(text: str, source: str) -> list[dict[str, Any]]:
    """Parse coqc ``-time`` lines from *text* into structured entries.

    coqc 9.x emits ``-time`` output on **stdout** (not stderr); earlier
    versions varied.  The parser is input-agnostic — it scans whatever
    text the caller hands it for ``Chars ... secs`` lines.

    Tolerant by design: any line that does not match
    :data:`_TIMING_LINE_RE` is ignored (warnings, errors, blanks all
    pass through silently).  When duration parsing fails the entry is
    dropped rather than poisoning the rest of the list — coqc emits
    ``0.`` and other unusual decimal shapes, so a permissive float
    cast with fallback keeps us robust to format drift.

    Each returned entry is a dict with keys ``line`` (1-based),
    ``characters`` (``[start, end]`` 0-based), ``name`` (vernac name
    as printed by coqc, with ``~`` left as-is — that is coqc's
    standard whitespace-substitute), and ``duration_seconds``.
    """
    entries: list[dict[str, Any]] = []
    if not text:
        return entries
    for raw_line in text.splitlines():
        m = _TIMING_LINE_RE.match(raw_line)
        if m is None:
            continue
        try:
            start = int(m.group(1))
            end = int(m.group(2))
            name = m.group(3)
            duration = float(m.group(4))
        except (TypeError, ValueError):
            continue
        entries.append(
            {
                "line": _char_offset_to_line(source, start),
                "characters": [start, end],
                "name": name,
                "duration_seconds": duration,
            }
        )
    return entries


def _strip_timing_lines(text: str) -> str:
    """Remove coqc ``-time`` lines from *text*.

    Used by :func:`_build_compile_result` when timing is enabled to
    keep the ``Chars ... secs`` noise out of the success-path
    ``output`` field (where they'd drown the rest of coqc's stdout).
    Non-timing lines are passed through unchanged.
    """
    if not text:
        return text
    return "\n".join(
        line for line in text.splitlines() if not _TIMING_LINE_RE.match(line)
    )


def _build_timing_field(
    timing_entries: list[dict[str, Any]],
    top_n: int = _TIMING_TOP_N,
) -> dict[str, Any]:
    """Assemble the ``timing`` response field from parsed entries.

    ``top_slowest`` is a stable-by-input-order sort by descending
    duration (Python sort is stable, so equal-duration entries keep
    source-position order).  ``last_completed`` is the final emitted
    entry — useful when coqc was killed mid-compile because it points
    at the sentence whose work was lost.
    """
    total = len(timing_entries)
    sorted_by_dur = sorted(
        timing_entries,
        key=lambda e: e["duration_seconds"],
        reverse=True,
    )
    top_slowest = sorted_by_dur[: max(0, top_n)]
    last_completed = timing_entries[-1] if timing_entries else None
    return {
        "total_sentences": total,
        "top_slowest": top_slowest,
        "last_completed": last_completed,
    }


def _format_last_completed_phrase(entry: dict[str, Any]) -> str:
    """Render a ``last_completed`` entry as a human-readable phrase."""
    return (
        f"line {entry['line']} [{entry['name']}] " f"({entry['duration_seconds']:.3g}s)"
    )


# ---------------------------------------------------------------------------
# Shared post-compilation result builder
# ---------------------------------------------------------------------------


def _truncate_error_text(text: str, include_warnings: bool) -> str:
    """Normalize a raw stderr blob for a compile-error ``error`` field.

    Drops warning lines when *include_warnings* is False, then tail-truncates
    to :data:`_MAX_ERROR_LENGTH` (keeping the end, where the actual error
    sits).  Dropping before truncating preserves more of the error tail than
    the reverse.  Shared by :func:`_build_compile_result`'s no-position
    fallback and :func:`_dune_dependency_error_result` so the truncation
    policy cannot drift between them.
    """
    text = text.strip()
    if not include_warnings:
        text = _drop_warning_lines(text).strip()
    if len(text) > _MAX_ERROR_LENGTH:
        text = text[-_MAX_ERROR_LENGTH:]
    return text


def _build_compile_result(
    result: dict[str, Any],
    source: str,
    timeout: int,
    include_warnings: bool,
    *,
    file_label: str = _PROOF_FILE_LABEL,
    clean_tmp_paths: bool = True,
    timing_field: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Build a structured result dict from a coqc subprocess result.

    Shared by ``run_compile`` (inline source) and ``run_compile_file`` (on-disk).

    Parameters
    ----------
    result : dict from ``_run_coqc`` / ``_run_coqc_file``
    source : the Rocq source text (for error context extraction)
    timeout : the timeout value used (for the timeout error message)
    include_warnings : passed to ``_format_error``
    file_label : label used in ``_format_error`` and fallback path cleaning
    clean_tmp_paths : if True, replace tmp file paths in fallback errors
    timing_field : when not None, the pre-built ``timing`` response field
        from :func:`_build_timing_field`.  Attached to every return path
        so callers see partial timings even on timeout or build failure.
        On timeout, the ``last_completed`` entry is also woven into the
        ``error`` string so the agent sees where coqc was stuck.
    """
    if result["timed_out"]:
        error_str = (
            f"Compilation timed out after {timeout}s. "
            "The proof may contain a diverging tactic. "
            "Retry with timing=True to identify the slowest sentence."
        )
        if timing_field is not None and timing_field.get("last_completed"):
            error_str = (
                f"Compilation timed out after {timeout}s. "
                "Last completed sentence: "
                f"{_format_last_completed_phrase(timing_field['last_completed'])}."
            )
        timeout_result: dict[str, Any] = {
            "success": False,
            "reason": "timeout",
            "error": error_str,
        }
        if timing_field is not None:
            timeout_result["timing"] = timing_field
        return timeout_result

    if result["returncode"] == 0:
        # With ``-time`` active, stdout is flooded with ``Chars ... secs``
        # entries; strip them from the displayable ``output`` so the user
        # sees the actual coqc messages without the timing-line firehose.
        stdout_for_output = (
            _strip_timing_lines(result["stdout"])
            if timing_field is not None
            else result["stdout"]
        )
        success_result: dict[str, Any] = {
            "success": True,
            "output": stdout_for_output[:2000],
        }
        if timing_field is not None:
            success_result["timing"] = timing_field
        return success_result

    # Older coqc versions may interleave timing on stderr; strip there too
    # so ``_format_error``'s diagnostic-block regex isn't fed phantom
    # body text.  Cheap when stderr has no timing lines.
    stderr_for_format = (
        _strip_timing_lines(result["stderr"])
        if timing_field is not None
        else result["stderr"]
    )

    error_text = _format_error(
        stderr_for_format,
        source,
        include_warnings=include_warnings,
        file_label=file_label,
    )
    if not error_text:
        raw = stderr_for_format
        if clean_tmp_paths:
            # Scrub tmp paths before truncation so paths in the tail are
            # cleaned too (regex is line-local, so ordering vs. warning-drop
            # doesn't matter for the surviving lines).
            raw = _TMP_PATH_RE.sub(f'"{file_label}"', raw)
        fallback = _truncate_error_text(raw, include_warnings)
        if not fallback:
            fallback = f"coqc exited with code {result['returncode']} (no stderr)."
        fallback_result: dict[str, Any] = {
            "success": False,
            "reason": "compile_error",
            "error": fallback,
        }
        if timing_field is not None:
            fallback_result["timing"] = timing_field
        return fallback_result

    positions = _parse_coqc_error_positions(
        stderr_for_format, include_warnings=include_warnings
    )
    result_dict: dict[str, Any] = {
        "success": False,
        "reason": "compile_error",
        "error": error_text,
    }
    if positions:
        result_dict["error_positions"] = positions
        result_dict["hint"] = (
            "Use rocq_start(file=..., line=..., character=...) to start "
            "an interactive session at the error position, then "
            "rocq_check or rocq_step_multi to explore fixes."
        )
    else:
        result_dict["hint"] = (
            "Use rocq_check for faster iteration, "
            "or rocq_step_multi to explore alternative tactics."
        )
    if timing_field is not None:
        result_dict["timing"] = timing_field
    # Attach a pattern-based diagnostic_hint when the error looks like
    # a recognised configuration failure (load path missing, Coq
    # version mismatch).  Recovery hints alone don't help the agent
    # *fix the cause* — diagnostic_hint does.
    diagnostic_hint = _diagnostic_hint_for_error(error_text)
    if diagnostic_hint:
        result_dict["diagnostic_hint"] = diagnostic_hint
    return result_dict


# ---------------------------------------------------------------------------
# Tool: rocq_compile (core implementation)
# ---------------------------------------------------------------------------


def run_compile(
    source: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Core implementation of rocq_compile (testable without FastMCP Context).

    Receives already-validated workspace and timeout.
    """
    if len(source) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "reason": "validation",
            "error": f"Source exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "reason": "validation", "error": forbidden}

    result = _run_coqc(source, workspace, timeout)
    return _build_compile_result(
        result,
        source,
        timeout,
        include_warnings,
    )


# ---------------------------------------------------------------------------
# dune-build integration
# ---------------------------------------------------------------------------

# dune reports this when asked to build a target it has no rule for — i.e. the
# ``.v`` is not part of any ``(coq.theory)`` / ``(rocq.theory)`` stanza (a
# scratch file, or one missing from an explicit ``(modules …)``).  It is the
# signal to fall back to a direct coqc compile.
_DUNE_RULE_MISSING_MARKER = "Don't know how to build"


def _dune_target_relpath(dune_root: Path, file_path: str, suffix: str) -> str | None:
    """Return *file_path*'s dune target relative to *dune_root*, or None.

    e.g. ``theory/use.v`` under root ``/proj`` with ``suffix=".vo"`` ->
    ``"theory/use.vo"``.  Returns None when *file_path* is outside
    *dune_root* (dune only knows targets within its own tree).
    """
    try:
        rel = Path(file_path).resolve().relative_to(dune_root.resolve())
    except ValueError:
        return None
    return str(rel.with_suffix(suffix))


def _dune_build_output(dune_root: Path, file_path: str, suffix: str) -> Path | None:
    """Return the ``_build/default/…`` artifact path for a coqc ``-o`` target.

    Mirrors dune's build layout: a source at ``<root>/theory/use.v`` builds to
    ``<root>/_build/default/theory/use.vo``.  Returns None when *file_path* is
    outside *dune_root*.
    """
    rel = _dune_target_relpath(dune_root, file_path, suffix)
    if rel is None:
        return None
    return dune_root.resolve() / "_build" / "default" / rel


def _clear_output_artifacts(out: Path, mode: str) -> None:
    """Remove the artifacts coqc's ``-o`` compile will (re)write at *out*.

    dune writes its ``_build/default`` artifacts read-only (and may hardlink
    them from a shared cache), so coqc's ``-o`` cannot overwrite the
    read-only ``.glob``/``.vos`` sibling and fails with a permission error.
    Unlinking first — the containing dir is writable — lets coqc regenerate
    them.  Crucially this *removes the directory entry* rather than writing
    through it, so any dune cache hardlink stays intact.

    Clears **only the set coqc recreates for this mode** — full compiles the
    whole ``.vo``/``.vok``/``.vos``/``.glob`` family (+ dot-prefixed
    ``.<name>.aux``); ``vos`` writes only the ``.vos``.  This matters:
    deleting a dune-tracked artifact that coqc will *not* recreate (e.g. the
    ``.vo`` in ``vos`` mode) desyncs dune's digest-db — dune then believes
    the target still exists and will not rebuild it until ``dune clean``.
    On a successful compile every cleared file is recreated, so dune
    re-syncs (content mismatch) on its next build; missing files are ignored
    (the common scratch-file case, where nothing was there to begin with).
    """
    stem = out.with_suffix("")
    if mode == "vos":
        # coqc -vos emits only the .vos (no .glob/.vok/.aux); leave dune's
        # .vo untouched so its digest-db stays in sync.
        stem.with_suffix(".vos").unlink(missing_ok=True)
        return
    for ext in _VO_FAMILY + (".glob",):
        stem.with_suffix(ext).unlink(missing_ok=True)
    # coqc's aux file is dot-prefixed: ``.<name>.aux``.
    (stem.parent / f".{stem.name}.aux").unlink(missing_ok=True)


def _run_dune_build(dune_root: Path, target: str, timeout: int) -> dict[str, Any]:
    """Run ``dune build <target>`` from *dune_root*.

    Returns a coqc-shaped result dict (``returncode`` / ``stdout`` /
    ``stderr`` / ``timed_out``) — dune emits coqc's own diagnostics
    verbatim, so the result feeds straight into :func:`_build_compile_result`
    — plus ``rule_missing``: True when dune has no rule for *target* (the
    file is not part of a stanza), the signal to fall back to coqc.
    """
    # "dune" on PATH — matches the existing ``dune {coq,rocq} top`` invocations
    # in server._run_dune_coq_top (dune is not a configurable binary here).
    result = _run_build_subprocess(
        ["dune", "build", target],
        str(dune_root),
        timeout,
    )
    result["rule_missing"] = _DUNE_RULE_MISSING_MARKER in result.get("stderr", "")
    return result


_DUNE_FILE_HEADER_RE = re.compile(r'File "([^"]+)"')


def _dune_error_targets_file(stderr: str, dune_root: Path, file_path: str) -> bool:
    """True iff dune's error output points at *file_path* (the requested file).

    ``dune build`` compiles the target's whole dependency closure, so a
    failure can be located in a *dependency* rather than the requested file.
    In that case the coqc-style ``File "..."`` header names the other file,
    and rendering a caret / ``error_positions`` against the requested file's
    source would mislead.  Returns False when no ``File`` header is present
    (a dune infrastructure error) so the caller falls back to raw output.
    """
    want = Path(file_path).resolve()
    for m in _DUNE_FILE_HEADER_RE.finditer(stderr):
        raw = m.group(1)
        p = Path(raw)
        if not p.is_absolute():
            p = dune_root / raw
        try:
            if p.resolve() == want:
                return True
        except OSError:
            continue
    return False


def _dune_dependency_error_result(
    stderr: str, include_warnings: bool
) -> dict[str, Any]:
    """Compile-error envelope for a ``dune build`` that failed in a dependency.

    Surfaces dune's own coqc-format diagnostics (which name the correct
    file) as ``error`` but omits ``error_positions`` — they carry no file
    field, so an agent would ``rocq_start`` at the wrong file's line.  The
    ``hint`` points at the dependency named in the error.
    """
    text = _truncate_error_text(stderr, include_warnings)
    return {
        "success": False,
        "reason": "compile_error",
        "error": text or "dune build failed in a dependency.",
        "hint": (
            "Compile the dependency named in the error first — dune builds "
            "the whole dependency closure, so the failure is upstream of the "
            "requested file."
        ),
    }


# ---------------------------------------------------------------------------
# Tool: rocq_compile_file (core implementation)
# ---------------------------------------------------------------------------


def run_compile_file(
    file: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
    keep_vo: bool = False,
    mode: str = "full",
    timing: bool = False,
) -> dict[str, Any]:
    """Core implementation of rocq_compile_file (testable without FastMCP Context).

    Compiles an existing .v file on disk.  Validates that the file is within
    the workspace, checks for forbidden commands, and returns structured errors.

    In a **dune project** (a ``dune-project`` ancestor is found and
    ``ROCQ_DUNE_BUILD`` is not ``0``), the compiled ``.vo``/``.vos`` is kept
    out of the source tree: full-mode in-stanza files build via
    ``dune build`` (artifacts under ``_build/default/…``), and everything
    else (scratch files, ``vos``/``timing`` modes) compiles with coqc but
    ``-o``-redirected into the same ``_build/default`` location.  In this
    mode *keep_vo* is a no-op — the artifact always lives in ``_build`` and
    the source tree is never written.  When ``dune build`` cannot build a
    file (not part of a stanza), the response carries a ``dune_build_warning``
    noting the coqc fallback.

    When *keep_vo* is True (outside a dune project), preserves the
    ``.vo``/``.vok``/``.vos`` outputs; diagnostic artifacts are still
    cleaned.  Default False preserves the "clean everything but the source"
    behavior.

    *mode* selects the coqc pass.  ``"full"`` (default) runs the normal
    compile.  ``"vos"`` adds ``-vos`` so coqc skips proof bodies, which
    is fast and still catches missing imports, statement type errors,
    holes, and notation conflicts — but does NOT catch tactic failures
    inside proof bodies.  Any other value is a validation error.

    When *timing* is True, coqc is invoked with ``-time`` and the result
    includes a ``timing`` field — see :func:`_build_timing_field`.
    Default False keeps the path zero-overhead.
    """
    if mode not in ("full", "vos"):
        return {
            "success": False,
            "reason": "validation",
            "error": f"Invalid mode {mode!r}: expected 'full' or 'vos'.",
        }
    try:
        file_path = _server._resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError) as e:
        return {"success": False, "reason": "validation", "error": str(e)}

    try:
        source = Path(file_path).read_text()
    except OSError as e:
        return {
            "success": False,
            "reason": "validation",
            "error": f"Cannot read file: {e}",
        }

    if len(source) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "reason": "validation",
            "error": f"File exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "reason": "validation", "error": forbidden}

    # In a dune project, keep compiled artifacts out of the source tree:
    # prefer `dune build` (writes to _build/default), and where that can't
    # be used, still redirect coqc's output there via `-o`.  Both
    # the dune target and the coqc `-o` output are computed relative to the
    # dune root, and the coqc fallback compiles with the dune root as its
    # workspace so its `-R _build/default/...` flags and the `-o` path agree
    # (coqc derives the module's logical name from the output path).
    ws = Path(workspace).resolve()
    dune_root = _server._find_dune_root(ws) if _server._DUNE_BUILD_ENABLED else None

    dune_build_warning: str | None = None
    coqc_workspace = workspace
    coqc_output: str | None = None

    if dune_root is not None:
        out = _dune_build_output(
            dune_root, file_path, ".vos" if mode == "vos" else ".vo"
        )
        if out is not None:
            # `dune build` is the blessed path but only knows in-stanza files
            # in full mode; it has no `.vos` target and no per-sentence
            # timing.  For those, skip straight to the coqc `-o` fallback.
            if mode == "full" and not timing:
                target = _dune_target_relpath(dune_root, file_path, ".vo")
                dres = _run_dune_build(dune_root, target, timeout)
                if not dres["rule_missing"]:
                    # dune owns the outcome — success, a real compile error
                    # (its stderr is coqc's own), or a timeout.  But a failure
                    # may be located in a *dependency* (dune builds the whole
                    # closure); a caret / error_positions rendered against the
                    # requested file's source would then be wrong, so surface
                    # dune's raw output for that case instead.
                    if (
                        dres["returncode"] != 0
                        and not dres["timed_out"]
                        and not _dune_error_targets_file(
                            dres["stderr"], dune_root, file_path
                        )
                    ):
                        return _dune_dependency_error_result(
                            dres["stderr"], include_warnings
                        )
                    return _build_compile_result(
                        dres,
                        source,
                        timeout,
                        include_warnings,
                        file_label=file,
                        clean_tmp_paths=False,
                    )
                # dune has no rule for this file (not part of a stanza).
                dune_build_warning = (
                    f"dune could not build {target!r} (the file is not part of "
                    "a dune stanza); compiled it directly with coqc into "
                    "_build/default instead."
                )
            try:
                out.parent.mkdir(parents=True, exist_ok=True)
                # dune's _build artifacts are read-only; clear any pre-existing
                # target so coqc's `-o` can write (see _clear_output_artifacts).
                _clear_output_artifacts(out, mode)
                coqc_output = str(out)
                coqc_workspace = str(dune_root)
            except OSError:
                # Cannot stage the _build dir — fall back to a plain
                # source-tree compile rather than failing outright.
                dune_build_warning = None

    result = _run_coqc_file(
        file_path,
        coqc_workspace,
        timeout,
        keep_vo=keep_vo,
        mode=mode,
        timing=timing,
        output=coqc_output,
    )

    timing_field: dict[str, Any] | None = None
    if timing:
        # Coqc 9.x emits ``-time`` output on stdout; parse there.  Walk
        # stderr too so we are robust to older or future coqc versions
        # that may route the lines differently.
        try:
            entries = _parse_timing_lines(result.get("stdout", ""), source)
            if not entries:
                entries = _parse_timing_lines(result.get("stderr", ""), source)
            timing_field = _build_timing_field(entries)
        except Exception:
            # Parser must never crash the response — coqc output shape may
            # drift across versions.  Fall back to an empty timing field.
            timing_field = _build_timing_field([])

    response = _build_compile_result(
        result,
        source,
        timeout,
        include_warnings,
        file_label=file,
        clean_tmp_paths=False,
        timing_field=timing_field,
    )
    if dune_build_warning:
        response["dune_build_warning"] = dune_build_warning
    return response


# ---------------------------------------------------------------------------
# Shared-defs verification helpers (Phase 2 fallback)
# ---------------------------------------------------------------------------


def _extract_source_range(
    lines: list[str],
    start_line: int,
    start_char: int,
    end_line: int,
    end_char: int,
) -> str:
    """Extract source text from lines using 0-based line/character positions."""
    if start_line < 0 or end_line >= len(lines) or start_line > end_line:
        raise IndexError(
            f"Invalid range: lines {start_line}-{end_line} "
            f"(file has {len(lines)} lines)"
        )
    if start_line == end_line:
        return lines[start_line][start_char:end_char]
    parts: list[str] = []
    parts.append(lines[start_line][start_char:])
    for i in range(start_line + 1, end_line):
        parts.append(lines[i])
    parts.append(lines[end_line][:end_char])
    return "\n".join(parts)


def _flatten_toc_elements(elements: list[Any]) -> list[Any]:
    """Flatten a tree of TocElements into a list, preserving order."""
    result: list[Any] = []
    for elem in elements:
        result.append(elem)
        if elem.children:
            result.extend(_flatten_toc_elements(elem.children))
    return result


def _deduplicate_toc_elements(all_elements: list[Any]) -> list[Any]:
    """Deduplicate and sort flattened toc elements.

    Deduplicates in two passes:
    1. By (name, start_line) — toc returns duplicate entries for
       constructors/fields of the same inductive/record.
    2. By full range tuple — mutual inductives share the same range.

    Returns elements sorted by source position.
    """
    # Pass 1: deduplicate by (name, start_line)
    seen: set[tuple[str | None, int]] = set()
    unique_elements: list[Any] = []
    for elem in all_elements:
        name = elem.name.v if elem.name else None
        start_line = elem.range.start.line if elem.range else -1
        key = (name, start_line)
        if key in seen:
            continue
        seen.add(key)
        unique_elements.append(elem)

    # Pass 2: deduplicate by range (mutual inductives share same range)
    seen_ranges: set[tuple[int, int, int, int]] = set()
    deduped_elements: list[Any] = []
    for elem in unique_elements:
        if elem.range:
            rng = (
                elem.range.start.line,
                elem.range.start.character,
                elem.range.end.line,
                elem.range.end.character,
            )
            if rng in seen_ranges:
                continue
            seen_ranges.add(rng)
        deduped_elements.append(elem)

    # Sort by source position
    deduped_elements.sort(
        key=lambda e: (
            e.range.start.line if e.range else 0,
            e.range.start.character if e.range else 0,
        )
    )

    return deduped_elements


def _toc_result_to_problem_structure(
    toc_result: Any, problem_statement: str
) -> ProblemStructure | None:
    """Pure transformation from pytanque toc output to a ``ProblemStructure``.

    Flattens / dedupes the toc tree, classifies each element, extracts
    source text per definition, and computes the preamble (everything
    before the first definition or theorem).  Returns ``None`` if the
    toc result is empty.

    Pure (no pet, no I/O) so it can be unit-tested in isolation and
    runs *outside* the pet lock.
    """
    if not toc_result:
        return None

    lines = problem_statement.splitlines()

    all_elements: list[Any] = []
    for _section_name, elements in toc_result:
        all_elements.extend(_flatten_toc_elements(elements))
    deduped_elements = _deduplicate_toc_elements(all_elements)

    definitions: list[DefinitionInfo] = []
    theorem_source: str = ""
    theorem_name: str | None = None
    first_def_line: int | None = None

    for elem in deduped_elements:
        name = elem.name.v if elem.name else None
        detail = elem.detail
        category = classify_toc_detail(detail)

        start_line = elem.range.start.line if elem.range else 0
        start_char = elem.range.start.character if elem.range else 0
        end_line = elem.range.end.line if elem.range else 0
        end_char = elem.range.end.character if elem.range else 0

        try:
            source_text = _extract_source_range(
                lines, start_line, start_char, end_line, end_char
            )
        except (IndexError, ValueError):
            continue

        if category == DefCategory.THEOREM:
            # toc range for theorem includes only the statement, not
            # Proof...Qed.  We need just the statement for the template.
            theorem_source = source_text
            theorem_name = name
        elif category in (DefCategory.SHARED_DEF, DefCategory.NOTATION):
            if first_def_line is None:
                first_def_line = start_line
            definitions.append(
                DefinitionInfo(
                    name=name,
                    detail=detail,
                    category=category,
                    source_text=source_text,
                    start_line=start_line,
                    end_line=end_line,
                )
            )

    # Extract preamble: everything before the first definition or theorem.
    # This captures Require Import / Open Scope lines that must be placed
    # outside Module M in Phase 2.
    first_significant_line = first_def_line
    if first_significant_line is None and theorem_source:
        # No shared defs -- use the theorem line as the boundary.
        for elem in deduped_elements:
            cat = classify_toc_detail(elem.detail)
            if cat == DefCategory.THEOREM and elem.range:
                first_significant_line = elem.range.start.line
                break
    if first_significant_line is not None and first_significant_line > 0:
        preamble_source = "\n".join(lines[:first_significant_line])
    else:
        preamble_source = ""

    has_shared = any(d.category == DefCategory.SHARED_DEF for d in definitions)

    return ProblemStructure(
        preamble_source=preamble_source,
        definitions=definitions,
        theorem_source=theorem_source,
        theorem_name=theorem_name,
        has_shared_defs=has_shared,
        full_source=problem_statement,
    )


async def _extract_problem_structure(
    problem_statement: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> ProblemStructure | dict[str, Any] | None:
    """Extract the structure of a problem statement using pytanque toc.

    Writes the problem_statement to a temp file, runs toc under the pet
    lock, releases the lock, then transforms the toc result into a
    ``ProblemStructure``.  The transformation is pure
    (:func:`_toc_result_to_problem_structure`) and runs outside the
    lock, keeping pet contention bounded.

    Three-way return:

    - ``ProblemStructure`` on success.
    - A failure dict (carrying ``pet_restarted: True`` when relevant)
      when pet died or memory was exhausted during toc.  The caller
      must propagate this dict back to the agent rather than falling
      through to Phase 3 — otherwise the ``pet_restarted`` signal is
      swallowed and the agent never learns to call ``rocq_diag``.
    - ``None`` when pet is unavailable or toc returned no data — Phase
      3 fallback applies.
    """
    _temp_files: list[str] = []

    def _do_toc(pet: Any) -> Any:
        ws = str(Path(workspace).resolve())
        _server._set_workspace_if_needed(pet, workspace, lifespan_state)
        with tempfile.NamedTemporaryFile(
            suffix=".v", mode="w", delete=False, dir=ws
        ) as f:
            f.write(problem_statement)
            f.flush()
            tmp_path = f.name
        _temp_files.append(tmp_path)
        try:
            from pytanque import PetanqueError
        except ImportError:
            PetanqueError = Exception  # type: ignore[assignment,misc]
        try:
            return pet.toc(tmp_path)
        except (PetanqueError, OSError):
            return None
        finally:
            _server._cleanup_coqc_artifacts(tmp_path)

    def _on_timeout() -> None:
        for p in _temp_files:
            _server._cleanup_coqc_artifacts(p)

    toc_result = await _server._run_with_pet(
        _do_toc,
        lifespan_state,
        "rocq_verify",
        on_timeout=_on_timeout,
    )

    # Distinguish three outcomes: pet-restart (must surface), other
    # pet-side failure (Phase 3 fallback is fine), and "toc returned
    # nothing" (also Phase 3).
    if isinstance(toc_result, dict):
        if toc_result.get("pet_restarted"):
            return toc_result
        return None
    if toc_result is None:
        return None
    return _toc_result_to_problem_structure(toc_result, problem_statement)


# ---------------------------------------------------------------------------
# Verdict-to-dict helper (shared by Phase 1 and Phase 2 of rocq_verify)
# ---------------------------------------------------------------------------


def _build_assumptions_result(
    verdict: str,
    details: dict,
    method: str,
) -> dict[str, Any]:
    """Map a parse_and_classify_assumptions verdict to a rocq_verify result dict.

    Args:
        verdict: One of "closed", "standard_only", "suspicious".
        details: The details dict from parse_and_classify_assumptions.
        method: Verification method label ("module_m", "shared_defs", or "direct").
    """
    note_suffix = ""
    if method == "shared_defs":
        note_suffix = (
            "Verified using shared-definitions template "
            "(definitions placed outside Module M for type compatibility). "
        )
    elif method == "direct":
        note_suffix = "Verified via direct compilation (no Module M sandbox). "

    if verdict == "closed":
        return {
            "success": True,
            "verification_method": method,
            "assumptions": [],
            **({"note": note_suffix.rstrip()} if note_suffix else {}),
        }
    elif verdict == "standard_only":
        note = (
            note_suffix + "Proof uses standard axioms (e.g., classical logic, Reals)."
        )
        return {
            "success": True,
            "verification_method": method,
            "assumptions": details["standard"],
            "note": note,
        }
    else:  # "suspicious"
        return {
            "success": False,
            "reason": "axiom_dependency",
            "verification_method": method,
            "error": (
                "Proof depends on unproved assumptions: "
                f"{', '.join(details['suspicious_names'])}"
            ),
            "assumptions": details["suspicious"],
            "hint": (
                "The proof uses Admitted, admit, or declares custom axioms. "
                "Provide a complete proof without these."
            ),
        }


# ---------------------------------------------------------------------------
# Phase 3: Direct verification (no Module M)
# ---------------------------------------------------------------------------


def _try_direct_verification(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str,
    timeout: int,
) -> dict[str, Any] | None:
    """Attempt Phase 3 direct verification (no Module M sandbox).

    Compiles the proof as-is, then verifies via Print Assumptions and
    Check type comparison against the problem statement.

    Returns:
        - A result dict (success=True/False) if Phase 3 can determine a verdict.
        - None if Phase 3 cannot apply (compilation failure, parse error, etc.),
          signaling the caller to fall back to the Phase 1 error.
    """
    # --- Build and compile proof source (Run A) ---
    try:
        proof_source = build_direct_verification_source(proof, problem_name)
    except ValueError as e:
        return {
            "success": False,
            "reason": "validation",
            "error": str(e),
            "verification_method": "direct",
        }

    t_start = time.monotonic()
    run_a_timeout = max(5, timeout // 2)
    result_a = _run_coqc(proof_source, workspace, run_a_timeout)

    if result_a["timed_out"] or result_a["returncode"] != 0:
        # Proof doesn't compile — Phase 3 can't apply
        return None

    # --- Parse Check type from proof (Run A stdout) ---
    proof_type = parse_check_type(result_a["stdout"], problem_name)
    if proof_type is None:
        return None

    # --- Parse Print Assumptions from proof (Run A stdout) ---
    verdict, details = parse_and_classify_assumptions(result_a["stdout"])
    if verdict == "suspicious":
        return _build_assumptions_result(verdict, details, "direct")

    # --- Build and compile problem source (Run B) ---
    try:
        problem_source = build_direct_type_check_source(problem_statement, problem_name)
    except ValueError:
        return None

    run_b_timeout = max(5, timeout - int(time.monotonic() - t_start))
    result_b = _run_coqc(problem_source, workspace, run_b_timeout)

    if result_b["timed_out"] or result_b["returncode"] != 0:
        # Problem doesn't compile — can't verify
        return None

    # --- Parse Check type from problem (Run B stdout) ---
    problem_type = parse_check_type(result_b["stdout"], problem_name)
    if problem_type is None:
        return None

    # --- Compare normalized types ---
    norm_proof = normalize_type_for_comparison(proof_type)
    norm_problem = normalize_type_for_comparison(problem_type)

    if norm_proof != norm_problem:
        return {
            "success": False,
            "reason": "type_mismatch",
            "error": (
                "Type mismatch: proof type differs from problem type. "
                f"Proof: {proof_type}  Expected: {problem_type}"
            ),
            "verification_method": "direct",
        }

    # Types match — return success with assumptions info
    return _build_assumptions_result(verdict, details, "direct")


# ---------------------------------------------------------------------------
# Tool: rocq_verify (core implementation)
# ---------------------------------------------------------------------------


def _remaining_timeout(t0: float, timeout: int, minimum: int = 10) -> int:
    """Compute remaining timeout budget from wall-clock start time.

    Returns at least *minimum* seconds so Phase 3 always gets a fair chance.
    """
    elapsed = time.monotonic() - t0
    return max(minimum, timeout - int(elapsed))


def _phase3_or_fallback(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str,
    timeout: int,
    fallback: dict[str, Any],
) -> dict[str, Any]:
    """Try Phase 3 direct verification; return *fallback* if Phase 3 cannot apply."""
    phase3_result = _try_direct_verification(
        proof, problem_name, problem_statement, workspace, timeout
    )
    if phase3_result is not None:
        return phase3_result
    return fallback


def _run_phase1_module_m(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str,
    timeout: int,
    include_warnings: bool,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Phase 1: Standard Module M sandbox (strongest security).

    Returns ``(result, phase1_failure)`` where:
    - *result* is non-None if Phase 1 produces a definitive answer
      (success, timeout+Phase3, or build error).
    - *phase1_failure* is the formatted error dict for Phase 2/3 fallback.
    """
    try:
        verification_source = build_verification_source(
            proof,
            problem_name,
            problem_statement,
        )
    except ValueError as e:
        return (
            {"success": False, "reason": "validation", "error": str(e)},
            {},
        )

    result = _run_coqc(verification_source, workspace, timeout)

    if result["timed_out"]:
        # Timeout in Module M (common for compute-heavy proofs).
        # Skip Phase 2 (also Module M) and try Phase 3 (no Module M).
        # Give Phase 3 the full original timeout — without Module M overhead
        # the proof may compile much faster.
        return (
            _phase3_or_fallback(
                proof,
                problem_name,
                problem_statement,
                workspace,
                timeout,
                fallback={
                    "success": False,
                    "reason": "timeout",
                    "error": f"Verification timed out after {timeout}s.",
                },
            ),
            {},
        )

    if result["returncode"] == 0:
        verdict, details = parse_and_classify_assumptions(result["stdout"])
        return (_build_assumptions_result(verdict, details, "module_m"), {})

    # Phase 1 failed — build failure dict for Phase 2/3 fallback
    phase1_stderr = result["stderr"]
    phase1_error = _format_error(
        phase1_stderr, verification_source, include_warnings=include_warnings
    )
    if not phase1_error:
        raw = phase1_stderr.strip()
        phase1_error = _TMP_PATH_RE.sub(
            f'"{_PROOF_FILE_LABEL}"',
            raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw,
        ).strip()
        if not include_warnings:
            phase1_error = _drop_warning_lines(phase1_error)
        if not phase1_error:
            phase1_error = f"coqc exited with code {result['returncode']}."
    phase1_failure: dict[str, Any] = {
        "success": False,
        "reason": "compile_error",
        "error": phase1_error,
        "hint": verification_hint(phase1_stderr),
    }
    return (None, phase1_failure)


async def _run_phase2_shared_defs(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str,
    timeout: int,
    lifespan_state: dict[str, Any] | None,
    phase1_failure: dict[str, Any],
    t0: float,
) -> dict[str, Any]:
    """Phase 2: Shared-defs Module M, with Phase 3 fallback.

    For problems with custom types (Inductive, Record, etc.), extracts
    shared definitions outside Module M.  Falls back to Phase 3 (direct
    compilation) if Phase 2 cannot apply or fails.
    """
    if lifespan_state is None:
        return _phase3_or_fallback(
            proof,
            problem_name,
            problem_statement,
            workspace,
            _remaining_timeout(t0, timeout),
            phase1_failure,
        )

    structure = await _extract_problem_structure(
        problem_statement, workspace, lifespan_state
    )

    # Pet died during toc — surface pet_restarted to the caller instead
    # of silently falling through to Phase 3.  Without this the
    # rocq_diag breadcrumb on the wrapper docstring is unreachable
    # through the Phase 2 path.
    if isinstance(structure, dict):
        return structure

    if structure is None:
        return _phase3_or_fallback(
            proof,
            problem_name,
            problem_statement,
            workspace,
            _remaining_timeout(t0, timeout),
            phase1_failure,
        )

    if not structure.has_shared_defs and not structure.preamble_source.strip():
        return _phase3_or_fallback(
            proof,
            problem_name,
            problem_statement,
            workspace,
            _remaining_timeout(t0, timeout),
            phase1_failure,
        )

    try:
        shared_source = build_shared_defs_verification_source(
            proof, problem_name, structure
        )
    except ValueError as e:
        return {"success": False, "reason": "validation", "error": str(e)}

    result2 = _run_coqc(shared_source, workspace, _remaining_timeout(t0, timeout))

    if result2["timed_out"]:
        # Give Phase 3 the full original timeout (no Module M overhead).
        return _phase3_or_fallback(
            proof,
            problem_name,
            problem_statement,
            workspace,
            timeout,
            fallback={
                "success": False,
                "reason": "timeout",
                "error": f"Verification (shared-defs) timed out after {timeout}s.",
            },
        )

    if result2["returncode"] != 0:
        return _phase3_or_fallback(
            proof,
            problem_name,
            problem_statement,
            workspace,
            timeout,
            phase1_failure,
        )

    verdict2, details2 = parse_and_classify_assumptions(result2["stdout"])
    return _build_assumptions_result(verdict2, details2, "shared_defs")


async def run_verify(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str,
    timeout: int,
    include_warnings: bool,
    lifespan_state: dict[str, Any] | None,
) -> dict[str, Any]:
    """Core implementation of rocq_verify (testable without FastMCP Context).

    Receives already-validated workspace and timeout.

    Verification phases:
      Phase 1 — Module M sandbox (strongest security).
      Phase 2 — Shared-defs Module M (for problems with custom types).
      Phase 3 — Direct compilation + Print Assumptions + Check type comparison
                (weaker, but handles compute-heavy proofs and Section/Variable).

    A wall-clock budget is tracked so the total time across all phases
    stays within approximately ``2 * timeout`` in the worst case.
    """
    try:
        _validate_rocq_identifier(problem_name)
    except ValueError as exc:
        return {"success": False, "reason": "validation", "error": str(exc)}

    if len(proof) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "reason": "validation",
            "error": f"Proof exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    if len(problem_statement) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "reason": "validation",
            "error": f"Problem statement exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    t0 = time.monotonic()

    # Phase 1: Standard Module M
    phase1_result, phase1_failure = _run_phase1_module_m(
        proof,
        problem_name,
        problem_statement,
        workspace,
        timeout,
        include_warnings,
    )
    if phase1_result is not None:
        return phase1_result

    # Phase 2: Shared-defs Module M (includes Phase 3 fallback)
    return await _run_phase2_shared_defs(
        proof,
        problem_name,
        problem_statement,
        workspace,
        timeout,
        lifespan_state,
        phase1_failure,
        t0,
    )


# ---------------------------------------------------------------------------
# Rocq sentence utilities
# ---------------------------------------------------------------------------


def _find_sentence_end(text: str) -> int | None:
    """Find the first Rocq sentence-terminating dot in *text*.

    A sentence-terminating dot is a ``.`` that is:
    - NOT inside a ``(* ... *)`` comment (arbitrarily nested), and
    - NOT inside a ``"..."`` string literal, and
    - followed by whitespace or end-of-string.

    Returns the index of the dot, or ``None`` if no terminating dot is found.
    """
    for idx, ch, in_comment, in_str in _rocq_scan(text):
        if ch == "." and not in_comment and not in_str:
            if idx + 1 >= len(text) or text[idx + 1] in (" ", "\t", "\n", "\r"):
                return idx
    return None


# Focus / bullet tokens are sentences in their own right but carry no
# terminating dot: a lone ``{`` / ``}`` brace, or a maximal run of one
# bullet character (``-``, ``+``, ``*``).  ``_find_sentence_end`` only
# recognizes dot-terminated sentences, so without special handling these
# tokens are silently dropped by the splitter (e.g. a body of just ``{``
# produces zero commands).
_LEADING_FOCUS_RE = re.compile(r"\{|\}|-+|\++|\*+")


def _leading_focus_token(text: str) -> tuple[str, int] | None:
    """Detect a leading focus/bullet token in *text*.

    Skips leading whitespace, then matches a lone ``{`` / ``}`` brace or
    a maximal run of a single bullet character (``-``/``+``/``*``).
    Returns ``(token, end_index)`` where *end_index* is the offset in the
    original *text* just past the token, or ``None`` when *text* does not
    begin with such a token.

    A ``{`` immediately followed by ``|`` is treated as record syntax
    (``{| ... |}``), not a focus brace, and yields ``None``.

    This detector is position-naive: it assumes *text* is the start of a
    proof-script sentence, where a leading ``-``/``+``/``*`` is a bullet.
    It does *not* distinguish a bullet from a term that happens to begin
    with one of those characters as a binary operator (e.g. a sentence
    starting ``* 2`` or ``- 3``).  That case does not arise for the
    tactic/bullet bodies this splitter is used on; callers feeding
    arbitrary term fragments should not rely on it.
    """
    offset = len(text) - len(text.lstrip())
    rest = text[offset:]
    m = _LEADING_FOCUS_RE.match(rest)
    if not m:
        return None
    tok = m.group(0)
    if tok == "{" and rest[1:2] == "|":
        return None
    return tok, offset + m.end()


def _is_focus_token(text: str) -> bool:
    """True if *text* is exactly one focus/bullet token.

    That is, ignoring surrounding whitespace, *text* is a lone ``{`` /
    ``}`` brace or a single maximal run of one bullet character.  Used to
    decide that a command must NOT have a terminating ``.`` appended:
    Rocq rejects ``-.`` and friends.  ``- reflexivity`` is *not* a focus
    token (it carries a trailing tactic) and does take a dot.
    """
    stripped = text.strip()
    focus = _leading_focus_token(stripped)
    return focus is not None and focus[1] == len(stripped)


def _split_rocq_sentences(source: str) -> list[str]:
    """Split Rocq source into individual sentences.

    Uses :func:`_find_sentence_end` repeatedly to split on
    sentence-terminating dots (handling comments and strings correctly).
    Focus and bullet tokens (``{``, ``}``, and runs of ``-``/``+``/``*``)
    are emitted as standalone sentences even though they carry no
    trailing dot — see :func:`_leading_focus_token`.  These tokens are
    emitted bare (without a dot): Rocq rejects a trailing ``.`` after a
    brace or bullet (e.g. ``-.`` is a syntax error).
    """
    sentences: list[str] = []
    remaining = source
    while remaining.strip():
        focus = _leading_focus_token(remaining)
        if focus is not None:
            token, end = focus
            sentences.append(token)
            remaining = remaining[end:]
            continue
        dot = _find_sentence_end(remaining)
        if dot is None:
            break
        sentence = remaining[: dot + 1].strip()
        if sentence:
            sentences.append(sentence)
        remaining = remaining[dot + 1 :]
    return sentences
