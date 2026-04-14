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


# ---------------------------------------------------------------------------
# coqc runner
# ---------------------------------------------------------------------------


def _run_coqc_process(file_path: str, workspace: Path, timeout: int) -> dict[str, Any]:
    """Run coqc on a .v file and return the result.

    Shared subprocess management for both :func:`_run_coqc` (temp files) and
    :func:`_run_coqc_file` (user files).  Handles timeout with graceful
    SIGTERM → SIGKILL escalation.

    Returns dict with keys:
        returncode: int
        stdout: str
        stderr: str
        timed_out: bool
    """
    try:
        proc = subprocess.Popen(
            [
                _server.ROCQ_COQC_BINARY,
                *_server._parse_project_flags(workspace),
                file_path,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=str(workspace),
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
        coqc_bin = _server.ROCQ_COQC_BINARY
        return {
            "returncode": -1,
            "stdout": "",
            "stderr": (
                f"{coqc_bin} not found or not executable: {e}"
                if isinstance(e, FileNotFoundError)
                else f"Failed to run {coqc_bin}: {e}"
            ),
            "timed_out": False,
        }


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


def _run_coqc_file(file_path: str, workspace: str, timeout: int) -> dict[str, Any]:
    """Run coqc on an existing .v file, return result dict.

    Unlike :func:`_run_coqc`, does NOT create a temp file — runs coqc
    directly on the given file.  Cleans up all compilation artifacts
    but preserves the source .v file.
    """
    ws = Path(workspace).resolve()
    try:
        return _run_coqc_process(file_path, ws, timeout)
    finally:
        # Clean compilation artifacts but preserve the source .v file
        base = Path(file_path).with_suffix("")
        for ext in _server._CLEANUP_EXTENSIONS:
            if ext == ".v":
                continue
            base.with_suffix(ext).unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Error formatting
# ---------------------------------------------------------------------------

_COQC_POS_RE = re.compile(
    r'File "[^"]*", line (\d+), characters (\d+)-(\d+):\s*\n((?:Error|Warning):.*?)(?=File "|$)',
    re.DOTALL,
)


def _parse_coqc_error_positions(stderr: str) -> list[dict[str, Any]]:
    """Parse coqc stderr into structured error positions.

    coqc uses 1-based lines, 0-based characters.
    Returns 0-based line numbers (for pytanque compatibility).
    """
    positions = []
    for m in _COQC_POS_RE.finditer(stderr):
        line_1based = int(m.group(1))
        char_start = int(m.group(2))
        char_end = int(m.group(3))
        message = m.group(4).strip()
        positions.append(
            {
                "line": line_1based - 1,
                "character": char_start,
                "end_character": char_end,
                "message": message[:500],
            }
        )
    return positions


# Regex to match coqc diagnostic blocks: File "path", line N, characters S-E:\n<body>
_COQC_DIAG_RE = re.compile(
    r'(File "([^"]*)", line (\d+), characters (\d+)-(\d+):\s*\n)(.*?)(?=File "|$)',
    re.DOTALL,
)

# Regex to extract Error/Warning kind from body
_KIND_RE = re.compile(r"^(Error|Warning)\b")

# Regex to replace tmp file paths with <proof>
_TMP_PATH_RE = re.compile(r'"[^"]*tmp[^"]*\.v"')


def _format_error(
    error_str: str,
    proof_str: str,
    *,
    include_warnings: bool = True,
    file_label: str = "<proof>",
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
# Shared post-compilation result builder
# ---------------------------------------------------------------------------


def _build_compile_result(
    result: dict[str, Any],
    source: str,
    timeout: int,
    include_warnings: bool,
    *,
    file_label: str = "<proof>",
    clean_tmp_paths: bool = True,
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
    """
    if result["timed_out"]:
        return {
            "success": False,
            "error": (
                f"Compilation timed out after {timeout}s. "
                "The proof may contain a diverging tactic."
            ),
        }

    if result["returncode"] == 0:
        return {"success": True, "output": result["stdout"][:2000]}

    error_text = _format_error(
        result["stderr"],
        source,
        include_warnings=include_warnings,
        file_label=file_label,
    )
    if not error_text:
        raw = result["stderr"].strip()
        fallback = raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw
        if clean_tmp_paths:
            fallback = _TMP_PATH_RE.sub(f'"{file_label}"', fallback).strip()
        else:
            fallback = fallback.strip()
        if not fallback:
            fallback = f"coqc exited with code {result['returncode']} (no stderr)."
        return {"success": False, "error": fallback}

    positions = _parse_coqc_error_positions(result["stderr"])
    result_dict: dict[str, Any] = {"success": False, "error": error_text}
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
            "error": f"Source exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "error": forbidden}

    result = _run_coqc(source, workspace, timeout)
    return _build_compile_result(result, source, timeout, include_warnings)


async def run_compile_with_state(
    source: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
    lifespan_state: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Async wrapper for run_compile.

    The compile MCP wrappers are async, so keep a matching async boundary here
    even before compile errors start consulting PET state.
    """
    del lifespan_state
    return run_compile(source, workspace, timeout, include_warnings)


# ---------------------------------------------------------------------------
# Tool: rocq_compile_file (core implementation)
# ---------------------------------------------------------------------------


def run_compile_file(
    file: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Core implementation of rocq_compile_file (testable without FastMCP Context).

    Compiles an existing .v file on disk.  Validates that the file is within
    the workspace, checks for forbidden commands, and returns structured errors.
    """
    try:
        file_path = _server._resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}

    try:
        source = Path(file_path).read_text()
    except OSError as e:
        return {"success": False, "error": f"Cannot read file: {e}"}

    if len(source) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "error": f"File exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "error": forbidden}

    result = _run_coqc_file(file_path, workspace, timeout)
    return _build_compile_result(
        result,
        source,
        timeout,
        include_warnings,
        file_label=file,
        clean_tmp_paths=False,
    )


async def run_compile_file_with_state(
    file: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
    lifespan_state: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Async wrapper for run_compile_file."""
    del lifespan_state
    return run_compile_file(file, workspace, timeout, include_warnings)


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


async def _extract_problem_structure(
    problem_statement: str,
    problem_name: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> ProblemStructure | None:
    """Extract the structure of a problem statement using pytanque toc.

    Writes the problem_statement to a temp file, runs toc, then parses the
    toc entries into a ProblemStructure with preamble, shared definitions,
    and the theorem source text.

    Returns None if pet is not available or toc fails.
    """
    lines = problem_statement.splitlines()
    _temp_files: list[str] = []

    def _do_toc(pet: Any) -> ProblemStructure | None:
        ws = str(Path(workspace).resolve())
        pet.set_workspace(debug=False, dir=ws)

        # Write problem statement to temp file
        with tempfile.NamedTemporaryFile(
            suffix=".v",
            mode="w",
            delete=False,
            dir=ws,
        ) as f:
            f.write(problem_statement)
            f.flush()
            tmp_path = f.name
        _temp_files.append(tmp_path)

        try:
            toc_result = pet.toc(tmp_path)
        except Exception:
            return None
        finally:
            _server._cleanup_coqc_artifacts(tmp_path)

        if not toc_result:
            return None

        # Flatten all toc elements from all sections
        all_elements: list[Any] = []
        for _section_name, elements in toc_result:
            all_elements.extend(_flatten_toc_elements(elements))

        deduped_elements = _deduplicate_toc_elements(all_elements)

        # Parse into DefinitionInfo objects
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

            # Extract source text for this element
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
            elif category in (
                DefCategory.SHARED_DEF,
                DefCategory.NOTATION,
            ):
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
            # No shared defs — use the theorem line as the boundary
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

    def _on_timeout() -> None:
        for p in _temp_files:
            _server._cleanup_coqc_artifacts(p)

    result = await _server._run_with_pet(
        _do_toc,
        lifespan_state,
        "Problem structure extraction",
        on_timeout=_on_timeout,
    )

    # _run_with_pet may return an error dict instead of a ProblemStructure
    if isinstance(result, dict):
        return None
    return result


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
            "verified": True,
            "verification_method": method,
            "assumptions": [],
            **({"note": note_suffix.rstrip()} if note_suffix else {}),
        }
    elif verdict == "standard_only":
        note = (
            note_suffix + "Proof uses standard axioms (e.g., classical logic, Reals)."
        )
        return {
            "verified": True,
            "verification_method": method,
            "assumptions": details["standard"],
            "note": note,
        }
    else:  # "suspicious"
        return {
            "verified": False,
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
        - A result dict (verified=True/False) if Phase 3 can determine a verdict.
        - None if Phase 3 cannot apply (compilation failure, parse error, etc.),
          signaling the caller to fall back to the Phase 1 error.
    """
    # --- Build and compile proof source (Run A) ---
    try:
        proof_source = build_direct_verification_source(proof, problem_name)
    except ValueError as e:
        return {"verified": False, "error": str(e), "verification_method": "direct"}

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
            "verified": False,
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
    t0: float,
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
        return ({"verified": False, "error": str(e)}, {})

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
                    "verified": False,
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
            '"<proof>"',
            raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw,
        ).strip()
        if not phase1_error:
            phase1_error = f"coqc exited with code {result['returncode']}."
    phase1_failure: dict[str, Any] = {
        "verified": False,
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
        problem_statement, problem_name, workspace, lifespan_state
    )

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
        return {"verified": False, "error": str(e)}

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
                "verified": False,
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
        return {"verified": False, "error": str(exc)}

    if len(proof) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "verified": False,
            "error": f"Proof exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    if len(problem_statement) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "verified": False,
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
        t0,
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


def _split_rocq_sentences(source: str) -> list[str]:
    """Split Rocq source into individual sentences.

    Uses :func:`_find_sentence_end` repeatedly to split on
    sentence-terminating dots (handling comments and strings correctly).
    """
    sentences: list[str] = []
    remaining = source
    while remaining.strip():
        dot = _find_sentence_end(remaining)
        if dot is None:
            break
        sentence = remaining[: dot + 1].strip()
        if sentence:
            sentences.append(sentence)
        remaining = remaining[dot + 1 :]
    return sentences
