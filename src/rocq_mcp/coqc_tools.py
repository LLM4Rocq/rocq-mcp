"""Rocq MCP Server — coqc-based tools (compile, verify, auto_solve).

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
    _THEOREM_DETAILS,
    build_verification_source,
    build_shared_defs_verification_source,
    classify_toc_detail,
    DefCategory,
    DefinitionInfo,
    parse_and_classify_assumptions,
    ProblemStructure,
    verification_hint,
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


def _run_coqc(source: str, workspace: str, timeout: int) -> dict[str, Any]:
    """Write source to temp file, run coqc, return result dict.

    Returns dict with keys:
        returncode: int
        stdout: str
        stderr: str
        timed_out: bool
    """
    ws = Path(workspace).resolve()
    with tempfile.NamedTemporaryFile(
        suffix=".v", mode="w", delete=False, dir=str(ws)
    ) as f:
        f.write(source)
        f.flush()
        tmp_path = f.name

    try:
        proc = subprocess.Popen(
            [_server.ROCQ_COQC_BINARY, *_server._parse_project_flags(ws), tmp_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=str(ws),
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
            # Kill the entire process group (coqc + any children)
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
    finally:
        _server._cleanup_coqc_artifacts(tmp_path)


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
    error_str: str, proof_str: str, *, include_warnings: bool = True
) -> str:
    """Reformat a raw coqc stderr string into LLM-friendly feedback.

    - Replaces the opaque tmp file path with ``<proof>``
    - Annotates the first Error-level diagnostic with the source line
      and a caret underline marking the exact character range
    - Suppresses pure-warning outputs (they don't prevent compilation)

    Args:
        error_str: Raw coqc stderr output.
        proof_str: The Rocq source that was compiled (for source annotations).
        include_warnings: If True (default), include deduplicated warnings
            that precede the first error.  If False, return only the error
            diagnostic itself — useful when warnings would drown the context.

    Falls back to the raw string (path-cleaned) when no structured
    location info is present (timeouts, workspace errors, etc.).
    """
    if not error_str:
        return error_str

    proof_lines = proof_str.splitlines()
    diagnostics = list(_COQC_DIAG_RE.finditer(error_str))

    if not diagnostics:
        cleaned = _TMP_PATH_RE.sub('"<proof>"', error_str).strip()
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
    # LLM context (math-comp can emit dozens of unique warnings).
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

        header = f"<proof>, line {line_1}, characters {char_start}-{char_end}:"

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

    result = _server._run_coqc(source, workspace, timeout)

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
    else:
        error_text = _format_error(
            result["stderr"], source, include_warnings=include_warnings
        )
        if not error_text:
            # No Error diagnostic parsed, but coqc still failed.
            # This can happen when voluminous warnings (e.g. math-comp
            # coercion ambiguity notices) precede the actual error.
            # Fall back to the tail of raw stderr so the error is visible.
            raw = result["stderr"].strip()
            fallback = raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw
            fallback = _TMP_PATH_RE.sub('"<proof>"', fallback).strip()
            if not fallback:
                fallback = f"coqc exited with code {result['returncode']} (no stderr)."
            return {"success": False, "error": fallback}
        positions = _parse_coqc_error_positions(result["stderr"])
        result_dict: dict[str, Any] = {"success": False, "error": error_text}
        if positions:
            result_dict["error_positions"] = positions
            result_dict["hint"] = (
                "Use rocq_step with file, line, and character parameters "
                "to start an interactive session at the error position."
            )
        return result_dict


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
        method: Verification method label (e.g. "module_m" or "shared_defs").
    """
    note_suffix = ""
    if method == "shared_defs":
        note_suffix = (
            "Verified using shared-definitions template "
            "(definitions placed outside Module M for type compatibility). "
        )

    if verdict == "closed":
        return {
            "verified": True,
            "verification_method": method,
            "assumptions": "Closed under the global context",
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
# Tool: rocq_verify (core implementation)
# ---------------------------------------------------------------------------


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
    """
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", problem_name):
        return {
            "verified": False,
            "error": (
                f"problem_name must be a valid Rocq identifier "
                f"(letters, digits, underscores, primes). Got: '{problem_name}'."
            ),
        }

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

    # --- Phase 1: Standard Module M. template ---
    try:
        verification_source = build_verification_source(
            proof,
            problem_name,
            problem_statement,
        )
    except ValueError as e:
        return {"verified": False, "error": str(e)}

    result = _server._run_coqc(verification_source, workspace, timeout)

    if result["timed_out"]:
        return {
            "verified": False,
            "error": f"Verification timed out after {timeout}s.",
        }

    if result["returncode"] == 0:
        # Phase 1 succeeded — parse Print Assumptions
        verdict, details = parse_and_classify_assumptions(result["stdout"])
        return _build_assumptions_result(verdict, details, "module_m")

    # --- Phase 1 failed: check if Phase 2 fallback is applicable ---
    phase1_stderr = result["stderr"]
    phase1_error = _format_error(
        phase1_stderr, verification_source, include_warnings=include_warnings
    )
    if not phase1_error:
        # No Error diagnostic parsed (e.g. voluminous warnings hid it).
        # Fall back to tail of raw stderr so the caller sees the actual error.
        raw = phase1_stderr.strip()
        phase1_error = _TMP_PATH_RE.sub(
            '"<proof>"',
            raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw,
        ).strip()
        if not phase1_error:
            phase1_error = f"coqc exited with code {result['returncode']}."
    phase1_hint = verification_hint(phase1_stderr)
    phase1_failure: dict[str, Any] = {
        "verified": False,
        "error": phase1_error,
        "hint": phase1_hint,
    }

    # Phase 2 condition: problem statement contains definition keywords
    # (Inductive, Record, etc.) or Require/Import statements that may cause
    # issues inside Module M.  Phase 2 is safe to attempt speculatively:
    # it either succeeds (correct) or fails (we return the Phase 1 error).

    # --- Phase 2: Shared-defs template via pytanque toc ---
    if lifespan_state is None:
        # No lifespan context (e.g., testing) — cannot use pytanque
        return phase1_failure

    structure = await _extract_problem_structure(
        problem_statement, problem_name, workspace, lifespan_state
    )

    if structure is None:
        # Could not extract structure — return Phase 1 error
        return phase1_failure

    if not structure.has_shared_defs and not structure.preamble_source.strip():
        # No shared defs and no preamble to extract — Phase 2 won't help
        return phase1_failure

    try:
        shared_source = build_shared_defs_verification_source(
            proof, problem_name, structure
        )
    except ValueError as e:
        return {"verified": False, "error": str(e)}

    result2 = _server._run_coqc(shared_source, workspace, timeout)

    if result2["timed_out"]:
        return {
            "verified": False,
            "error": f"Verification (shared-defs) timed out after {timeout}s.",
        }

    if result2["returncode"] != 0:
        # Phase 2 also failed — return the Phase 1 error (more informative)
        return phase1_failure

    # Phase 2 succeeded — parse Print Assumptions
    verdict2, details2 = parse_and_classify_assumptions(result2["stdout"])
    return _build_assumptions_result(verdict2, details2, "shared_defs")


# ---------------------------------------------------------------------------
# Tool: rocq_auto_solve (helpers + core implementation)
# ---------------------------------------------------------------------------

# Theorem-like keywords — derived from verify._THEOREM_DETAILS (single source of truth).
_THEOREM_KEYWORDS: tuple[str, ...] = tuple(sorted(_THEOREM_DETAILS))

_THEOREM_KW_RE = re.compile(
    r"^(" + "|".join(re.escape(k) for k in _THEOREM_KEYWORDS) + r")\s+",
    re.MULTILINE,
)

# Tactics tried in order from cheapest to most expensive.
_AUTO_SOLVE_TACTICS: list[str] = [
    "trivial",
    "reflexivity",
    "assumption",
    "exact I",
    "auto",
    "eauto",
    "tauto",
    "intuition",
    "lia",
    "lra",
    "nia",
    "nra",
    "ring",
    "field",
    "decide equality",
    "firstorder",
]

# Extra imports needed to make decision procedures available.
_AUTO_SOLVE_IMPORTS = "From Stdlib Require Import Lia Lra Ring Field.\n"


def _rocq_comment_ranges(text: str) -> list[tuple[int, int]]:
    """Return ``(start, end)`` ranges for ``(* ... *)`` comments in *text*.

    Handles nested comments and skips ``(*``/``*)`` inside string literals
    (delimited by ``"``).  The returned ranges cover only comments, not
    strings; strings are tracked solely to avoid false positives.
    """
    ranges: list[tuple[int, int]] = []
    comment_start: int | None = None
    prev_in_comment = False
    closing_end: int | None = None
    depth = 0
    for idx, ch, in_comment, _in_str in _rocq_scan(text):
        if in_comment and not prev_in_comment:
            comment_start = idx
            closing_end = None
            depth = 1
        elif not in_comment and prev_in_comment and comment_start is not None:
            # The '*' of '*)' is yielded with in_comment=True, and the
            # scanner skips past both chars (i += 2).  So idx here is the
            # first character AFTER the closing ')'.
            ranges.append((comment_start, idx))
            comment_start = None
            closing_end = None
            depth = 0
        elif in_comment and prev_in_comment and not _in_str:
            # Track nesting depth for nested (* ... *) inside a comment.
            # Skip depth changes for (* / *) inside string literals within
            # a comment, matching the scanner's behavior.
            if ch == "(" and idx + 1 < len(text) and text[idx + 1] == "*":
                depth += 1
            elif ch == "*" and idx + 1 < len(text) and text[idx + 1] == ")":
                depth -= 1
        # Track position of closing *) for end-of-text handling, but ONLY
        # when the *) actually closes the outermost comment (depth -> 0).
        # For nested comments, an inner *) reduces depth but should not
        # set closing_end since the outer comment is still open.
        if (
            in_comment
            and not _in_str
            and ch == "*"
            and idx + 1 < len(text)
            and text[idx + 1] == ")"
            and depth == 0
        ):
            closing_end = idx + 2
        prev_in_comment = in_comment
    # Comment that closes at the very end of text — no subsequent char
    # triggers the transition above.
    if prev_in_comment and comment_start is not None and closing_end is not None:
        ranges.append((comment_start, closing_end))
    return ranges


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


def _parse_last_theorem(source: str) -> tuple[str, str, str, str] | None:
    """Parse *source* and return info about the LAST theorem declaration.

    Returns ``(preamble, keyword, name, full_statement)`` where:
    - *preamble* is everything before the theorem keyword
    - *keyword* is the Rocq keyword (``Theorem``, ``Lemma``, ...)
    - *name* is the theorem identifier
    - *full_statement* is the complete declaration from keyword to the
      terminating ``.`` (inclusive), e.g.
      ``Theorem foo : forall n, n = n.``

    The function handles:
    - Multi-line statements (``Theorem foo :\\n  forall n, ...``)
    - ``Proof. ... Admitted.`` / ``Proof. Admitted.`` / bare ``Admitted.``
      after the statement -- these are stripped from the returned values so
      the caller can substitute its own proof.

    Returns ``None`` if no theorem-like declaration is found.
    """
    # Find all theorem-keyword positions.  We want the LAST one.
    matches = list(_THEOREM_KW_RE.finditer(source))
    if not matches:
        return None

    # Build list of comment ranges to filter out matches inside (* ... *)
    comment_ranges = _rocq_comment_ranges(source)

    def _in_comment(pos: int) -> bool:
        return any(start <= pos < end for start, end in comment_ranges)

    # Filter out matches that fall inside comments
    matches = [m for m in matches if not _in_comment(m.start())]
    if not matches:
        return None

    m = matches[-1]

    preamble = source[: m.start()]
    rest = source[m.start() :]

    # The statement ends at the first ``.`` that is NOT inside a comment
    # and is followed by whitespace / end-of-string.
    dot_pos = _find_sentence_end(rest)

    if dot_pos is None:
        return None

    full_statement = rest[: dot_pos + 1]

    # Extract keyword and name from the statement.
    header_match = re.match(
        r"("
        + "|".join(re.escape(k) for k in _THEOREM_KEYWORDS)
        + r")\s+([A-Za-z_][A-Za-z0-9_']*)",
        full_statement,
    )
    if not header_match:
        return None
    keyword = header_match.group(1)
    name = header_match.group(2)

    return preamble, keyword, name, full_statement


def _build_auto_solve_source(
    preamble: str,
    full_statement: str,
    preamble_tactics: str,
    tactics: list[str],
) -> str:
    """Build a .v source that tries all *tactics* via ``first [...]``."""
    parts: list[str] = []

    # Original preamble (imports, definitions, opens, notations).
    parts.append(preamble.rstrip())

    # Always add decision procedure imports (duplicate imports are harmless).
    parts.append("")
    parts.append(_AUTO_SOLVE_IMPORTS.rstrip())

    # The theorem statement.
    parts.append("")
    parts.append(full_statement)
    parts.append("Proof.")

    # Always intros first (safe no-op if nothing to introduce),
    # then user-provided preamble tactics if any.
    if preamble_tactics:
        parts.append(f"  intros. {preamble_tactics}")
    else:
        parts.append("  intros.")

    # The ``first`` combinator with all tactics.
    # Each tactic is wrapped in ``solve [...]`` so that ``first``
    # only commits when the tactic fully closes the goal.
    alternatives = " | ".join(f"solve [{t}]" for t in tactics)
    parts.append(f"  first [ {alternatives} ].")
    parts.append("Qed.")

    return "\n".join(parts) + "\n"


def _build_single_tactic_source(
    preamble: str,
    full_statement: str,
    preamble_tactics: str,
    tactic: str,
) -> str:
    """Build a .v source that tries a single *tactic*."""
    parts: list[str] = []

    parts.append(preamble.rstrip())

    parts.append("")
    parts.append(_AUTO_SOLVE_IMPORTS.rstrip())

    parts.append("")
    parts.append(full_statement)
    parts.append("Proof.")

    if preamble_tactics:
        parts.append(f"  intros. {preamble_tactics}")
    else:
        parts.append("  intros.")

    parts.append(f"  {tactic}.")
    parts.append("Qed.")

    return "\n".join(parts) + "\n"


def run_auto_solve(
    problem: str,
    preamble_tactics: str,
    workspace: str,
    timeout: int,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Core implementation of rocq_auto_solve (testable without FastMCP Context).

    Receives already-validated workspace and timeout.
    """
    start_time = time.monotonic()

    if len(problem) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "solved": False,
            "error": f"Problem exceeds maximum size ({_server.ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    forbidden = _check_forbidden_commands(problem)
    if forbidden:
        return {"solved": False, "error": forbidden}

    if preamble_tactics:
        forbidden = _check_forbidden_commands(preamble_tactics)
        if forbidden:
            return {"solved": False, "error": forbidden}

    # --- Parse the problem file ---
    parsed = _parse_last_theorem(problem)
    if parsed is None:
        return {
            "solved": False,
            "error": (
                "Could not find a Theorem/Lemma/Proposition/Corollary/"
                "Example/Fact/Remark declaration in the problem."
            ),
        }
    preamble, keyword, name, full_statement = parsed

    # Normalise preamble_tactics: ensure it ends with "." if non-empty.
    pt = preamble_tactics.strip()
    if pt and not pt.endswith("."):
        pt += "."

    # --- Phase 1: Try all tactics via ``first [...]`` ---
    combined_source = _build_auto_solve_source(
        preamble, full_statement, pt, _AUTO_SOLVE_TACTICS
    )

    result = _server._run_coqc(combined_source, workspace, timeout)

    if result["timed_out"]:
        return {
            "solved": False,
            "error": f"Timed out after {timeout}s trying automation tactics.",
        }

    if result["returncode"] != 0:
        details = _format_error(
            result["stderr"],
            combined_source,
            include_warnings=include_warnings,
        )
        if not details:
            # _format_error found no Error diagnostics (e.g. voluminous
            # warnings hid the error).  Fall back to tail of raw stderr.
            raw = result["stderr"].strip()
            details = _TMP_PATH_RE.sub(
                '"<proof>"',
                raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw,
            ).strip()
        return {
            "solved": False,
            "error": "None of the standard automation tactics succeeded.",
            "details": details or f"coqc exited with code {result['returncode']}.",
        }

    # --- Phase 2: Identify which specific tactic worked ---
    # Use a shorter timeout per individual tactic since we already know
    # the combined run succeeded within *timeout*.
    per_tactic_timeout = max(timeout // 3, 10)

    for tactic in _AUTO_SOLVE_TACTICS:
        # Check if the overall timeout has been exceeded
        if time.monotonic() - start_time > timeout:
            # Timeout: we know it's solvable but can't identify which tactic
            break

        single_source = _build_single_tactic_source(
            preamble, full_statement, pt, tactic
        )
        single_result = _server._run_coqc(single_source, workspace, per_tactic_timeout)

        if single_result["returncode"] == 0:
            # Build the human-readable proof text.
            proof_lines = ["Proof."]
            if pt:
                proof_lines.append(f"  intros. {pt}")
            else:
                proof_lines.append("  intros.")
            proof_lines.append(f"  {tactic}.")
            proof_lines.append("Qed.")
            proof_text = "\n".join(proof_lines)

            return {
                "solved": True,
                "tactic": tactic,
                "proof": proof_text,
            }

    # Edge case: the ``first [...]`` succeeded but no single tactic did
    # (shouldn't happen in theory, but handle gracefully).
    proof_lines = ["Proof."]
    if pt:
        proof_lines.append(f"  intros. {pt}")
    else:
        proof_lines.append("  intros.")
    alternatives = " | ".join(f"solve [{t}]" for t in _AUTO_SOLVE_TACTICS)
    proof_lines.append(f"  first [ {alternatives} ].")
    proof_lines.append("Qed.")
    proof_text = "\n".join(proof_lines)

    return {
        "solved": True,
        "tactic": "first [...]",
        "proof": proof_text,
    }
