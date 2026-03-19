"""Rocq MCP Server — tools for Rocq/Coq proof development."""

from __future__ import annotations

import asyncio
import os
import re
import signal
import subprocess
import tempfile
import threading
import time
from pathlib import Path
from typing import Any, Callable

from fastmcp import FastMCP, Context
from fastmcp.server.lifespan import lifespan

from rocq_mcp.verify import (
    _check_forbidden_commands,
    _rocq_scan,
    _SHARED_DEF_DETAILS,
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
_MAX_ERROR_LENGTH: int = 4000
_MAX_FORMAT_WARNINGS: int = 3

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
    }
    try:
        yield state
    finally:
        client = state.get("pet_client")
        if client:
            _kill_pet(client)


mcp = FastMCP("rocq-mcp", lifespan=app_lifespan)

# ---------------------------------------------------------------------------
# Helpers
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
            [ROCQ_COQC_BINARY, "-Q", str(ws), "Test", tmp_path],
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
            stdout, stderr = proc.communicate()
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
                f"{ROCQ_COQC_BINARY} not found or not executable: {e}"
                if isinstance(e, FileNotFoundError)
                else f"Failed to run {ROCQ_COQC_BINARY}: {e}"
            ),
            "timed_out": False,
        }
    finally:
        _cleanup_coqc_artifacts(tmp_path)


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
# Tool: rocq_compile
# ---------------------------------------------------------------------------


@mcp.tool
def rocq_compile(
    source: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Compile Rocq source code and return structured errors.

    Use this as the first step for any proof. 81% of proofs succeed
    via direct compilation. Pass the complete .v file content.

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

    # Input validation
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    if len(source) > ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "error": f"Source exceeds maximum size ({ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "error": forbidden}

    result = _run_coqc(source, workspace, timeout)

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
    if start_line == end_line:
        return lines[start_line][start_char:end_char]
    parts: list[str] = []
    parts.append(lines[start_line][start_char:])
    for i in range(start_line + 1, end_line):
        parts.append(lines[i])
    parts.append(lines[end_line][:end_char])
    return "\n".join(parts)


# Definition keywords for Phase 2 gate check.  Based on _SHARED_DEF_DETAILS
# from verify.py, plus "Let" which is a valid definition keyword in problem
# statements even though it is not a shared-def detail for toc classification.
_DEF_KEYWORDS: set[str] = _SHARED_DEF_DETAILS | {"Let"}

_DEF_KEYWORD_RE = re.compile(
    r"\b("
    + "|".join(re.escape(k) for k in sorted(_DEF_KEYWORDS, key=len, reverse=True))
    + r")\b"
)


def _has_definition_keywords(text: str) -> bool:
    """Quick regex check for Inductive/Record/Definition/Fixpoint etc. in text."""
    return bool(_DEF_KEYWORD_RE.search(text))


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
    lines = problem_statement.split("\n")
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
            _cleanup_coqc_artifacts(tmp_path)

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

        # Extract preamble: everything before the first reported definition
        if first_def_line is not None and first_def_line > 0:
            preamble_source = "\n".join(lines[:first_def_line])
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
            _cleanup_coqc_artifacts(p)

    result = await _run_with_pet(
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

    Uses conservative Module M. verification: wraps the proof in a module,
    then checks that applying M.theorem_name proves the original statement.
    Also runs Print Assumptions to detect axioms or admitted goals.

    This catches:
    - Type redefinition cheating (e.g., redefining nat as bool)
    - Admitted/Abort hidden in the proof
    - Custom axiom declarations (e.g., Axiom cheat : False)
    - Proofs that compile but prove a different statement

    Standard mathematical axioms (classical logic, functional extensionality,
    axiom of choice, Reals axiomatization) are accepted as valid.

    Always run this after rocq_compile succeeds.

    When the standard Module M. template fails due to type unification errors
    (common when the problem defines local types/functions), automatically
    falls back to a shared-definitions template that places type definitions
    outside Module M for compatibility.

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

    # Input validation
    err = _validate_workspace(workspace)
    if err:
        return {"verified": False, "error": err}

    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", problem_name):
        return {
            "verified": False,
            "error": (
                f"problem_name must be a valid Rocq identifier "
                f"(letters, digits, underscores, primes). Got: '{problem_name}'."
            ),
        }

    if len(proof) > ROCQ_MAX_SOURCE_SIZE:
        return {
            "verified": False,
            "error": f"Proof exceeds maximum size ({ROCQ_MAX_SOURCE_SIZE} bytes).",
        }

    if len(problem_statement) > ROCQ_MAX_SOURCE_SIZE:
        return {
            "verified": False,
            "error": f"Problem statement exceeds maximum size ({ROCQ_MAX_SOURCE_SIZE} bytes).",
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

    result = _run_coqc(verification_source, workspace, timeout)

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
        phase1_stderr, proof, include_warnings=include_warnings
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
    # (Inductive, Record, etc.) that may cause type incompatibility across
    # the Module M boundary.  Phase 2 is safe to attempt speculatively:
    # it either succeeds (correct) or fails (we return the Phase 1 error).
    if not _has_definition_keywords(problem_statement):
        return phase1_failure

    # --- Phase 2: Shared-defs template via pytanque toc ---
    lifespan_state = ctx.lifespan_context if ctx else None
    if lifespan_state is None:
        # No lifespan context (e.g., testing) — cannot use pytanque
        return phase1_failure

    structure = await _extract_problem_structure(
        problem_statement, problem_name, workspace, lifespan_state
    )

    if structure is None or not structure.has_shared_defs:
        # Could not extract structure or no shared defs found — return Phase 1 error
        return phase1_failure

    try:
        shared_source = build_shared_defs_verification_source(
            proof, problem_name, structure
        )
    except ValueError as e:
        return {"verified": False, "error": str(e)}

    result2 = _run_coqc(shared_source, workspace, timeout)

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
# Tool: rocq_auto_solve
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


@mcp.tool
def rocq_auto_solve(
    problem: str,
    preamble_tactics: str = "",
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Try to prove a theorem using standard automation tactics.

    Attempts tactics in order: trivial, reflexivity, assumption, exact I,
    auto, eauto, tauto, intuition, lia, lra, nia, nra, ring, field,
    decide, firstorder.

    Optionally run preamble tactics first (e.g., "intros." or "intros. simpl.").

    Does NOT require pytanque — uses coqc directly.

    Args:
        problem: Complete .v file content with the theorem to prove
                 (the theorem should end with Admitted. or Abort. or
                  have Proof. Admitted.).
        preamble_tactics: Optional tactics to run before automation
                         (e.g., "intros." or "intros. simpl.").
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
        timeout: Timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
        include_warnings: If True (default), include deduplicated warnings
            before the error in the output.  Set to False for compact errors.
    """
    workspace = workspace or ROCQ_WORKSPACE
    timeout = timeout if timeout is not None and timeout > 0 else ROCQ_COQC_TIMEOUT
    start_time = time.monotonic()

    # --- Input validation ---
    err = _validate_workspace(workspace)
    if err:
        return {"solved": False, "error": err}

    if len(problem) > ROCQ_MAX_SOURCE_SIZE:
        return {
            "solved": False,
            "error": f"Problem exceeds maximum size ({ROCQ_MAX_SOURCE_SIZE} bytes).",
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

    result = _run_coqc(combined_source, workspace, timeout)

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
        single_result = _run_coqc(single_source, workspace, per_tactic_timeout)

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


# ---------------------------------------------------------------------------
# Pet subprocess management (Phase 1+)
# ---------------------------------------------------------------------------

# Global lock for ALL pytanque operations. Pytanque's stdio pipe is
# single-duplex -- concurrent reads/writes corrupt JSON-RPC framing.
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
            # Clean up dead client
            _try_close_pet(pet)
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
    except (OSError, ChildProcessError):
        # Process already dead or group doesn't exist
        pass
    # Close pipe file descriptors
    _try_close_pet(pet)


def _try_close_pet(pet: Any) -> None:
    """Close pytanque's pipe file descriptors without killing."""
    if pet.process is None:
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
    """
    pet = lifespan_state.get("pet_client")
    if pet:
        _kill_pet(pet)
    lifespan_state["pet_client"] = None


# ---------------------------------------------------------------------------
# Tool: rocq_query (Phase 1)
# ---------------------------------------------------------------------------


_MAX_QUERY_OUTPUT = 8000


async def run_query(
    command: str,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> dict[str, Any]:
    """Core implementation of rocq_query (testable without FastMCP Context)."""
    forbidden = _check_forbidden_commands(command)
    if forbidden:
        return {"success": False, "error": forbidden}
    forbidden = _check_forbidden_commands(preamble)
    if forbidden:
        return {"success": False, "error": forbidden}

    _temp_files: list[str] = []

    def _do_query(pet: Any) -> dict[str, Any]:
        ws = str(Path(workspace).resolve())
        pet.set_workspace(debug=False, dir=ws)

        preamble_text = preamble.strip()
        dummy_source = (
            f"{preamble_text}\n" "Lemma _rocq_mcp_dummy : True. Proof. exact I. Qed.\n"
        )
        with tempfile.NamedTemporaryFile(
            suffix=".v",
            mode="w",
            delete=False,
            dir=str(ws),
        ) as f:
            f.write(dummy_source)
            f.flush()
            dummy_path = Path(f.name)
        _temp_files.append(str(dummy_path))
        try:
            state = pet.start(str(dummy_path), "_rocq_mcp_dummy")

            cmd = command.strip()
            if not cmd.endswith("."):
                cmd += "."
            state = pet.run(state, cmd)
            feedback = state.feedback or []

            output = "\n".join(msg for _, msg in feedback)
            if len(output) > _MAX_QUERY_OUTPUT:
                output = (
                    output[:_MAX_QUERY_OUTPUT]
                    + f"\n... (truncated, {len(output)} total chars)"
                )
            return {"success": True, "output": output or "(no output)"}
        finally:
            _cleanup_coqc_artifacts(str(dummy_path))

    def _on_timeout() -> None:
        for p in _temp_files:
            _cleanup_coqc_artifacts(p)

    return await _run_with_pet(
        _do_query,
        lifespan_state,
        "Query",
        on_timeout=_on_timeout,
    )


@mcp.tool
async def rocq_query(
    command: str,
    preamble: str = "",
    workspace: str = "",
    ctx: Context = None,
) -> dict[str, Any]:
    """Run a Rocq query (Search, Check, Print, About) and return results.

    The query does NOT modify any proof state.

    Examples:
      command="Search (nat -> nat -> nat)."
      command="Check Nat.add."
      command="Print Assumptions my_lemma."
      command="About plus."

    Args:
        command: The Rocq query command to execute.
        preamble: Optional import lines needed for the query context
                  (e.g., "Require Import Reals.\\nOpen Scope R_scope.").
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
    """
    return await run_query(
        command=command,
        preamble=preamble,
        workspace=workspace or ROCQ_WORKSPACE,
        lifespan_state=ctx.lifespan_context,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_toc (Phase 1)
# ---------------------------------------------------------------------------


def _format_toc_elements(elements: list[Any], indent: int = 1) -> list[str]:
    """Recursively format TocElement tree into indented text lines."""
    lines: list[str] = []
    prefix = "  " * indent
    for elem in elements:
        name = elem.name.v if elem.name else None
        if name is None:
            # Skip unnamed elements but still recurse into children
            if elem.children:
                lines.extend(_format_toc_elements(elem.children, indent))
            continue
        line_no = elem.range.start.line if elem.range else "?"
        lines.append(f"{prefix}{elem.detail} {name} (line {line_no})")
        if elem.children:
            lines.extend(_format_toc_elements(elem.children, indent + 1))
    return lines


async def run_toc(
    file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> dict[str, Any]:
    """Core implementation of rocq_toc (testable without FastMCP Context)."""
    # Path traversal check (before entering thread)
    file_path = str((Path(workspace).resolve() / file).resolve())
    ws_resolved = str(Path(workspace).resolve())
    if not file_path.startswith(ws_resolved + os.sep) and file_path != ws_resolved:
        return {"success": False, "error": "File path must be within workspace."}

    def _do_toc(pet: Any) -> dict[str, Any]:
        ws = str(Path(workspace).resolve())
        pet.set_workspace(debug=False, dir=ws)
        toc_result = pet.toc(file_path)

        # Format the result as readable text
        lines: list[str] = [f"File: {file}"]
        if toc_result:
            for _section_name, elements in toc_result:
                lines.extend(_format_toc_elements(elements))

        output = "\n".join(lines)
        if len(output) > _MAX_QUERY_OUTPUT:
            output = (
                output[:_MAX_QUERY_OUTPUT]
                + f"\n... (truncated, {len(output)} total chars)"
            )
        return {"success": True, "output": output or f"File: {file}\n  (empty)"}

    return await _run_with_pet(
        _do_toc,
        lifespan_state,
        "TOC request",
    )


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

    Does NOT require an active rocq_step session.

    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
    """
    workspace = workspace or ROCQ_WORKSPACE

    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}

    return await run_toc(
        file=file,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_notations (Phase 1)
# ---------------------------------------------------------------------------


async def run_notations(
    statement: str,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> dict[str, Any]:
    """Core implementation of rocq_notations (testable without FastMCP Context)."""
    forbidden = _check_forbidden_commands(statement)
    if forbidden:
        return {"success": False, "error": forbidden}
    forbidden = _check_forbidden_commands(preamble)
    if forbidden:
        return {"success": False, "error": forbidden}

    _temp_files: list[str] = []

    def _do_notations(pet: Any) -> dict[str, Any]:
        ws = str(Path(workspace).resolve())
        pet.set_workspace(debug=False, dir=ws)

        preamble_text = preamble.strip()
        dummy_source = (
            f"{preamble_text}\n" "Lemma _rocq_mcp_dummy : True. Proof. exact I. Qed.\n"
        )
        with tempfile.NamedTemporaryFile(
            suffix=".v",
            mode="w",
            delete=False,
            dir=str(ws),
        ) as f:
            f.write(dummy_source)
            f.flush()
            dummy_path = Path(f.name)
        _temp_files.append(str(dummy_path))
        try:
            state = pet.start(str(dummy_path), "_rocq_mcp_dummy")

            # Construct the full Lemma declaration for pytanque
            full_statement = f"Lemma _rocq_mcp_notation_check : {statement}."
            notations = pet.list_notations_in_statement(state, full_statement)

            if not notations:
                return {
                    "success": True,
                    "output": "No notations found in statement.",
                }

            lines = ["Notations found in statement:"]
            for ni in notations:
                scope_str = f"  (scope: {ni.scope})" if ni.scope else ""
                # Use path or secpath for module provenance
                module = ni.path or ni.secpath or "unknown"
                lines.append(f'  "{ni.notation}"  ->  {module}{scope_str}')

            output = "\n".join(lines)
            if len(output) > _MAX_QUERY_OUTPUT:
                output = (
                    output[:_MAX_QUERY_OUTPUT]
                    + f"\n... (truncated, {len(output)} total chars)"
                )
            return {"success": True, "output": output}
        finally:
            _cleanup_coqc_artifacts(str(dummy_path))

    def _on_timeout() -> None:
        for p in _temp_files:
            _cleanup_coqc_artifacts(p)

    return await _run_with_pet(
        _do_notations,
        lifespan_state,
        "Notation query",
        on_timeout=_on_timeout,
    )


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

    return await run_notations(
        statement=statement,
        preamble=preamble,
        workspace=workspace,
        lifespan_state=ctx.lifespan_context,
    )


# ---------------------------------------------------------------------------
# Goal formatting helper (shared by run_step and run_step_multi)
# ---------------------------------------------------------------------------


def _format_goals(goals_list: list[Any]) -> str:
    """Format goal objects into readable text with hypotheses."""
    parts = []
    for i, g in enumerate(goals_list):
        hyps = "\n".join(
            f"{', '.join(h.names)}" f"{' := ' + h.def_ if h.def_ else ''}" f" : {h.ty}"
            for h in g.hyps
        )
        pp = f"{hyps}\n|-{g.ty}"
        if len(goals_list) > 1:
            parts.append(f"Goal {i + 1}:\n{pp}")
        else:
            parts.append(pp)
    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Two-tier timeout helpers
# ---------------------------------------------------------------------------

_PET_TIMEOUT_GRACE: float = float(os.environ.get("ROCQ_PET_TIMEOUT_GRACE", "10"))


def _is_timeout_eligible(tac: str) -> bool:
    """Check if a tactic can be wrapped with Rocq's Timeout command.

    Timeout N can only wrap commands that end with '.' and do NOT
    start with bullet markers: '-', '+', '*'.
    """
    stripped = tac.strip()
    if not stripped.endswith("."):
        return False
    return not stripped.startswith(("-", "+", "*"))


def _compute_hard_timeout(soft_timeout: float) -> float:
    """Compute the process-level hard timeout from the Rocq-level soft timeout."""
    return soft_timeout + _PET_TIMEOUT_GRACE


# ---------------------------------------------------------------------------
# Tool: rocq_step (Phase 2)
# ---------------------------------------------------------------------------

# Session state (single-client stdio model)
_session: dict[str, Any] = {
    "state": None,
    "file": None,
    "theorem": None,
    "history": [],
}

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


async def _run_with_pet(
    fn: Callable[[Any], Any],
    lifespan_state: dict[str, Any],
    description: str,
    on_timeout: Callable[[], None] | None = None,
) -> Any:
    """Run *fn(pet)* with the pet client, handling lock/semaphore/timeout/errors.

    The helper encapsulates the full boilerplate shared by every pytanque
    operation that follows the simple "acquire lock, ensure pet, do work"
    pattern:

    1. PetanqueError import check
    2. _pet_lock acquisition with timeout
    3. _ensure_pet (lazy-init the pet subprocess)
    4. asyncio.Semaphore + asyncio.wait_for (async-level timeout)
    5. All four standard exception handlers

    *fn* receives the live pet client and must return the desired result.
    It runs inside a background thread with _pet_lock held; the lock is
    released automatically when *fn* returns or raises.
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
        }

    timeout: float = lifespan_state["pet_timeout"]

    def _execute() -> Any:
        if not _pet_lock.acquire(timeout=timeout):
            raise TimeoutError("Could not acquire pet lock")
        try:
            pet = _ensure_pet(lifespan_state)
            return fn(pet)
        finally:
            _pet_lock.release()

    sem = _get_pet_semaphore()
    try:
        async with sem:
            result = await asyncio.wait_for(
                asyncio.to_thread(_execute),
                timeout=timeout,
            )
            return result
    except asyncio.TimeoutError:
        _invalidate_pet(lifespan_state)
        if on_timeout:
            on_timeout()
        return {
            "success": False,
            "error": f"{description} timed out after {timeout}s.",
        }
    except PetanqueError as e:
        return {"success": False, "error": e.message}
    except FileNotFoundError:
        return {
            "success": False,
            "error": "pet binary not found on PATH. Install coq-lsp.",
        }
    except Exception as e:
        return {"success": False, "error": f"Unexpected error: {e}"}


async def run_step(
    tactic: str,
    file: str,
    theorem: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    line: int | None = None,
    character: int | None = None,
) -> dict[str, Any]:
    """Core implementation of rocq_step (testable without FastMCP Context)."""
    try:
        from pytanque import PetanqueError
    except ImportError:
        return {
            "success": False,
            "error": (
                "pytanque is not installed. "
                "Install with: pip install 'rocq-mcp[interactive]'"
            ),
        }

    forbidden = _check_forbidden_commands(tactic)
    if forbidden:
        return {"success": False, "error": forbidden}

    timeout: float = lifespan_state["pet_timeout"]

    # Determine if this is a session-start call
    _start_by_theorem = bool(file and theorem)
    _start_by_pos = bool(
        file and not theorem and line is not None and character is not None
    )

    if _start_by_pos:
        if not (0 <= line <= 100000) or not (0 <= character <= 100000):
            return {
                "success": False,
                "error": "line and character must be in range [0, 100000].",
            }

    # Path traversal check (before entering thread)
    if _start_by_theorem or _start_by_pos:
        file_path = str((Path(workspace).resolve() / file).resolve())
        ws_resolved = str(Path(workspace).resolve())
        if not file_path.startswith(ws_resolved + os.sep) and file_path != ws_resolved:
            return {"success": False, "error": "File path must be within workspace."}

    # Normalize tactic before _execute so both inner and outer scope
    # can reference the same normalized form for timeout eligibility.
    tac = tactic.strip()
    if not tac.endswith("."):
        tac += "."

    # Two-tier timeout: if the tactic is eligible for Rocq's Timeout
    # command, pass it to pet.run() (soft timeout).  The process-level
    # hard timeout is extended by a grace period so Rocq has time to
    # report the timeout before we kill the process.
    eligible = _is_timeout_eligible(tac) and timeout >= 1
    rocq_timeout = int(timeout) if eligible else None
    hard_timeout = _compute_hard_timeout(timeout) if eligible else timeout

    sem = _get_pet_semaphore()

    async with sem:

        def _execute() -> dict[str, Any]:
            if not _pet_lock.acquire(timeout=hard_timeout):
                raise TimeoutError("Could not acquire pet lock")
            try:
                pet = _ensure_pet(lifespan_state)

                # Start new session if file+theorem provided
                if _start_by_theorem:
                    ws = str(Path(workspace).resolve())
                    resolved_file = str((Path(workspace).resolve() / file).resolve())
                    pet.set_workspace(debug=False, dir=ws)
                    state = pet.start(resolved_file, theorem)
                    _session.update(
                        {
                            "state": state,
                            "file": file,
                            "theorem": theorem,
                            "history": [],
                        }
                    )
                elif _start_by_pos:
                    ws = str(Path(workspace).resolve())
                    resolved_file = str((Path(workspace).resolve() / file).resolve())
                    pet.set_workspace(debug=False, dir=ws)
                    state = pet.get_state_at_pos(resolved_file, line, character)
                    _session.update(
                        {
                            "state": state,
                            "file": file,
                            "theorem": f"@pos({line},{character})",
                            "history": [],
                        }
                    )

                current_state = _session.get("state")
                if current_state is None:
                    return {
                        "success": False,
                        "error": (
                            "No active session. "
                            "Provide file and theorem to start one."
                        ),
                    }

                # Execute tactic with optional Rocq-level timeout
                new_state = pet.run(current_state, tac, timeout=rocq_timeout)

                # Get complete goals before updating session state so
                # that if complete_goals() raises, the session is not
                # advanced.  Using complete_goals() instead of goals()
                # surfaces shelf and given_up info.
                complete = pet.complete_goals(new_state)
                goals_list = complete.goals if complete else []

                # Format goals
                goals_text = _format_goals(goals_list)

                # Only update session after both run() and
                # complete_goals() succeed
                _session["state"] = new_state
                _session["history"].append(tac)

                result = {
                    "success": True,
                    "goals": goals_text or "No goals remaining.",
                    "proof_finished": new_state.proof_finished,
                    "step": len(_session["history"]),
                }
                if complete and complete.shelf:
                    result["shelved_goals"] = len(complete.shelf)
                if complete and complete.given_up:
                    result["given_up_goals"] = len(complete.given_up)
                return result
            finally:
                _pet_lock.release()

        try:
            result = await asyncio.wait_for(
                asyncio.to_thread(_execute),
                timeout=hard_timeout,
            )
            return result
        except asyncio.TimeoutError:
            _invalidate_pet(lifespan_state)
            _session.update(
                {
                    "state": None,
                    "history": [],
                    "file": _session.get("file"),
                    "theorem": _session.get("theorem"),
                }
            )
            return {
                "success": False,
                "error": (
                    f"Tactic timed out after {timeout}s. Session lost but "
                    "file/theorem preserved. Start a new session (provide "
                    "file + theorem) and replay your tactics."
                ),
            }
        except PetanqueError as e:
            # Tactic error -- session state NOT corrupted (run() raised
            # before _session["state"] was updated)
            msg = str(e) if not hasattr(e, "message") else e.message
            if "timeout" in msg.lower() or "timed out" in msg.lower():
                return {
                    "success": False,
                    "error": (
                        f"Tactic timed out (Rocq Timeout {int(timeout)}s). "
                        "Session is still active \u2014 try a different tactic."
                    ),
                }
            return {"success": False, "error": msg}
        except FileNotFoundError:
            return {
                "success": False,
                "error": "pet binary not found on PATH.",
            }
        except Exception as e:
            return {"success": False, "error": f"Unexpected error: {e}"}


@mcp.tool
async def rocq_step(
    tactic: str,
    file: str = "",
    theorem: str = "",
    workspace: str = "",
    line: int | None = None,
    character: int | None = None,
    ctx: Context = None,
) -> dict[str, Any]:
    """Execute a tactic in an interactive proof session and return goals.

    Two ways to start a session:
    1. By theorem name: provide file and theorem.
    2. By position: provide file, line, and character (0-based).
       Use this to start at a specific position in the file, e.g., at an
       error position reported by rocq_compile's error_positions field.
       Leave theorem empty when using position-based start.

    If both theorem and line/character are provided, theorem takes precedence.

    Subsequent calls only need the tactic.

    If the session is lost (timeout, crash), you'll get an error.
    Re-send file + theorem (or file + line + character) to start a new
    session, then replay your tactics from your conversation history.

    Send one tactic per call. Do NOT send Qed -- the proof is complete
    when proof_finished is True.

    This server supports one interactive session at a time (single-client
    stdio model). Do not use with multi-client transports (HTTP/SSE).

    Args:
        tactic: The tactic to execute (e.g., "intros", "simpl", "lia").
        file: Path to the .v file (relative to workspace). Required for first call.
        theorem: Name of the theorem to prove. Required for theorem-based start.
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
        line: 0-based line number for position-based session start.
        character: 0-based character offset for position-based session start.
    """
    return await run_step(
        tactic=tactic,
        file=file,
        theorem=theorem,
        workspace=workspace or ROCQ_WORKSPACE,
        lifespan_state=ctx.lifespan_context,
        line=line,
        character=character,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi (Phase 2)
# ---------------------------------------------------------------------------

_MAX_STEP_MULTI_TACTICS = 20


async def run_step_multi(
    tactics: list[str],
    lifespan_state: dict[str, Any],
) -> dict[str, Any]:
    """Core implementation of rocq_step_multi (testable without FastMCP Context)."""
    try:
        from pytanque import PetanqueError
    except ImportError:
        return {
            "success": False,
            "error": (
                "pytanque is not installed. "
                "Install with: pip install 'rocq-mcp[interactive]'"
            ),
        }

    # Validate each tactic up front
    if len(tactics) > _MAX_STEP_MULTI_TACTICS:
        return {
            "success": False,
            "error": f"Too many tactics: {len(tactics)} exceeds maximum of {_MAX_STEP_MULTI_TACTICS}.",
        }

    for tac in tactics:
        forbidden = _check_forbidden_commands(tac)
        if forbidden:
            return {
                "success": False,
                "error": f"Forbidden in tactic {tac!r}: {forbidden}",
            }

    timeout: float = lifespan_state["pet_timeout"]
    hard_timeout = _compute_hard_timeout(timeout)
    sem = _get_pet_semaphore()

    # Shared list so partial results survive a timeout
    partial_results: list[dict[str, Any]] = []

    async with sem:

        def _execute() -> dict[str, Any]:
            if not _pet_lock.acquire(timeout=hard_timeout):
                raise TimeoutError("Could not acquire pet lock")
            try:
                pet = _ensure_pet(lifespan_state)

                parent_state = _session.get("state")
                if parent_state is None:
                    return {
                        "success": False,
                        "error": (
                            "No active session. "
                            "Use rocq_step with file and theorem to start one."
                        ),
                    }

                for tactic in tactics:
                    tac = tactic.strip()
                    if not tac.endswith("."):
                        tac += "."

                    # Per-tactic Rocq-level timeout for eligible tactics
                    tac_rocq_timeout = (
                        int(timeout)
                        if _is_timeout_eligible(tac) and timeout >= 1
                        else None
                    )

                    entry: dict[str, Any] = {"tactic": tac}
                    try:
                        new_state = pet.run(parent_state, tac, timeout=tac_rocq_timeout)

                        # Get complete goals for the trial state
                        complete = pet.complete_goals(new_state)
                        goals_list = complete.goals if complete else []

                        # Format goals
                        goals_text = _format_goals(goals_list)
                        entry["success"] = True
                        entry["goals"] = goals_text or "No goals remaining."
                        entry["proof_finished"] = new_state.proof_finished
                        if complete and complete.shelf:
                            entry["shelved_goals"] = len(complete.shelf)
                        if complete and complete.given_up:
                            entry["given_up_goals"] = len(complete.given_up)
                    except PetanqueError as e:
                        entry["success"] = False
                        entry["error"] = e.message

                    partial_results.append(entry)

                # Do NOT update _session -- this is read-only exploration
                return {"success": True, "results": list(partial_results)}
            finally:
                _pet_lock.release()

        try:
            result = await asyncio.wait_for(
                asyncio.to_thread(_execute),
                timeout=hard_timeout,
            )
            return result
        except asyncio.TimeoutError:
            _invalidate_pet(lifespan_state)
            _session.update(
                {
                    "state": None,
                    "history": [],
                    "file": _session.get("file"),
                    "theorem": _session.get("theorem"),
                }
            )
            resp: dict[str, Any] = {
                "success": False,
                "error": (
                    f"Multi-tactic exploration timed out after {timeout}s. "
                    "Session lost but file/theorem preserved. "
                    "Start a new session (provide file + theorem to "
                    "rocq_step) and replay your tactics."
                ),
            }
            if partial_results:
                resp["partial_results"] = list(partial_results)
            return resp
        except PetanqueError as e:
            return {"success": False, "error": e.message}
        except FileNotFoundError:
            return {
                "success": False,
                "error": "pet binary not found on PATH.",
            }
        except Exception as e:
            return {"success": False, "error": f"Unexpected error: {e}"}


@mcp.tool
async def rocq_step_multi(
    tactics: list[str],
    ctx: Context = None,
) -> dict[str, Any]:
    """Try multiple tactics against the current proof state and return all results.

    Does NOT advance the session — use rocq_step with the winning tactic to commit.
    Requires an active rocq_step session.

    Useful for quickly testing which automation tactic works:
      tactics=["auto", "lia", "lra", "ring", "omega", "tauto"]

    To auto-solve the current subgoal, first run rocq_step with "intros."
    then call this tool with the standard automation tactics:
      ["trivial", "reflexivity", "assumption", "exact I", "auto", "eauto",
       "tauto", "intuition", "lia", "lra", "nia", "nra", "ring", "field",
       "decide equality", "firstorder"]
    Pick the first successful tactic and commit it with rocq_step.
    Note: lia/lra/ring/field require the .v file to import Lia/Lra/Ring/Field.

    Args:
        tactics: List of tactics to try (max 20).
    """
    return await run_step_multi(
        tactics=tactics,
        lifespan_state=ctx.lifespan_context,
    )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> None:
    """Run the MCP server."""
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
