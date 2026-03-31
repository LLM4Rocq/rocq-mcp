"""Rocq MCP Server — interactive proof tools (start, check, step_multi, query, toc, notations).

This module contains the implementation of all tools that use the pytanque
(pet) subprocess for interactive proof exploration.  All functions accept
a ``lifespan_state`` dict instead of a FastMCP ``Context`` so they can be
tested without the MCP framework.

Tools:
- **rocq_start** — opens a proof context, returns ``state_id``
- **rocq_check** — executes commands sequentially (one tactic = step,
  full proof = batch)
- **rocq_step_multi** — try N tactics from the same state (branching),
  read-only exploration

Infrastructure:
- **Import cache** — ``_get_or_create_import_state`` caches the pytanque
  State after running import commands, skipping re-processing on repeated calls.
- **State table** — ``_state_table`` stores all proof states with integer
  IDs, enabling tree-shaped exploration via ``from_state=N``.
"""

from __future__ import annotations

import asyncio
import hashlib
import os
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from rocq_mcp.verify import _check_forbidden_commands

# Imports from server.py — these are all defined before server.py imports
# interactive, so the circular import resolves cleanly.
# NOTE: _pet_lock is accessed via module reference (_server._pet_lock)
# because _force_release_pet_lock can replace the global.  A bare
# ``from server import _pet_lock`` would capture a stale reference.
import rocq_mcp.server as _server

# _PetLockTimeout is a class used in raise/except — direct import required.
# Everything else is accessed via _server.X so that monkeypatching on
# rocq_mcp.server is visible.
from rocq_mcp.server import _PetLockTimeout

# _split_rocq_sentences is in compile — import directly (no cycle).
from rocq_mcp.compile import _split_rocq_sentences

# ---------------------------------------------------------------------------
# Goal formatting helper (shared by run_check, run_step_multi)
# ---------------------------------------------------------------------------

_MAX_GOALS_LENGTH: int = 8000  # Max chars for formatted goals output
_MAX_GOALS_SHOWN: int = 10  # Max number of goals to format


def _format_goals(goals_list: list[Any]) -> str:
    """Format goal objects into readable text with hypotheses."""
    total = len(goals_list)
    shown = min(total, _MAX_GOALS_SHOWN)
    parts = []
    for i, g in enumerate(goals_list[:shown]):
        hyps = "\n".join(
            f"{', '.join(h.names)}" f"{' := ' + h.def_ if h.def_ else ''}" f" : {h.ty}"
            for h in g.hyps
        )
        pp = f"{hyps}\n|-{g.ty}"
        if total > 1:
            parts.append(f"Goal {i + 1}:\n{pp}")
        else:
            parts.append(pp)
    if total > shown:
        parts.append(f"... ({total} goals total, showing first {shown})")
    result = "\n\n".join(parts)
    total_len = len(result)
    if total_len > _MAX_GOALS_LENGTH:
        result = (
            result[:_MAX_GOALS_LENGTH] + f"... (truncated, {total_len} chars total)"
        )
    return result


def _try_get_goals(pet: Any, state: Any) -> str | None:
    """Best-effort goal retrieval.  Returns formatted text or None."""
    try:
        complete = pet.complete_goals(state)
        goals_list = complete.goals if complete else []
        text = _format_goals(goals_list)
        return text or None
    except Exception:
        return None


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
# Import cache
# ---------------------------------------------------------------------------

_MAX_IMPORT_CACHE_SIZE: int = 10


@dataclass
class _CachedImportContext:
    """Cached pytanque State after running a set of import commands."""

    state: Any
    imports_hash: str
    workspace: str
    pet_generation: int


_import_cache: dict[str, _CachedImportContext] = {}
_import_cache_generation: int = 0


def _get_or_create_import_state(
    pet: Any,
    workspace: str,
    import_commands: list[str],
    lifespan_state: dict[str, Any],
) -> Any:
    """Return a cached post-import pytanque State, creating if needed.

    Writes all *import_commands* to a cache ``.v`` file so that coq-lsp
    processes them natively, then calls ``get_state_at_pos`` at the end
    of the file.  Subsequent calls with the same imports and workspace
    return the cached State instantly (skipping import re-processing).
    """
    imports_key = hashlib.sha256("\n".join(import_commands).encode()).hexdigest()
    ws = str(Path(workspace).resolve())

    cached = _import_cache.get(imports_key)
    if (
        cached
        and cached.workspace == ws
        and cached.pet_generation == _import_cache_generation
    ):
        return cached.state

    # Build the cache file content from the import commands.  coq-lsp
    # will process these as part of the file, so ``get_state_at_pos``
    # at the end gives us the complete post-import state.
    cache_content = "\n".join(import_commands) + "\n" if import_commands else ""
    cache_file = Path(ws) / f"rocq_mcp_cache_{os.getpid()}_.v"
    file_changed = not cache_file.exists() or cache_file.read_text() != cache_content
    if file_changed:
        cache_file.write_text(cache_content)

    # The file must exist on disk before set_workspace so coq-lsp can
    # index it.  Force a workspace re-set when the file content changed
    # so coq-lsp picks up the updated imports.
    if file_changed:
        lifespan_state["current_workspace"] = None  # force re-set
    _server._set_workspace_if_needed(pet, workspace, lifespan_state)

    end_line = cache_content.count("\n")
    state = pet.get_state_at_pos(str(cache_file), end_line, 0)

    _import_cache[imports_key] = _CachedImportContext(
        state=state,
        imports_hash=imports_key,
        workspace=ws,
        pet_generation=_import_cache_generation,
    )

    # Bound cache size (FIFO eviction)
    if len(_import_cache) > _MAX_IMPORT_CACHE_SIZE:
        del _import_cache[next(iter(_import_cache))]

    return state


def _invalidate_import_cache() -> None:
    """Clear all cached import states (called on pet crash/invalidation)."""
    global _import_cache_generation
    _import_cache.clear()
    _import_cache_generation += 1


# ---------------------------------------------------------------------------
# State table
# ---------------------------------------------------------------------------

_MAX_STATES: int = int(os.environ.get("ROCQ_MAX_STATES", "200"))


@dataclass
class _StateEntry:
    """A proof state stored in the state table."""

    state: Any  # pytanque State
    file: str
    theorem: str
    workspace: str
    parent_id: int | None
    tactic: str | None
    step: int
    proof_finished: bool = False
    file_mtime: float | None = None  # mtime at session creation
    resolved_file: str | None = None  # absolute path for staleness check


_state_table: dict[int, _StateEntry] = {}
_state_next_id: int = 1
_state_current_id: int | None = None


def _state_add(
    state: Any,
    file: str,
    theorem: str,
    workspace: str,
    parent_id: int | None,
    tactic: str | None,
    step: int,
    *,
    file_mtime: float | None = None,
    resolved_file: str | None = None,
) -> int:
    """Add a state to the table and return its integer ID."""
    global _state_next_id, _state_current_id
    sid = _state_next_id
    _state_next_id += 1
    _state_table[sid] = _StateEntry(
        state=state,
        file=file,
        theorem=theorem,
        workspace=workspace,
        parent_id=parent_id,
        tactic=tactic,
        step=step,
        proof_finished=getattr(state, "proof_finished", False),
        file_mtime=file_mtime,
        resolved_file=resolved_file,
    )
    _state_current_id = sid
    # Evict oldest entries when table exceeds max size
    while len(_state_table) > _MAX_STATES:
        del _state_table[min(_state_table)]
    return sid


def _state_get(state_id: int) -> _StateEntry | None:
    """Look up a state by ID.  Returns None if not found."""
    return _state_table.get(state_id)


def _state_get_or_error(state_id: int) -> tuple[_StateEntry | None, str | None]:
    """Look up a state by ID, returning (entry, None) or (None, error_msg)."""
    entry = _state_table.get(state_id)
    if entry is not None:
        return entry, None
    # Distinguish eviction from never-existed
    if state_id < _state_next_id:
        return None, (
            f"State {state_id} expired (evicted from table or lost to pet restart). "
            f"Use rocq_start to begin a new session."
        )
    return None, f"State {state_id} does not exist."


def _state_invalidate_all() -> None:
    """Clear all states (called on pet crash/invalidation)."""
    global _state_current_id
    _state_table.clear()
    _state_current_id = None


def _check_staleness(entry: _StateEntry) -> str | None:
    """Check if a state's backing file has been modified since session start.

    Returns a warning message if the file changed or is inaccessible,
    or None if fresh.  Returns None for preamble-mode states (no backing file).
    """
    if entry.resolved_file is None or entry.file_mtime is None:
        return None
    try:
        current_mtime = os.path.getmtime(entry.resolved_file)
    except OSError:
        return (
            f"File '{entry.file}' is no longer accessible. "
            f"The proof state may be stale. "
            f"Use rocq_start to begin a fresh session."
        )
    if current_mtime != entry.file_mtime:
        return (
            f"File '{entry.file}' has been modified since session start. "
            f"The proof state may be stale. "
            f"Use rocq_start to begin a fresh session."
        )
    return None


def _reconstruct_tactic_path(state_id: int) -> tuple[list[str], bool]:
    """Walk the parent_id chain backward and return (tactics in root→leaf order, complete).

    Returns (tactics, True) if the full chain to root was traversed.
    Returns (tactics, False) if the chain was broken by eviction or cycle.
    """
    tactics: list[str] = []
    current_id: int | None = state_id
    visited: set[int] = set()
    while current_id is not None:
        if current_id in visited:
            break  # cycle detected
        visited.add(current_id)
        entry = _state_get(current_id)
        if entry is None:
            break  # chain broken by eviction
        if entry.tactic is not None:
            tactics.append(entry.tactic)
        current_id = entry.parent_id
    tactics.reverse()
    complete = current_id is None  # True only if we reached root (parent_id=None)
    return tactics, complete


# ---------------------------------------------------------------------------
# Register pet invalidation hooks
# ---------------------------------------------------------------------------
# These are called by _invalidate_pet() in server.py whenever pet is killed
# (timeout, crash).  All cached State objects become invalid when pet dies.

_server._pet_invalidation_hooks.append(_invalidate_import_cache)
_server._pet_invalidation_hooks.append(_state_invalidate_all)


# ---------------------------------------------------------------------------
# Tool: rocq_query (with import caching)
# ---------------------------------------------------------------------------

_MAX_QUERY_OUTPUT = 8000


async def run_query(
    command: str,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    max_results: int | None = None,
) -> dict[str, Any]:
    """Core implementation of rocq_query (testable without FastMCP Context).

    Uses the import cache for preamble commands — repeated queries with the
    same imports skip the import phase entirely.
    """
    forbidden = _check_forbidden_commands(command)
    if forbidden:
        return {"success": False, "error": forbidden}
    forbidden = _check_forbidden_commands(preamble)
    if forbidden:
        return {"success": False, "error": forbidden}

    def _do_query(pet: Any) -> dict[str, Any]:
        preamble_text = preamble.strip()
        preamble_cmds = _split_rocq_sentences(preamble_text) if preamble_text else []

        # Get a usable state — cached if preamble was seen before
        state = _get_or_create_import_state(
            pet, workspace, preamble_cmds, lifespan_state
        )

        cmd = command.strip()
        if not cmd.endswith("."):
            cmd += "."
        state = pet.run(state, cmd)
        feedback = state.feedback or []

        # Apply result-count limit before character truncation
        total_results = len(feedback)
        if max_results is not None and max_results > 0 and total_results > max_results:
            feedback = feedback[:max_results]

        output = "\n".join(msg for _, msg in feedback)
        if max_results is not None and max_results > 0 and total_results > max_results:
            output += (
                f"\n... ({total_results - max_results} more results, "
                f"{total_results} total)"
            )
        if len(output) > _MAX_QUERY_OUTPUT:
            output = (
                output[:_MAX_QUERY_OUTPUT]
                + f"\n... (truncated, {len(output)} total chars)"
            )
        return {"success": True, "output": output or "(no output)"}

    return await _server._run_with_pet(
        _do_query,
        lifespan_state,
        "Query",
    )


# ---------------------------------------------------------------------------
# Tool: rocq_assumptions
# ---------------------------------------------------------------------------


async def run_assumptions(
    name: str,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> dict[str, Any]:
    """Core implementation of rocq_assumptions (testable without FastMCP Context).

    Runs ``Print Assumptions <name>.`` via :func:`run_query` and classifies
    the result using :func:`verify.parse_and_classify_assumptions`.
    """
    from rocq_mcp.verify import parse_and_classify_assumptions

    # Validate: non-empty, valid Rocq identifier or qualified name
    clean_name = name.strip() if name else ""
    if not clean_name:
        return {"success": False, "error": "Theorem name must not be empty."}
    if not re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", clean_name
    ):
        return {
            "success": False,
            "error": f"Invalid identifier: {clean_name!r}. "
            "Expected a Rocq name like 'add_comm' or 'Nat.add_comm'.",
        }

    query_result = await run_query(
        command=f"Print Assumptions {clean_name}.",
        preamble=preamble,
        workspace=workspace,
        lifespan_state=lifespan_state,
    )
    if not query_result.get("success"):
        return query_result

    raw_output = query_result["output"]
    try:
        verdict, details = parse_and_classify_assumptions(raw_output)
    except Exception as e:
        return {
            "success": False,
            "error": f"Failed to parse assumptions output: {e}",
            "raw_output": raw_output,
        }
    result: dict[str, Any] = {
        "success": True,
        "theorem": clean_name,
        "verdict": verdict,
        "raw_output": raw_output,
    }
    if verdict == "closed":
        result["assumptions"] = []
    elif verdict == "standard_only":
        result["assumptions"] = details.get("standard", [])
    else:
        result["assumptions"] = details.get("suspicious", [])
        result["standard_assumptions"] = details.get("standard", [])
    return result


# ---------------------------------------------------------------------------
# Tool: rocq_toc
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
        _server._set_workspace_if_needed(pet, workspace, lifespan_state)
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

    return await _server._run_with_pet(
        _do_toc,
        lifespan_state,
        "TOC request",
    )


# ---------------------------------------------------------------------------
# Tool: rocq_notations
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
        _server._set_workspace_if_needed(pet, workspace, lifespan_state)
        ws = str(Path(workspace).resolve())

        preamble_text = preamble.strip()
        dummy_source = (
            f"{preamble_text}\n" "Lemma _rocq_mcp_dummy : True. Proof. exact I. Qed.\n"
        )
        import tempfile

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
            _server._cleanup_coqc_artifacts(str(dummy_path))

    def _on_timeout() -> None:
        for p in _temp_files:
            _server._cleanup_coqc_artifacts(p)

    return await _server._run_with_pet(
        _do_notations,
        lifespan_state,
        "Notation query",
        on_timeout=_on_timeout,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_start
# ---------------------------------------------------------------------------

_MAX_STEP_MULTI_TACTICS = 20


async def run_start(
    file: str,
    theorem: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    line: int | None = None,
    character: int | None = None,
    preamble: str = "",
) -> dict[str, Any]:
    """Open a proof context and return a state_id.

    Three start modes (precedence: theorem > position > preamble):
    1. By theorem: file + theorem -> pet.start()
    2. By position: file + line + character -> pet.get_state_at_pos()
    3. From imports: preamble -> _get_or_create_import_state()
    """
    # Mode detection
    _start_by_theorem = bool(file and theorem)
    _start_by_pos = bool(
        file and not theorem and line is not None and character is not None
    )
    _start_by_preamble = bool(
        not file and not theorem and preamble and preamble.strip()
    )

    if not (_start_by_theorem or _start_by_pos or _start_by_preamble):
        return {
            "success": False,
            "error": (
                "No valid start mode. Provide file+theorem, "
                "file+line+character, or preamble."
            ),
        }

    if _start_by_pos:
        if not (0 <= line <= 100000) or not (0 <= character <= 100000):
            return {
                "success": False,
                "error": "line and character must be in range [0, 100000].",
            }

    # Path traversal check
    if _start_by_theorem or _start_by_pos:
        file_path = str((Path(workspace).resolve() / file).resolve())
        ws_resolved = str(Path(workspace).resolve())
        if not file_path.startswith(ws_resolved + os.sep) and file_path != ws_resolved:
            return {"success": False, "error": "File path must be within workspace."}

    # Forbidden commands check for preamble
    if _start_by_preamble:
        forbidden = _check_forbidden_commands(preamble)
        if forbidden:
            return {"success": False, "error": forbidden}

    def _execute(pet: Any) -> dict[str, Any]:
        if _start_by_theorem:
            resolved_file = str((Path(workspace).resolve() / file).resolve())
            _server._set_workspace_if_needed(pet, workspace, lifespan_state)
            state = pet.start(resolved_file, theorem)
            # Capture mtime after pet.start to avoid TOCTOU gap
            try:
                file_mtime = os.path.getmtime(resolved_file)
            except OSError:
                file_mtime = None
            state_id = _state_add(
                state=state,
                file=file,
                theorem=theorem,
                workspace=workspace,
                parent_id=None,
                tactic=None,
                step=0,
                file_mtime=file_mtime,
                resolved_file=resolved_file,
            )
            goals = _try_get_goals(pet, state) or ""
            return {
                "success": True,
                "state_id": state_id,
                "goals": goals,
                "file": file,
                "theorem": theorem,
                "proof_finished": getattr(state, "proof_finished", False),
            }
        elif _start_by_pos:
            resolved_file = str((Path(workspace).resolve() / file).resolve())
            _server._set_workspace_if_needed(pet, workspace, lifespan_state)
            state = pet.get_state_at_pos(resolved_file, line, character)
            # Capture mtime after get_state_at_pos to avoid TOCTOU gap
            try:
                file_mtime = os.path.getmtime(resolved_file)
            except OSError:
                file_mtime = None
            state_id = _state_add(
                state=state,
                file=file,
                theorem=f"@pos({line},{character})",
                workspace=workspace,
                parent_id=None,
                tactic=None,
                step=0,
                file_mtime=file_mtime,
                resolved_file=resolved_file,
            )
            goals = _try_get_goals(pet, state) or ""
            return {
                "success": True,
                "state_id": state_id,
                "goals": goals,
                "file": file,
                "theorem": f"@pos({line},{character})",
                "proof_finished": getattr(state, "proof_finished", False),
            }
        else:
            # Preamble mode
            preamble_cmds = _split_rocq_sentences(preamble) if preamble.strip() else []
            import_state = _get_or_create_import_state(
                pet, workspace, preamble_cmds, lifespan_state
            )
            state_id = _state_add(
                state=import_state,
                file="<preamble>",
                theorem="<preamble>",
                workspace=workspace,
                parent_id=None,
                tactic=None,
                step=0,
            )
            return {
                "success": True,
                "state_id": state_id,
                "goals": "",
                "file": "<preamble>",
                "theorem": "<preamble>",
                "proof_finished": getattr(import_state, "proof_finished", False),
            }

    return await _server._run_with_pet(
        _execute,
        lifespan_state,
        "Start proof context",
    )


# ---------------------------------------------------------------------------
# Tool: rocq_check
# ---------------------------------------------------------------------------


async def run_check(
    body: str,
    workspace: str,
    timeout: float,
    lifespan_state: dict[str, Any],
    from_state: int | None = None,
) -> dict[str, Any]:
    """Execute commands sequentially from a state.

    One command = step. Multiple commands = batch.
    Returns state_id, goals, proof_finished, and timing info.
    On error mid-batch, returns last_valid_state_id for recovery.
    """
    if len(body) > _server.ROCQ_MAX_SOURCE_SIZE:
        return {
            "success": False,
            "error": f"Body too large ({len(body)} bytes, max {_server.ROCQ_MAX_SOURCE_SIZE}).",
        }

    forbidden = _check_forbidden_commands(body)
    if forbidden:
        return {"success": False, "error": forbidden}

    commands = _split_rocq_sentences(body) if body.strip() else []

    # Resolve base state
    if from_state is not None:
        entry, err = _state_get_or_error(from_state)
        if err:
            return {"success": False, "error": err}
        base_state_id = from_state
    else:
        cur_id = _state_current_id
        if cur_id is not None:
            entry = _state_get(cur_id)
            if entry is None:
                return {
                    "success": False,
                    "error": "No active state. Use rocq_start first.",
                }
            base_state_id = cur_id
        else:
            return {
                "success": False,
                "error": "No active state. Use rocq_start first.",
            }

    # Empty body — return early
    if not commands:
        return {
            "success": True,
            "commands_run": 0,
            "state_id": base_state_id,
            "parent_state_id": base_state_id,
            "goals": "",
            "proof_finished": entry.proof_finished,
            "check_time_ms": 0,
        }

    _timeout = timeout if timeout > 0 else lifespan_state["pet_timeout"]
    is_single = len(commands) == 1

    def _execute(pet: Any) -> dict[str, Any]:
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

        # Re-validate state under lock (pet may have restarted since outer check)
        re_entry, re_err = _state_get_or_error(base_state_id)
        if re_err:
            return {"success": False, "error": re_err}
        entry_to_use = re_entry

        # Check for file staleness (non-blocking warning)
        stale_warning = _check_staleness(entry_to_use)

        start_time = time.monotonic()
        _server._set_workspace_if_needed(pet, entry_to_use.workspace, lifespan_state)

        state = entry_to_use.state
        prev_state_id = base_state_id

        for i, cmd in enumerate(commands):
            try:
                if _is_timeout_eligible(cmd) and _timeout >= 1:
                    if is_single:
                        rocq_timeout = int(_timeout)
                    else:
                        # Budget: divide timeout among commands so total
                        # stays within the hard_timeout window.
                        rocq_timeout = max(1, int(_timeout / len(commands)))
                else:
                    rocq_timeout = None

                new_state = pet.run(state, cmd, timeout=rocq_timeout)
                state_id = _state_add(
                    state=new_state,
                    file=entry_to_use.file,
                    theorem=entry_to_use.theorem,
                    workspace=entry_to_use.workspace,
                    parent_id=prev_state_id,
                    tactic=cmd,
                    step=entry_to_use.step + i + 1,
                    file_mtime=entry_to_use.file_mtime,
                    resolved_file=entry_to_use.resolved_file,
                )
                prev_state_id = state_id
                state = new_state
            except PetanqueError as e:
                # If pet died, re-raise so _run_with_pet detects it
                # and returns pet_restarted=True to the client.
                if not _server._pet_alive(lifespan_state.get("pet_client")):
                    raise
                goals = _try_get_goals(pet, state)
                result: dict[str, Any] = {
                    "success": False,
                    "error": e.message,
                    "failed_command": cmd,
                    "command_index": i,
                    "commands_run": i,
                    "last_valid_state_id": prev_state_id,
                    "goals_at_failure": goals,
                }
                if stale_warning:
                    result["stale_warning"] = stale_warning
                if prev_state_id is not None:
                    result["hint"] = (
                        f"Use rocq_check(body='...', from_state={prev_state_id}) "
                        f"or rocq_step_multi(tactics=[...], from_state={prev_state_id})."
                    )
                return result

        elapsed = time.monotonic() - start_time

        # Get goals at final state
        try:
            complete = pet.complete_goals(state)
            goals_list = complete.goals if complete else []
            goals_text = _format_goals(goals_list)
        except Exception:
            goals_text = "(goals unavailable)"
            complete = None

        result: dict[str, Any] = {
            "success": True,
            "goals": goals_text or "No goals remaining.",
            "proof_finished": state.proof_finished,
            "commands_run": len(commands),
            "check_time_ms": int(elapsed * 1000),
            "state_id": prev_state_id,
            "parent_state_id": base_state_id,
        }
        if stale_warning:
            result["stale_warning"] = stale_warning
        if complete and complete.shelf:
            result["shelved_goals"] = len(complete.shelf)
        if complete and complete.given_up:
            result["given_up_goals"] = len(complete.given_up)
        if state.proof_finished and prev_state_id is not None:
            tactics, chain_complete = _reconstruct_tactic_path(prev_state_id)
            if tactics:
                result["proof_tactics"] = tactics
            if not chain_complete:
                result["proof_tactics_complete"] = False
            result["proof_hint"] = (
                "Proof complete! Assemble imports + theorem statement "
                "+ Proof. + tactics + Qed. then validate with "
                "rocq_compile and rocq_verify."
            )
        return result

    # Timeout strategy: both single and multi-command use two-tier when eligible
    if _timeout >= 1:
        hard_timeout = _compute_hard_timeout(_timeout)
    else:
        hard_timeout = _timeout

    return await _server._run_with_pet(
        _execute,
        lifespan_state,
        "Check",
        timeout=float(hard_timeout),
    )


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi (with from_state support)
# ---------------------------------------------------------------------------


async def run_step_multi(
    tactics: list[str],
    lifespan_state: dict[str, Any],
    from_state: int | None = None,
) -> dict[str, Any]:
    """Core implementation of rocq_step_multi (testable without FastMCP Context).

    Supports ``from_state`` to try tactics from a specific state.
    Results are ephemeral — commit with ``rocq_check(body=..., from_state=...)``.
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
    sem = _server._get_pet_semaphore()

    # Shared list so partial results survive a timeout
    partial_results: list[dict[str, Any]] = []

    # Quick pre-check to avoid acquiring lock for invalid states.
    # Re-validated inside _execute (state may be invalidated between checks).
    if from_state is not None:
        entry, err = _state_get_or_error(from_state)
        if err:
            return {"success": False, "error": err}
    elif _state_current_id is None:
        return {"success": False, "error": "No active state. Use rocq_start first."}

    async with sem:

        def _execute() -> dict[str, Any]:
            # Access _pet_lock via module ref — see run_check comment.
            lock = _server._pet_lock
            if not lock.acquire(timeout=hard_timeout * 0.8):
                raise _PetLockTimeout("Could not acquire pet lock")
            try:
                pet = _server._ensure_pet(lifespan_state)

                # Determine the base state — unify both branches into
                # entry_to_use so workspace and staleness are always handled.
                entry_to_use: _StateEntry | None = None
                base_state_id: int | None = None
                if from_state is not None:
                    entry_to_use, err = _state_get_or_error(from_state)
                    if err:
                        return {"success": False, "error": err}
                    base_state_id = from_state
                else:
                    if _state_current_id is not None:
                        entry_to_use = _state_get(_state_current_id)
                    base_state_id = _state_current_id

                if entry_to_use is None:
                    return {
                        "success": False,
                        "error": "No active state. Use rocq_start first.",
                    }

                _server._set_workspace_if_needed(
                    pet, entry_to_use.workspace, lifespan_state
                )
                parent_state = entry_to_use.state

                # Check for file staleness (non-blocking warning)
                stale_warning = _check_staleness(entry_to_use)

                for tactic in tactics:
                    tac = tactic.strip()
                    if tac not in ("{", "}") and not tac.endswith("."):
                        tac += "."

                    # Per-tactic Rocq-level timeout for eligible tactics
                    # Budget: divide timeout among all tactics so total
                    # stays within the hard_timeout window.
                    per_tactic_budget = max(1, int(timeout / len(tactics)))
                    tac_rocq_timeout = (
                        per_tactic_budget
                        if _is_timeout_eligible(tac) and timeout >= 1
                        else None
                    )

                    entry_dict: dict[str, Any] = {"tactic": tac}
                    try:
                        new_state = pet.run(parent_state, tac, timeout=tac_rocq_timeout)

                        # Get complete goals for the trial state
                        complete = pet.complete_goals(new_state)
                        goals_list = complete.goals if complete else []

                        # Format goals
                        goals_text = _format_goals(goals_list)
                        entry_dict["success"] = True
                        entry_dict["goals"] = goals_text or "No goals remaining."
                        entry_dict["proof_finished"] = new_state.proof_finished
                        if complete and complete.shelf:
                            entry_dict["shelved_goals"] = len(complete.shelf)
                        if complete and complete.given_up:
                            entry_dict["given_up_goals"] = len(complete.given_up)
                    except PetanqueError as e:
                        # If pet died, re-raise so outer handler detects it
                        # and returns pet_restarted=True to the client.
                        if not _server._pet_alive(lifespan_state.get("pet_client")):
                            raise
                        entry_dict["success"] = False
                        entry_dict["error"] = e.message

                    partial_results.append(entry_dict)

                # Read-only exploration — do NOT update state table
                resp: dict[str, Any] = {
                    "success": True,
                    "results": list(partial_results),
                }
                if base_state_id is not None:
                    resp["from_state_id"] = base_state_id
                if stale_warning:
                    resp["stale_warning"] = stale_warning
                return resp
            finally:
                lock.release()

        try:
            result = await asyncio.wait_for(
                asyncio.to_thread(_execute),
                timeout=hard_timeout,
            )
            return result
        except asyncio.TimeoutError:
            _server._invalidate_pet(lifespan_state)
            await _server._force_release_pet_lock()
            resp: dict[str, Any] = {
                "success": False,
                "error": (
                    f"Multi-tactic exploration timed out after {timeout}s. "
                    "All states invalidated. Use rocq_start to begin a new session."
                ),
                "pet_restarted": True,
            }
            if partial_results:
                resp["partial_results"] = list(partial_results)
            return resp
        except _PetLockTimeout:
            return {
                "success": False,
                "error": "pet is busy (lock contention). Try again.",
            }
        except PetanqueError as e:
            if not _server._pet_alive(lifespan_state.get("pet_client")):
                _server._invalidate_pet(lifespan_state)
                await _server._force_release_pet_lock()
                return {
                    "success": False,
                    "error": f"Pet process died: {e.message}",
                    "pet_restarted": True,
                }
            return {"success": False, "error": e.message}
        except FileNotFoundError:
            return {
                "success": False,
                "error": "pet binary not found on PATH.",
            }
        except (BrokenPipeError, ConnectionError) as e:
            _server._invalidate_pet(lifespan_state)
            await _server._force_release_pet_lock()
            return {
                "success": False,
                "error": f"Pet process died: {e}",
                "pet_restarted": True,
            }
        except (OSError, RuntimeError, ValueError, TypeError) as e:
            return {"success": False, "error": f"Unexpected error: {e}"}
