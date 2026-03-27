"""Rocq MCP Server — interactive proof tools (step, query, toc, notations).

This module contains the implementation of all tools that use the pytanque
(pet) subprocess for interactive proof exploration.  All functions accept
a ``lifespan_state`` dict instead of a FastMCP ``Context`` so they can be
tested without the MCP framework.
"""

from __future__ import annotations

import asyncio
import os
import tempfile
from pathlib import Path
from typing import Any

from rocq_mcp.verify import _check_forbidden_commands

# Imports from server.py — these are all defined before server.py imports
# interactive, so the circular import resolves cleanly.
# NOTE: _pet_lock is accessed via module reference (_server._pet_lock)
# because _force_release_pet_lock can replace the global.  A bare
# ``from server import _pet_lock`` would capture a stale reference.
import rocq_mcp.server as _server

# _session is a mutable dict — direct import is safe (mutations visible
# everywhere).  _PetLockTimeout is a class used in raise/except — direct
# import required.  Everything else is accessed via _server.X so that
# monkeypatching on rocq_mcp.server is visible.
from rocq_mcp.server import (
    _PetLockTimeout,
    _session,
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
# Tool: rocq_query
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
            _server._cleanup_coqc_artifacts(str(dummy_path))

    def _on_timeout() -> None:
        for p in _temp_files:
            _server._cleanup_coqc_artifacts(p)

    return await _server._run_with_pet(
        _do_query,
        lifespan_state,
        "Query",
        on_timeout=_on_timeout,
    )


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
# Tool: rocq_step
# ---------------------------------------------------------------------------

_MAX_STEP_MULTI_TACTICS = 20


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
    if tac not in ("{", "}") and not tac.endswith("."):
        tac += "."

    # Two-tier timeout: if the tactic is eligible for Rocq's Timeout
    # command, pass it to pet.run() (soft timeout).  The process-level
    # hard timeout is extended by a grace period so Rocq has time to
    # report the timeout before we kill the process.
    eligible = _is_timeout_eligible(tac) and timeout >= 1
    rocq_timeout = int(timeout) if eligible else None
    hard_timeout = _compute_hard_timeout(timeout) if eligible else timeout

    sem = _server._get_pet_semaphore()

    async with sem:

        def _execute() -> dict[str, Any]:
            # Access _pet_lock via module ref — _force_release_pet_lock
            # can replace the global, and we need to capture the current one.
            lock = _server._pet_lock
            if not lock.acquire(timeout=hard_timeout * 0.8):
                raise _PetLockTimeout("Could not acquire pet lock")
            try:
                pet = _server._ensure_pet(lifespan_state)

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
        except _PetLockTimeout:
            return {
                "success": False,
                "error": "pet is busy (lock contention). Try again.",
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


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi
# ---------------------------------------------------------------------------


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
    sem = _server._get_pet_semaphore()

    # Shared list so partial results survive a timeout
    partial_results: list[dict[str, Any]] = []

    async with sem:

        def _execute() -> dict[str, Any]:
            # Access _pet_lock via module ref — see run_step comment.
            lock = _server._pet_lock
            if not lock.acquire(timeout=hard_timeout * 0.8):
                raise _PetLockTimeout("Could not acquire pet lock")
            try:
                pet = _server._ensure_pet(lifespan_state)

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
                    if tac not in ("{", "}") and not tac.endswith("."):
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
        except _PetLockTimeout:
            return {
                "success": False,
                "error": "pet is busy (lock contention). Try again.",
            }
        except PetanqueError as e:
            return {"success": False, "error": e.message}
        except FileNotFoundError:
            return {
                "success": False,
                "error": "pet binary not found on PATH.",
            }
        except Exception as e:
            return {"success": False, "error": f"Unexpected error: {e}"}
