"""Rocq MCP Server — tools for Rocq/Coq proof development."""

from __future__ import annotations

import asyncio
import os
import re
import signal
import subprocess
import tempfile
import threading
from pathlib import Path
from typing import Any

from fastmcp import FastMCP, Context
from fastmcp.server.lifespan import lifespan

from rocq_mcp.verify import (
    _check_forbidden_commands,
    build_verification_source,
    parse_and_classify_assumptions,
    verification_hint,
)

# ---------------------------------------------------------------------------
# Configuration (env vars with defaults)
# ---------------------------------------------------------------------------

ROCQ_WORKSPACE: str = os.environ.get("ROCQ_WORKSPACE", os.getcwd())
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


# ---------------------------------------------------------------------------
# Tool: rocq_compile
# ---------------------------------------------------------------------------


@mcp.tool
def rocq_compile(
    source: str,
    workspace: str = "",
    timeout: int = 0,
) -> dict[str, Any]:
    """Compile Rocq source code and return structured errors.

    Use this as the first step for any proof. 81% of proofs succeed
    via direct compilation. Pass the complete .v file content.

    Args:
        source: Complete Rocq (.v) file content to compile.
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Compilation timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
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
        return {
            "success": False,
            "error": result["stderr"][:4000],
        }


# ---------------------------------------------------------------------------
# Tool: rocq_verify
# ---------------------------------------------------------------------------


@mcp.tool
def rocq_verify(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str = "",
    timeout: int = 0,
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

    Known limitation: proofs that define local types/functions (e.g.,
    Fixpoint sum_f_R0, Definition C) may fail verification even if correct,
    because module-qualified names (M.C) don't unify with outer-scope names.
    If verification fails with "Unable to unify", the proof may still be
    correct -- use rocq_compile result as fallback.

    Args:
        proof: The complete proof file content (including imports).
        problem_name: The unqualified theorem name (e.g., "add_comm", not "Nat.add_comm").
        problem_statement: The original problem file content (with Admitted/Abort).
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Verification timeout in seconds (default: ROCQ_VERIFY_TIMEOUT env var).
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

    # Build the verification source
    try:
        verification_source = build_verification_source(
            proof,
            problem_name,
            problem_statement,
        )
    except ValueError as e:
        return {"verified": False, "error": str(e)}

    # Run coqc on the verification source
    result = _run_coqc(verification_source, workspace, timeout)

    if result["timed_out"]:
        return {
            "verified": False,
            "error": f"Verification timed out after {timeout}s.",
        }

    if result["returncode"] != 0:
        return {
            "verified": False,
            "error": result["stderr"][:4000],
            "hint": verification_hint(result["stderr"]),
        }

    # Parse and classify Print Assumptions output
    verdict, details = parse_and_classify_assumptions(result["stdout"])

    if verdict == "closed":
        return {
            "verified": True,
            "assumptions": "Closed under the global context",
        }
    elif verdict == "standard_only":
        return {
            "verified": True,
            "assumptions": details["standard"],
            "note": "Proof uses standard axioms (e.g., classical logic, Reals).",
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

    forbidden = _check_forbidden_commands(command)
    if forbidden:
        return {"success": False, "error": forbidden}
    forbidden = _check_forbidden_commands(preamble)
    if forbidden:
        return {"success": False, "error": forbidden}

    timeout: float = lifespan_state["pet_timeout"]

    _temp_files: list[str] = []

    def _run_query() -> list[tuple[int, str]]:
        if not _pet_lock.acquire(timeout=timeout):
            raise TimeoutError("Could not acquire pet lock")
        try:
            pet = _ensure_pet(lifespan_state)
            ws = str(Path(workspace).resolve())
            pet.set_workspace(debug=False, dir=ws)

            preamble_text = preamble.strip()
            dummy_source = (
                f"{preamble_text}\n"
                "Lemma _rocq_mcp_dummy : True. Proof. exact I. Qed.\n"
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
                return [(lvl, msg) for lvl, msg in feedback]
            finally:
                dummy_path.unlink(missing_ok=True)
        finally:
            _pet_lock.release()

    sem = _get_pet_semaphore()
    try:
        async with sem:
            feedback = await asyncio.wait_for(
                asyncio.to_thread(_run_query),
                timeout=timeout,
            )
            output = "\n".join(msg for _, msg in feedback)
            if len(output) > _MAX_QUERY_OUTPUT:
                output = (
                    output[:_MAX_QUERY_OUTPUT]
                    + f"\n... (truncated, {len(output)} total chars)"
                )
            return {"success": True, "output": output or "(no output)"}
    except asyncio.TimeoutError:
        _invalidate_pet(lifespan_state)
        # Clean up any temp files left by the orphaned thread
        for p in _temp_files:
            Path(p).unlink(missing_ok=True)
        return {"success": False, "error": f"Query timed out after {timeout}s."}
    except PetanqueError as e:
        return {"success": False, "error": e.message}
    except FileNotFoundError:
        return {
            "success": False,
            "error": "pet binary not found on PATH. Install coq-lsp.",
        }
    except Exception as e:
        return {"success": False, "error": f"Unexpected error: {e}"}


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


async def run_step(
    tactic: str,
    file: str,
    theorem: str,
    workspace: str,
    lifespan_state: dict[str, Any],
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
    sem = _get_pet_semaphore()

    async with sem:

        def _execute() -> dict[str, Any]:
            if not _pet_lock.acquire(timeout=timeout):
                raise TimeoutError("Could not acquire pet lock")
            try:
                pet = _ensure_pet(lifespan_state)

                # Start new session if file+theorem provided
                if file and theorem:
                    ws = str(Path(workspace).resolve())
                    pet.set_workspace(debug=False, dir=ws)
                    state = pet.start(file, theorem)
                    _session.update(
                        {
                            "state": state,
                            "file": file,
                            "theorem": theorem,
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

                # Execute tactic
                tac = tactic.strip()
                if not tac.endswith("."):
                    tac += "."

                new_state = pet.run(current_state, tac)

                # Get goals before updating session state so that
                # if goals() raises, the session is not advanced.
                goals = pet.goals(new_state)
                goals_list = goals or []

                # Only update session after both run() and goals() succeed
                _session["state"] = new_state
                _session["history"].append(tac)
                goals_text = "\n\n".join(g.pp or str(g) for g in goals_list)

                return {
                    "success": True,
                    "goals": goals_text or "No goals remaining.",
                    "proof_finished": new_state.proof_finished,
                    "step": len(_session["history"]),
                }
            finally:
                _pet_lock.release()

        try:
            result = await asyncio.wait_for(
                asyncio.to_thread(_execute),
                timeout=timeout,
            )
            return result
        except asyncio.TimeoutError:
            _invalidate_pet(lifespan_state)
            _session.update({"state": None, "history": []})
            return {
                "success": False,
                "error": (
                    f"Tactic timed out after {timeout}s. Session lost. "
                    "Start a new session (provide file + theorem) and "
                    "replay your tactics."
                ),
            }
        except PetanqueError as e:
            # Tactic error -- session state NOT corrupted (run() raised
            # before _session["state"] was updated)
            return {"success": False, "error": e.message}
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
    ctx: Context = None,
) -> dict[str, Any]:
    """Execute a tactic in an interactive proof session and return goals.

    On first call, provide file and theorem to start a new session.
    Subsequent calls only need the tactic.

    If the session is lost (timeout, crash), you'll get an error.
    Re-send file + theorem to start a new session, then replay
    your tactics from your conversation history.

    Send one tactic per call. Do NOT send Qed -- the proof is complete
    when proof_finished is True.

    This server supports one interactive session at a time (single-client
    stdio model). Do not use with multi-client transports (HTTP/SSE).

    Args:
        tactic: The tactic to execute (e.g., "intros", "simpl", "lia").
        file: Path to the .v file (relative to workspace). Required for first call.
        theorem: Name of the theorem to prove. Required for first call.
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
    """
    return await run_step(
        tactic=tactic,
        file=file,
        theorem=theorem,
        workspace=workspace or ROCQ_WORKSPACE,
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
