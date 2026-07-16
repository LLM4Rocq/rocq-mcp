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

import hashlib
import os
import re
import tempfile
import time
from collections import OrderedDict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal, NamedTuple

try:
    from pytanque import PetanqueError as _PetanqueError
except ImportError:  # pragma: no cover - pytanque optional
    _PetanqueError = None  # type: ignore[assignment, misc]

from rocq_mcp.verify import _check_forbidden_commands

# Imports from server.py — these are all defined before server.py imports
# interactive, so the circular import resolves cleanly.
# NOTE: _pet_lock is accessed via module reference (_server._pet_lock)
# because _force_release_pet_lock can replace the global.  A bare
# ``from server import _pet_lock`` would capture a stale reference.
import rocq_mcp.server as _server
from rocq_mcp import taxonomy

# _split_rocq_sentences is in compile — import directly (no cycle).
from rocq_mcp.compile import _split_rocq_sentences, _is_focus_token
from rocq_mcp.envelope import collects_degraded, note_degraded

# ---------------------------------------------------------------------------
# Goal formatting helper (shared by run_check, run_step_multi)
# ---------------------------------------------------------------------------

_MAX_GOALS_LENGTH: int = 8000  # Max chars for formatted goals output
_MAX_GOALS_SHOWN: int = 10  # Max number of goals to format
_MAX_FEEDBACK_LENGTH: int = 50_000  # Max chars per feedback step
_MAX_TOTAL_FEEDBACK: int = 200_000  # Max total chars across all feedback steps
# Max line / character index accepted by ``rocq_start`` in by-position
# mode.  100k is well above any realistic .v file (a 100k-line file
# would be ~3 MB of source and far past any practical Coq build).
_MAX_LINE_CHAR_RANGE: int = 100_000

# LSP DiagnosticSeverity: 1=Error, 2=Warning, 3=Information, 4=Hint.
# See coq-lsp 0.2.5+9.1: lang/diagnostic.ml.
_LSP_SEVERITY_WARNING: int = 2


def _truncate_result(text: str, max_length: int) -> str:
    """Truncate *text* to *max_length* chars, appending an indicator if cut."""
    if len(text) <= max_length:
        return text
    return text[:max_length] + f"\n... (truncated, {len(text)} total chars)"


def _extract_feedback(state: Any, *, include_warnings: bool = True) -> str | None:
    """Extract non-empty feedback from a pytanque State, joined as a string.

    Returns *None* when there is nothing to report.  When
    ``include_warnings=False``, drops entries at LSP Warning severity
    (level 2) so warning noise does not crowd out tool output (Print /
    Search / vm_compute traces). See coq-lsp 0.2.5+9.1 ``lang/diagnostic.ml``.
    """
    if include_warnings:
        msgs = [msg for _, msg in (state.feedback or []) if msg]
    else:
        msgs = [
            msg
            for lvl, msg in (state.feedback or [])
            if msg and lvl != _LSP_SEVERITY_WARNING
        ]
    if not msgs:
        return None
    raw = "\n".join(msgs)
    return _truncate_result(raw, _MAX_FEEDBACK_LENGTH)


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


def _focus_depth(complete: Any) -> int | None:
    """How many ``{...}`` / bullet focus frames are open above the goal.

    Each suspended focus level is one entry in a ``complete_goals``
    result's proof ``stack``, so ``len(stack)`` is the current nesting
    depth: ``0`` in a flat, unfocused context, ``1`` just inside a ``{``
    or a bullet, and so on.  Returns ``None`` only when *complete* itself
    is ``None`` (no goal information — e.g. a non-proof state or an
    upstream pet error).
    """
    if complete is None:
        return None
    return len(complete.stack)


_GOAL_TYPE_CAP: int = 2000  # per-hypothesis/conclusion char cap in structured modes

#: goals_format values accepted everywhere goals are rendered.
#: ``diff`` / ``none`` are additionally accepted by run_check only.
GOALS_RENDER_FORMATS: frozenset[str] = frozenset({"pretty", "structured", "names_only"})


def _cap_type(text: str) -> str:
    if len(text) > _GOAL_TYPE_CAP:
        return text[:_GOAL_TYPE_CAP] + f"... (truncated, {len(text)} chars total)"
    return text


def _render_goals(goals_list: list[Any], goals_format: str = "pretty") -> Any:
    """Render goals per *goals_format*.

    - ``"pretty"`` -> the classic human-readable string (see
      :func:`_format_goals`).
    - ``"structured"`` -> ``[{hyps: [{names, type, body?}], conclusion}]``
      straight from pytanque's structured Goal objects.
    - ``"names_only"`` -> ``[{hyp_names: [...], conclusion}]`` — the
      token-lean variant for hypothesis-heavy proofs.

    List modes cap at ``_MAX_GOALS_SHOWN`` goals (a trailing
    ``{"omitted_goals": N}`` marker reports the overflow) and truncate
    individual type strings at ``_GOAL_TYPE_CAP`` chars.
    """
    if goals_format == "pretty":
        return _format_goals(goals_list)
    total = len(goals_list)
    shown = min(total, _MAX_GOALS_SHOWN)
    rendered: list[dict[str, Any]] = []
    for g in goals_list[:shown]:
        if goals_format == "structured":
            hyps = []
            for h in g.hyps:
                entry: dict[str, Any] = {
                    "names": list(h.names),
                    "type": _cap_type(h.ty),
                }
                if h.def_:
                    entry["body"] = _cap_type(h.def_)
                hyps.append(entry)
            rendered.append({"hyps": hyps, "conclusion": _cap_type(g.ty)})
        else:  # names_only
            rendered.append(
                {
                    "hyp_names": [n for h in g.hyps for n in h.names],
                    "conclusion": _cap_type(g.ty),
                }
            )
    if total > shown:
        rendered.append({"omitted_goals": total - shown})
    return rendered


def _goal_text(g: Any) -> str:
    """One goal's pretty text (hypotheses + turnstile + conclusion)."""
    hyps = "\n".join(
        f"{', '.join(h.names)}" f"{' := ' + h.def_ if h.def_ else ''}" f" : {h.ty}"
        for h in g.hyps
    )
    return f"{hyps}\n|-{g.ty}"


def _goals_diff(old_list: list[Any], new_list: list[Any]) -> dict[str, Any]:
    """Delta between two goal lists, by rendered per-goal text.

    Returns ``{unchanged: true, count}`` when nothing changed; otherwise
    ``{before_count, after_count, added: [goal texts new since parent],
    removed_count}``.  ``added`` is capped like pretty goals.
    """
    old_texts = [_goal_text(g) for g in old_list]
    new_texts = [_goal_text(g) for g in new_list]
    if old_texts == new_texts:
        return {"unchanged": True, "count": len(new_texts)}
    remaining = list(old_texts)
    added: list[str] = []
    for text in new_texts:
        if text in remaining:
            remaining.remove(text)
        else:
            added.append(text)
    added_shown = [_cap_type(t) for t in added[:_MAX_GOALS_SHOWN]]
    diff: dict[str, Any] = {
        "before_count": len(old_texts),
        "after_count": len(new_texts),
        "added": added_shown,
        "removed_count": len(remaining),
    }
    if len(added) > len(added_shown):
        diff["added_omitted"] = len(added) - len(added_shown)
    return diff


def _try_get_goals_with_depth(pet: Any, state: Any) -> tuple[str | None, int | None]:
    """Best-effort ``(goals_text, focus_depth)`` from one ``complete_goals`` call.

    Both elements are ``None`` if the call fails.
    """
    try:
        complete = pet.complete_goals(state)
        goals_list = complete.goals if complete else []
        return _format_goals(goals_list) or None, _focus_depth(complete)
    except Exception as e:
        note_degraded("goals:pet_call_failed", repr(e))
        return None, None


def _try_get_goals(pet: Any, state: Any) -> str | None:
    """Best-effort goal retrieval.  Returns formatted text or None."""
    text, _ = _try_get_goals_with_depth(pet, state)
    return text


def _try_render_goals_with_depth(
    pet: Any, state: Any, goals_format: str = "pretty"
) -> tuple[Any, int | None]:
    """Best-effort ``(goals_payload, focus_depth)`` in the requested format.

    ``payload`` is ``None`` when goal retrieval fails (recorded as a
    degraded note); callers substitute their existing empty value.
    """
    try:
        complete = pet.complete_goals(state)
        goals_list = complete.goals if complete else []
        if goals_format == "pretty":
            return _format_goals(goals_list) or None, _focus_depth(complete)
        return _render_goals(goals_list, goals_format), _focus_depth(complete)
    except Exception as e:
        note_degraded("goals:pet_call_failed", repr(e))
        return None, None


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

    # Position past the last line so all imports are in scope.
    # +1 ensures consistency with _get_file_end_state line counting.
    end_line = cache_content.count("\n") + 1
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


def _get_file_end_state(
    pet: Any,
    file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> Any:
    """Get pytanque State at end of a ``.v`` file (all definitions in scope).

    Resolves the file path, validates workspace containment, sets the
    workspace, counts lines, and calls ``pet.get_state_at_pos`` past the
    last line.  The returned state has all imports, definitions, and
    notations from the file in scope.

    This is used by tools that accept a ``file`` parameter as an
    alternative to ``preamble`` (e.g., ``rocq_query``, ``rocq_assumptions``).

    Raises:
        ValueError: If the file path is outside the workspace.
        FileNotFoundError: If the file does not exist or is not readable.
    """
    resolved = _server._resolve_file_in_workspace(file, workspace)

    try:
        content = Path(resolved).read_text()
    except PermissionError:
        raise FileNotFoundError(f"File not accessible: {file}")

    # coq-lsp re-reads individual files on every get_state_at_pos call,
    # so the workspace itself only needs re-setting when the workspace
    # path changes — _set_workspace_if_needed handles that.  Eagerly
    # invalidating ``current_workspace`` here used to defeat that cache
    # on every sibling call against the same project.
    _server._set_workspace_if_needed(pet, workspace, lifespan_state)

    # Position past the last line so all definitions are in scope.
    # +1 ensures files without a trailing newline still capture the last line.
    end_line = content.count("\n") + 1

    return pet.get_state_at_pos(resolved, end_line, 0)


def _invalidate_import_cache() -> None:
    """Clear all cached import states (called on pet crash/invalidation)."""
    global _import_cache_generation
    _import_cache.clear()
    _import_cache_generation += 1


# ---------------------------------------------------------------------------
# State table
# ---------------------------------------------------------------------------

_MAX_STATES: int = int(os.environ.get("ROCQ_MAX_STATES", "1000"))


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
    # Cumulative root->here command path, materialized at creation so a
    # finished proof's tactic chain survives LRU eviction of ancestors
    # (the tuple shares structure with the parent's — pointer copies).
    tactic_path: tuple[str, ...] = ()
    # Wall-clock timestamp; used by rocq_diag for age.
    created_at: float = field(default_factory=time.time)


# LRU-ordered: ``_state_get`` / ``_state_get_or_error`` move accessed
# entries to the most-recently-used end; eviction pops from the
# least-recently-used end.  Keeps actively-used states alive even when
# a parallel caller is churning through fresh states (e.g. two sub-agents
# on different files sharing one rocq-mcp process).
_state_table: "OrderedDict[int, _StateEntry]" = OrderedDict()
_state_next_id: int = 1


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
    global _state_next_id
    sid = _state_next_id
    _state_next_id += 1
    parent_entry = _state_table.get(parent_id) if parent_id is not None else None
    base_path = parent_entry.tactic_path if parent_entry is not None else ()
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
        tactic_path=(*base_path, tactic) if tactic is not None else base_path,
    )
    # Evict LRU entries when table exceeds max size.
    while len(_state_table) > _MAX_STATES:
        _state_table.popitem(last=False)
    return sid


def _state_get(state_id: int) -> _StateEntry | None:
    """Look up a state by ID and promote it to most-recently-used.

    Returns None if not found.  Promotion is the read-side of LRU: a
    parked state that's still being queried by ``from_state=N`` survives
    eviction pressure from a parallel caller churning through new states.
    """
    entry = _state_table.get(state_id)
    if entry is not None:
        _state_table.move_to_end(state_id)
    return entry


def _state_remove(state_id: int) -> None:
    """Drop a state from the table."""
    _state_table.pop(state_id, None)


def _state_get_or_error(state_id: int) -> tuple[_StateEntry | None, str | None]:
    """Look up a state by ID, returning (entry, None) or (None, error_msg).

    On hit, promotes the entry to most-recently-used (same LRU semantics
    as ``_state_get``).
    """
    entry = _state_table.get(state_id)
    if entry is not None:
        _state_table.move_to_end(state_id)
        return entry, None
    # Distinguish eviction from never-existed
    if state_id < _state_next_id:
        return None, (
            f"State {state_id} expired: it aged out of the LRU table (no calls "
            f"to from_state={state_id} while many other states were active), or "
            f"pet was restarted (auto-recovery from a timeout or crash, or a "
            f"peer caller's force_restart=True).  Call rocq_start to begin a "
            f"fresh session — you do not need force_restart=True unless this "
            f"expiry repeats."
        )
    return None, f"State {state_id} does not exist."


def _state_invalidate_all() -> None:
    """Clear all states (called on pet crash/invalidation)."""
    _state_table.clear()


def _resolve_check_base_state(
    from_state: int,
) -> tuple["_StateEntry | None", int | None, str | None]:
    """Resolve the base state for ``run_check`` / friends.

    Returns ``(entry, base_state_id, error_message)``.  Exactly one of
    *error_message* / ``(entry, base_state_id)`` is set.  ``from_state``
    is required — there is no implicit "current state" fallback, which
    avoids a peer-caller hazard in shared-process deployments.
    """
    entry, err = _state_get_or_error(from_state)
    if err:
        return None, None, err
    return entry, from_state, None


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


@dataclass(frozen=True)
class _TacticPathResult:
    """Outcome of walking the ``parent_id`` chain back from a leaf state.

    ``tactics`` is in root→leaf order and is only meaningful when
    ``status == "complete"``.  On a broken walk it holds whatever was
    collected before the break; the caller should not surface it as a
    finished tactic chain.

    ``status`` is one of:

    - ``"complete"`` — walk reached the root (``parent_id`` is ``None``)
    - ``"ancestor_evicted"`` — an ancestor entry was missing from the
      state table (LRU eviction or pet restart)
    - ``"cycle"`` — a ``current_id`` reappeared during the walk

    ``broken_at`` is the ``current_id`` at the break point in the
    ``ancestor_evicted`` / ``cycle`` cases, and ``None`` when complete.
    """

    tactics: list[str]
    status: Literal["complete", "ancestor_evicted", "cycle"]
    broken_at: int | None


def _reconstruct_tactic_path(state_id: int) -> _TacticPathResult:
    """Return the root->leaf command path for *state_id*.

    Since every ``_StateEntry`` materializes its cumulative
    ``tactic_path`` at creation, the chain survives LRU eviction of
    ancestors — the walk-the-parents failure modes (``ancestor_evicted``
    mid-chain, ``cycle``) are structurally gone.  The only remaining
    break is the leaf itself missing from the table (evicted or pet
    restarted), reported as ``ancestor_evicted`` at *state_id* for
    contract continuity.
    """
    entry = _state_get(state_id)
    if entry is None:
        return _TacticPathResult(
            tactics=[], status="ancestor_evicted", broken_at=state_id
        )
    return _TacticPathResult(
        tactics=list(entry.tactic_path), status="complete", broken_at=None
    )


_DECL_KEYWORDS = (
    "Theorem",
    "Lemma",
    "Fact",
    "Remark",
    "Corollary",
    "Proposition",
    "Property",
    "Example",
)
_DECL_RE = re.compile(rf"^\s*({'|'.join(_DECL_KEYWORDS)})\b")


def _recover_statement(
    entry: _StateEntry, tactics: list[str]
) -> tuple[str | None, str]:
    """Best-effort ``(statement, statement_source)`` for a finished proof.

    - theorem-mode sessions: extract the declaration sentence from the
      session's ``.v`` file (``statement_source="file"``).
    - preamble-mode sessions: the statement is one of the session
      commands (``"session_commands"``).
    - otherwise ``(None, "unrecoverable")`` — e.g. position-mode starts.
    """
    theorem = entry.theorem or ""
    if (
        entry.resolved_file
        and theorem
        and not theorem.startswith("@pos(")
        and theorem != "<preamble>"
    ):
        try:
            source = Path(entry.resolved_file).read_text()
        except OSError:
            source = None
        if source is not None:
            name_re = re.compile(
                rf"^\s*({'|'.join(_DECL_KEYWORDS)})\s+{re.escape(theorem)}\b"
            )
            for sentence in _split_rocq_sentences(source):
                if name_re.match(sentence.strip()):
                    return sentence.strip(), "file"
    for command in tactics:
        if _DECL_RE.match(command):
            return command.strip(), "session_commands"
    return None, "unrecoverable"


_PROOF_CLOSERS = ("Qed.", "Defined.", "Admitted.", "Abort.", "Save.")


def _assemble_proof_script(entry: _StateEntry, tactics: list[str]) -> dict[str, Any]:
    """Build ``{proof_script?, statement?, statement_source}``.

    The script is the ready-to-paste declaration + ``Proof.`` + tactic
    body + ``Qed.``; preamble-mode sessions additionally prepend the
    session's import commands so the script is self-contained.
    """
    statement, source_kind = _recover_statement(entry, tactics)
    if statement is None:
        return {"statement_source": source_kind}

    if source_kind == "session_commands":
        split = tactics.index(statement) if statement in tactics else 0
        preamble_cmds = tactics[:split]
        body = tactics[split + 1 :]
    else:
        preamble_cmds = []
        body = list(tactics)

    # Normalize: the agent may have run "Proof." / a closer explicitly.
    if body and body[0].strip() == "Proof.":
        body = body[1:]
    closer = "Qed."
    if body and body[-1].strip() in _PROOF_CLOSERS:
        closer = body[-1].strip()
        body = body[:-1]

    lines: list[str] = []
    if preamble_cmds:
        lines.extend(cmd.strip() for cmd in preamble_cmds)
        lines.append("")
    lines.append(statement)
    lines.append("Proof.")
    lines.extend(f"  {t.strip()}" for t in body)
    lines.append(closer)
    return {
        "proof_script": "\n".join(lines) + "\n",
        "statement": statement,
        "statement_source": source_kind,
    }


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


def _query_context_state(
    pet: Any,
    *,
    tool: str,
    file: str,
    preamble: str,
    from_state: int | None,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> tuple[Any, int | None, str | None] | dict[str, Any]:
    """Resolve the environment state for a query-style tool.

    Same three modes as ``rocq_query`` (from_state > file > preamble).
    Returns ``(state, from_state_id, stale_warning)`` on success, or a
    failure-envelope dict.  Callers run under ``_run_with_pet``.
    """
    if from_state is not None:
        entry, base_id, err = _resolve_check_base_state(from_state)
        if err or entry is None:
            return _server._fail(
                lifespan_state, tool, err or f"State {from_state} not found."
            )
        return entry.state, base_id, _check_staleness(entry)
    if file:
        try:
            return (
                _get_file_end_state(pet, file, workspace, lifespan_state),
                None,
                None,
            )
        except (ValueError, FileNotFoundError) as e:
            return _server._fail(lifespan_state, tool, str(e))
    preamble_text = preamble.strip()
    preamble_cmds = _split_rocq_sentences(preamble_text) if preamble_text else []
    return (
        _get_or_create_import_state(pet, workspace, preamble_cmds, lifespan_state),
        None,
        None,
    )


@collects_degraded
async def run_query(
    command: str,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    file: str = "",
    max_results: int | None = None,
    *,
    include_warnings: bool = True,
    timeout: float | None = None,
    from_state: int | None = None,
    auto_record: bool = True,
) -> dict[str, Any]:
    """Core implementation of rocq_query (testable without FastMCP Context).

    Three modes (mutually exclusive):
    - **preamble mode**: import commands set up the environment (cached).
    - **file mode**: a ``.v`` file provides the full environment.
    - **from_state mode**: a live state from the state-table (e.g. mid-
      ``rocq_check``) provides the full proof context — opened scopes,
      hypotheses, local definitions.  The transient child state produced
      by the query is discarded; the parent state-table entry stays
      unchanged.

    When *file* is given, uses :func:`_get_file_end_state` to obtain a
    state at the end of the file where all definitions are in scope.

    When *from_state* is given, the live state is resolved via
    :func:`_resolve_check_base_state`; eviction / non-existence yields a
    validation failure pointing the caller to ``rocq_start``.  The
    response is augmented with ``from_state_id`` so the caller can
    confirm which state was queried.

    When ``include_warnings=False``, drops feedback entries at LSP
    Warning severity (level 2) before counting / returning.

    ``timeout`` (when not ``None``) is forwarded explicitly to
    :func:`_run_with_pet`; otherwise the helper falls back to
    ``lifespan_state["pet_timeout"]``.  Caller (the MCP wrapper) is
    expected to apply ``ROCQ_QUERY_TIMEOUT_CAP``.

    When ``auto_record=False``, pet-side failures (timeout, crashed,
    lock_contended, ...) still propagate as the usual failure-envelope
    dict but skip the ``recent_errors`` push.  Used by ``run_assumptions``
    so it can record once at its own layer with the right tool/reason
    attribution.
    """
    if file and from_state is not None:
        return _server._fail(
            lifespan_state,
            "rocq_query",
            "Provide either 'file' or 'from_state', not both.",
        )
    if from_state is not None and preamble.strip():
        # Silent preamble drop would mislead the caller — fail loudly so
        # they understand the live state already provides the context.
        return _server._fail(
            lifespan_state,
            "rocq_query",
            "preamble is not used in from_state mode; the live state already "
            "provides the context.",
        )
    if from_state is None and file and preamble.strip():
        return _server._fail(
            lifespan_state,
            "rocq_query",
            "Provide either 'file' or 'preamble', not both.",
        )

    forbidden = _check_forbidden_commands(command)
    if forbidden:
        return _server._fail(lifespan_state, "rocq_query", forbidden)
    # In from_state mode, the preamble is irrelevant — skip its scan.
    if not file and from_state is None:
        forbidden = _check_forbidden_commands(preamble)
        if forbidden:
            return _server._fail(lifespan_state, "rocq_query", forbidden)

    def _do_query(pet: Any) -> dict[str, Any]:
        resolved = _query_context_state(
            pet,
            tool="rocq_query",
            file=file,
            preamble=preamble,
            from_state=from_state,
            workspace=workspace,
            lifespan_state=lifespan_state,
        )
        if isinstance(resolved, dict):
            return resolved
        state, from_state_id, stale_warning = resolved

        cmd = command.strip()
        if not cmd.endswith("."):
            cmd += "."
        state = pet.run(state, cmd)
        feedback = state.feedback or []
        if not include_warnings:
            feedback = [
                (lvl, msg) for lvl, msg in feedback if lvl != _LSP_SEVERITY_WARNING
            ]

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
        resp: dict[str, Any] = {"success": True, "output": output or "(no output)"}
        if from_state_id is not None:
            resp["from_state_id"] = from_state_id
        if stale_warning:
            resp["stale_warning"] = stale_warning
        return resp

    return await _server._run_with_pet(
        _do_query,
        lifespan_state,
        "rocq_query",
        timeout=timeout,
        auto_record=auto_record,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_search (structured Search)
# ---------------------------------------------------------------------------

#: One Search hit per feedback message: ``name: type`` (type may wrap
#: across lines).  Unparseable messages are kept as raw hits.
_SEARCH_HIT_RE = re.compile(r"^([^\s:]+)\s*:\s*(.*)$", re.DOTALL)

_SEARCH_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")
_MAX_SEARCH_PATTERNS = 8


def _build_search_command(
    pat: str, kind: str, inside: list[str], outside: list[str]
) -> str:
    parts = ["Search"]
    if kind:
        parts.append(f"is:{kind}")
    parts.append(pat.strip().rstrip("."))
    if inside:
        parts.append("inside " + " ".join(inside))
    if outside:
        parts.append("outside " + " ".join(outside))
    return " ".join(parts) + "."


@collects_degraded
async def run_search(
    pattern: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    *,
    patterns: list[str] | None = None,
    kind: str = "",
    inside: list[str] | None = None,
    outside: list[str] | None = None,
    preamble: str = "",
    file: str = "",
    from_state: int | None = None,
    max_results: int = 30,
    offset: int = 0,
    include_types: bool = True,
    include_warnings: bool = True,
    timeout: float | None = None,
) -> dict[str, Any]:
    """Structured ``Search``: parsed hits, filters, fan-out, pagination.

    Each Coq Search hit arrives as its own feedback message, so parsing
    is per-message (``name: type``), not blob regexing.  With multiple
    *patterns*, hits are merged and deduplicated by name, and each hit
    records which patterns matched it (``matched_patterns``) — a cheap
    premise-ranking signal.

    Coq rejecting the Search syntax surfaces as ``reason:
    "query_rejected"`` with the offending command in the message.
    """
    all_patterns = [pat for pat in [pattern, *(patterns or [])] if pat and pat.strip()]
    if not all_patterns:
        return _server._fail(
            lifespan_state, "rocq_search", "Provide a non-empty pattern."
        )
    if len(all_patterns) > _MAX_SEARCH_PATTERNS:
        return _server._fail(
            lifespan_state,
            "rocq_search",
            f"Too many patterns: {len(all_patterns)} exceeds "
            f"{_MAX_SEARCH_PATTERNS}.",
        )
    if kind and not _SEARCH_IDENT_RE.match(kind):
        return _server._fail(lifespan_state, "rocq_search", f"Invalid kind {kind!r}.")
    for module in (inside or []) + (outside or []):
        if not _SEARCH_IDENT_RE.match(module):
            return _server._fail(
                lifespan_state, "rocq_search", f"Invalid module name {module!r}."
            )
    if max_results < 1:
        return _server._fail(lifespan_state, "rocq_search", "max_results must be >= 1.")
    if offset < 0:
        return _server._fail(lifespan_state, "rocq_search", "offset must be >= 0.")
    if file and from_state is not None:
        return _server._fail(
            lifespan_state,
            "rocq_search",
            "Provide either 'file' or 'from_state', not both.",
        )
    if from_state is not None and preamble.strip():
        return _server._fail(
            lifespan_state,
            "rocq_search",
            "preamble is not used in from_state mode; the live state already "
            "provides the context.",
        )
    if from_state is None and file and preamble.strip():
        return _server._fail(
            lifespan_state,
            "rocq_search",
            "Provide either 'file' or 'preamble', not both.",
        )

    commands = [
        _build_search_command(pat, kind, inside or [], outside or [])
        for pat in all_patterns
    ]
    for cmd in commands + ([preamble] if preamble.strip() else []):
        forbidden = _check_forbidden_commands(cmd)
        if forbidden:
            return _server._fail(lifespan_state, "rocq_search", forbidden)

    multi = len(all_patterns) > 1

    def _do_search(pet: Any) -> dict[str, Any]:
        try:
            from pytanque import PetanqueError
        except ImportError:
            return {
                "success": False,
                "error": _server._PYTANQUE_NOT_INSTALLED_HINT,
            }

        resolved = _query_context_state(
            pet,
            tool="rocq_search",
            file=file,
            preamble=preamble,
            from_state=from_state,
            workspace=workspace,
            lifespan_state=lifespan_state,
        )
        if isinstance(resolved, dict):
            return resolved
        state, from_state_id, stale_warning = resolved

        # name/raw-key -> {"name"|"raw", "type", "patterns"} in first-seen order
        merged: dict[str, dict[str, Any]] = {}
        for pat, cmd in zip(all_patterns, commands, strict=True):
            try:
                result_state = pet.run(state, cmd)
            except PetanqueError as e:
                if not _server._pet_alive(lifespan_state.get("pet_client")):
                    raise
                return _server._fail(
                    lifespan_state,
                    "rocq_search",
                    f"Coq rejected {cmd!r}: {e.message}",
                    reason="query_rejected",
                )
            feedback = result_state.feedback or []
            if not include_warnings:
                feedback = [
                    (lvl, msg) for lvl, msg in feedback if lvl != _LSP_SEVERITY_WARNING
                ]
            for _, msg in feedback:
                text = (msg or "").strip()
                if not text:
                    continue
                match = _SEARCH_HIT_RE.match(text)
                if match:
                    key = match.group(1)
                    entry = merged.setdefault(
                        key,
                        {"name": key, "type": match.group(2).strip(), "patterns": []},
                    )
                else:
                    key = text
                    entry = merged.setdefault(
                        key, {"raw": text, "type": None, "patterns": []}
                    )
                if pat not in entry["patterns"]:
                    entry["patterns"].append(pat)

        order = list(merged)
        total = len(order)
        window = order[offset : offset + max_results]
        hits: list[dict[str, Any]] = []
        for key in window:
            entry = merged[key]
            hit: dict[str, Any] = {}
            if "name" in entry:
                hit["name"] = entry["name"]
                if include_types and entry["type"]:
                    hit["type"] = _cap_type(entry["type"])
            else:
                hit["raw"] = _cap_type(entry["raw"])
            if multi:
                hit["matched_patterns"] = entry["patterns"]
            hits.append(hit)

        resp: dict[str, Any] = {
            "success": True,
            "hits": hits,
            "total": total,
            "offset": offset,
            "truncated": offset + len(hits) < total,
            "query": commands if multi else commands[0],
        }
        if from_state_id is not None:
            resp["from_state_id"] = from_state_id
        if stale_warning:
            resp["stale_warning"] = stale_warning
        return resp

    return await _server._run_with_pet(
        _do_search,
        lifespan_state,
        "rocq_search",
        timeout=timeout,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_goal (stateless goal inspection)
# ---------------------------------------------------------------------------


@collects_degraded
async def run_goal(
    lifespan_state: dict[str, Any],
    *,
    from_state: int | None = None,
    file: str = "",
    line: int | None = None,
    character: int | None = None,
    workspace: str = "",
    goals_format: str = "pretty",
    diff_from: int | None = None,
    timeout: float | None = None,
) -> dict[str, Any]:
    """Show goals at a live state_id or a file position — registers no state.

    Unlike ``rocq_start`` in position mode, this never allocates a
    ``state_id``: pure inspection with zero LRU-table footprint.
    ``diff_from`` (with ``from_state``) returns the delta between two
    live states instead of full goals.
    """
    if goals_format not in GOALS_RENDER_FORMATS:
        return _server._fail(
            lifespan_state,
            "rocq_goal",
            f"Invalid goals_format {goals_format!r}; expected one of "
            "pretty | structured | names_only.",
        )
    by_state = from_state is not None
    by_pos = bool(file) and line is not None and character is not None
    if by_state == by_pos:
        return _server._fail(
            lifespan_state,
            "rocq_goal",
            "Provide either from_state, or file+line+character (not both).",
        )
    if diff_from is not None and not by_state:
        return _server._fail(
            lifespan_state, "rocq_goal", "diff_from requires from_state."
        )

    resolved_file = ""
    if by_pos:
        if not (0 <= line <= _MAX_LINE_CHAR_RANGE) or not (
            0 <= character <= _MAX_LINE_CHAR_RANGE
        ):
            return _server._fail(
                lifespan_state,
                "rocq_goal",
                f"line and character must be in range [0, {_MAX_LINE_CHAR_RANGE}].",
            )
        try:
            resolved_file = _server._resolve_file_in_workspace(file, workspace)
        except (ValueError, FileNotFoundError) as e:
            return _server._fail(lifespan_state, "rocq_goal", str(e))

    def _do_goal(pet: Any) -> dict[str, Any]:
        stale_warning: str | None = None
        if by_state:
            entry, base_id, err = _resolve_check_base_state(from_state)
            if err or entry is None:
                return _server._fail(
                    lifespan_state, "rocq_goal", err or "State not found."
                )
            state = entry.state
            stale_warning = _check_staleness(entry)
            from_state_id: int | None = base_id
        else:
            _server._set_workspace_if_needed(pet, workspace, lifespan_state)
            state = pet.get_state_at_pos(resolved_file, line, character)
            from_state_id = None

        complete = pet.complete_goals(state)
        goals_list = complete.goals if complete else []

        resp: dict[str, Any] = {
            "success": True,
            "stateless": True,
            "proof_finished": getattr(state, "proof_finished", False),
            "goals_count": len(goals_list),
        }
        if diff_from is not None:
            other, _, err2 = _resolve_check_base_state(diff_from)
            if err2 or other is None:
                return _server._fail(
                    lifespan_state, "rocq_goal", err2 or "diff_from state not found."
                )
            other_complete = pet.complete_goals(other.state)
            other_goals = other_complete.goals if other_complete else []
            resp["goals_diff"] = _goals_diff(other_goals, goals_list)
        elif goals_format == "pretty":
            resp["goals"] = _format_goals(goals_list) or "No goals remaining."
        else:
            resp["goals"] = _render_goals(goals_list, goals_format)
        depth = _focus_depth(complete)
        if depth is not None:
            resp["focus_depth"] = depth
        if complete and complete.shelf:
            resp["shelved_goals"] = len(complete.shelf)
        if complete and complete.given_up:
            resp["given_up_goals"] = len(complete.given_up)
        if from_state_id is not None:
            resp["from_state_id"] = from_state_id
        if stale_warning:
            resp["stale_warning"] = stale_warning
        return resp

    return await _server._run_with_pet(
        _do_goal,
        lifespan_state,
        "rocq_goal",
        timeout=timeout,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_assumptions
# ---------------------------------------------------------------------------

# Matches Coq's per-file opaque-proof loader notices, one per line.  Stripped
# from ``raw_output`` before parse so the response is dominated by the actual
# ``Print Assumptions`` answer rather than the loader preamble.  Coq emits at
# least two suffix shapes after the literal prefix: ``for <module>`` (older
# builds) and ``: <module>`` (current).  Matching the prefix only — without
# requiring a specific delimiter — covers both; safe because no real Coq
# identifier can start with these words (identifiers disallow whitespace).
_OPAQUE_FETCH_NOTICE_RE = re.compile(
    r"^Fetching opaque proofs from disk[^\n]*\n",
    re.MULTILINE,
)


@collects_degraded
async def run_assumptions(
    name: str,
    file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    *,
    timeout: float | None = None,
    include_raw: bool = False,
) -> dict[str, Any]:
    """Core implementation of rocq_assumptions (testable without FastMCP Context).

    Runs ``Print Assumptions <name>.`` via :func:`run_query` in file mode
    and returns the parsed assumption list verbatim.  No classification —
    the agent decides what's safe to trust.  For an axiom-policy *verdict*
    (accept standard mathematical axioms, reject custom ones) prefer
    ``rocq_verify``; this tool is pure introspection.

    The *file* parameter is required — it provides the ``.v`` file where the
    theorem is defined, so the query runs in a context where all definitions
    from that file are in scope.  This eliminates shadowing ambiguity that
    plagued the old preamble-based approach.

    Returns a dict containing:

        * ``success``           — bool.
        * ``theorem``           — the cleaned theorem name.
        * ``assumptions``       — list[str] of ``"name : type"`` pairs from
          ``Print Assumptions``.  Empty when the theorem is closed.
        * ``raw_output``        — raw ``Print Assumptions`` output with
          ``Fetching opaque proofs from disk ...`` loader notices stripped
          (Coq emits either a ``for <module>`` or ``: <module>`` suffix;
          both are filtered).  Those are Coq's per-file load notices,
          not part of the assumptions answer.
    """
    from rocq_mcp.verify import _parse_assumptions_raw, is_rocq_qualified_name

    # Validate file parameter
    if not file or not file.strip():
        return _server._fail(
            lifespan_state, "rocq_assumptions", "File parameter is required."
        )

    # Validate: non-empty, valid Rocq identifier or qualified name.
    clean_name = name.strip() if name else ""
    if not clean_name:
        return _server._fail(
            lifespan_state, "rocq_assumptions", "Theorem name must not be empty."
        )
    if not is_rocq_qualified_name(clean_name):
        return _server._fail(
            lifespan_state,
            "rocq_assumptions",
            (
                f"Invalid identifier: {clean_name!r}. "
                "Expected a Rocq name like 'add_comm' or 'Nat.add_comm'."
            ),
        )

    # auto_record=False lets us classify the failure once at the
    # rocq_assumptions layer below: a typo against a valid file becomes
    # ``not_found``; everything else inherits the underlying reason but
    # under our tool name.  Without this, _run_with_pet would push the
    # generic ``rocq_query/crashed`` first and we'd have to pop-and-
    # re-push to fix the attribution.
    query_result = await run_query(
        command=f"Print Assumptions {clean_name}.",
        preamble="",
        workspace=workspace,
        lifespan_state=lifespan_state,
        file=file,
        timeout=timeout,
        auto_record=False,
    )
    if not query_result.get("success"):
        # Best-effort enrichment: attach the file's symbol list so the
        # agent can fuzzy-match a misspelled name without a separate tool
        # call.  Skip when ``available_in_file`` is already present (e.g.
        # if a future caller pre-attached one) and when the file path
        # cannot be resolved.
        #
        # Gate the enrichment on non-transport failures.  Two ways to be
        # a "transport failure":
        #   * reason in {timeout, lock_contended, unavailable,
        #     memory_exhausted}; or
        #   * reason == "crashed" *and* ``pet_restarted`` is True (the
        #     pet process actually died — see ``_run_with_pet``).
        # A bare ``reason == "crashed"`` without ``pet_restarted`` is a
        # live PetanqueError (typically a Coq "Reference X not found"
        # error from a typo'd theorem name) — exactly the case the
        # enrichment exists to help with, so we DO run it.
        reason = query_result.get("reason")
        pet_restarted = query_result.get("pet_restarted") is True
        is_transport_failure = (
            reason in _TRANSPORT_FAILURE_REASONS and reason != "crashed"
        ) or (reason == "crashed" and pet_restarted)
        retagged_not_found = False
        if "available_in_file" not in query_result and not is_transport_failure:
            result = await _fetch_available_in_file(
                file=file,
                workspace=workspace,
                lifespan_state=lifespan_state,
                tool="rocq_assumptions",
            )
            _attach_available_in_file(query_result, result)
            if result.names:
                # Non-empty names means the file IS valid; the failure
                # was about the requested name (a typo).  Re-tag as
                # ``not_found`` so ``rocq_diag`` reports it correctly
                # rather than as the generic ``crashed`` reason
                # ``_run_with_pet`` would have set on a Coq error.
                if query_result.get("reason") != "not_found":
                    query_result["reason"] = "not_found"
                    retagged_not_found = True
        final_reason = query_result.get("reason") or "crashed"
        # Idempotency: when reason is already ``not_found`` from the
        # inner layer (a future ``run_query`` classification) and we
        # did not retag here, skip the record to mirror the legacy
        # behavior tested by
        # ``test_typo_failure_no_double_record_when_reason_already_not_found``.
        if final_reason != "not_found" or retagged_not_found:
            _server._record_error(
                lifespan_state,
                "rocq_assumptions",
                query_result.get("error", ""),
                reason=final_reason,
            )
        return query_result

    # Strip the opaque-proof loader notices that Coq emits before the
    # actual ``Print Assumptions`` output.  On mathcomp-flavored proofs
    # they can outweigh the answer 20:1 ("Fetching opaque proofs from disk
    # for mathcomp.X..." × dozens of files), pushing the Axioms: block
    # past response-truncation thresholds.  Pure cosmetic strip; the lines
    # are Notice-level feedback, never part of the assumptions list.
    raw_output = _OPAQUE_FETCH_NOTICE_RE.sub("", query_result["output"])
    try:
        pairs = _parse_assumptions_raw(raw_output)
    except Exception as e:
        # Parser blew up on Print Assumptions output we didn't expect
        # (future Rocq format change, unusual identifier shape, …).
        # Tag as "crashed" because the failure is below our layer; the
        # alternatives (validation, not_found) don't fit — this isn't
        # user input that failed validation.
        msg = f"Failed to parse assumptions output: {e}"
        _server._record_error(lifespan_state, "rocq_assumptions", msg, reason="crashed")
        return {
            "success": False,
            "reason": "crashed",
            "error": msg,
            "raw_output": raw_output,
        }
    result = {
        "success": True,
        "theorem": clean_name,
        "assumptions": [f"{name} : {ty}" for name, ty in pairs],
    }
    # The parsed list and the raw output are ~1:1 redundant on success;
    # the raw text is opt-in.  (Parse failures above keep raw_output
    # unconditionally — there it IS the payload.)
    if include_raw:
        result["raw_output"] = raw_output
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


# ---------------------------------------------------------------------------
# TOC name cache (used by `available_in_file` enrichment on not-found failures)
# ---------------------------------------------------------------------------

# Cache for ``pet.toc`` name lists keyed by ``(resolved_file, mtime)``.  Bounded
# at :data:`_TOC_CACHE_MAX` entries with FIFO eviction so long sessions do not
# accumulate stale ``.v`` files.  An mtime change naturally invalidates the
# entry (different key).  Best-effort: any error in extraction yields ``[]``
# and no field is attached on the failure path.
_TOC_CACHE: dict[tuple[str, float], list[str]] = {}
_TOC_CACHE_MAX: int = 50


# pet.toc flattens Module hierarchy: members of `Module M.` are emitted at
# top level with their bare name (`foo`), not the addressable qualified
# form (`M.foo`).  We reconstruct the path by scanning the source for
# `Module X.` / `End X.` lines and intersecting with each element's range.
# Sections do NOT introduce a namespace qualifier in Coq, so they are
# excluded from the prefix.  Module Type DOES qualify members.
_MODULE_OPEN_RE = re.compile(r"^\s*Module\s+(?:Type\s+)?([A-Z][A-Za-z0-9_']*)\b")
_MODULE_END_RE = re.compile(r"^\s*End\s+([A-Z][A-Za-z0-9_']*)\s*\.")


def _scan_module_regions(source: str) -> list[tuple[int, int, str]]:
    """Return ``(start_line, end_line, name)`` for each Module/Module Type
    block in *source*.  Lines are 0-based to match coq-lsp ranges.

    Comment- and string-safe via :func:`verify._neutralize_for_regex`
    (length-preserving so line numbers survive).  A region is emitted
    only when a matching ``End <Name>.`` is seen.

    Declarative one-liners (``Module M : MT.``, ``Module M := SomeMod.``)
    have no body and no closing ``End``.  The opener regex matches them
    indistinguishably from a real opener, so they get pushed onto the
    stack.  When a later ``End <Outer>.`` fires we scan the stack
    top-down for the matching name and pop everything down to and
    including it — discarding the intervening one-liner pushes.  Without
    this, an inner declarative one-liner would silently corrupt the
    parent's qualifier (the audit reproducer was
    ``Module Outer. Module M : MT. Module Sibling. … End Sibling. End Outer.``
    where ``Outer`` was being dropped from regions and ``Sibling.x``
    would be qualified bare instead of as ``Outer.Sibling.x``).
    """
    from rocq_mcp.verify import _neutralize_for_regex

    cleaned = _neutralize_for_regex(source)
    open_stack: list[tuple[int, str]] = []
    regions: list[tuple[int, int, str]] = []
    for i, line in enumerate(cleaned.split("\n")):
        m = _MODULE_OPEN_RE.match(line)
        if m:
            open_stack.append((i, m.group(1)))
            continue
        e = _MODULE_END_RE.match(line)
        if not (e and open_stack):
            continue
        target = e.group(1)
        for j in range(len(open_stack) - 1, -1, -1):
            if open_stack[j][1] == target:
                top_line, _ = open_stack[j]
                del open_stack[j:]
                regions.append((top_line, i, target))
                break
    return regions


def _module_prefix_for_line(regions: list[tuple[int, int, str]], line: int) -> str:
    """Return the dot-prefix for an element at *line* (0-based).

    For nested ``Module Outer. Module Inner. … End Inner. End Outer.``,
    a definition inside ``Inner`` returns ``"Outer.Inner."``.  Returns
    the empty string when *line* is outside every region.
    """
    enclosing = [(s, name) for (s, e, name) in regions if s < line < e]
    if not enclosing:
        return ""
    enclosing.sort(key=lambda r: r[0])
    return ".".join(name for _, name in enclosing) + "."


def _collect_toc_names(toc_result: Any, source: str = "") -> list[str]:
    """Flatten a ``pet.toc`` tree into a list of addressable definition names.

    ``pet.toc`` returns ``list[(section_name, list[TocElement])]``; each
    element has ``elem.name.v`` (the identifier) plus optional nested
    ``children``.

    Filters Notation/Infix entries: their ``name.v`` is a syntax key
    like ``"x + y"``, useless as a ``name=`` argument to subsequent
    calls.

    When *source* is provided, qualifies Module members by prefixing
    them with the enclosing path (``foo`` → ``Outer.Inner.foo``).  Pet
    flattens Module structure away in its own output; we reconstruct
    it from the source using element line ranges.  Without *source*,
    returns bare names (callers like the unit tests pass mocked
    elements with no real source attached).
    """
    from rocq_mcp.verify import _NOTATION_DETAILS

    regions = _scan_module_regions(source) if source else []
    names: list[str] = []

    def _walk(elements: list[Any]) -> None:
        for elem in elements:
            detail = getattr(elem, "detail", "") or ""
            if detail in _NOTATION_DETAILS:
                continue
            name = elem.name.v if elem.name else None
            if name:
                prefix = ""
                if regions and elem.range is not None:
                    prefix = _module_prefix_for_line(regions, elem.range.start.line)
                names.append(f"{prefix}{name}")
            if elem.children:
                _walk(elem.children)

    if toc_result:
        for _section_name, elements in toc_result:
            _walk(elements)
    return names


def _toc_names_cached(pet: Any, resolved_file: str) -> list[str]:
    """Return sorted addressable names in ``resolved_file`` via ``pet.toc``,
    cached by ``(file, mtime)``.

    Returns an empty list on any error (best-effort enrichment) and does
    *not* cache the failure — a transient pet hiccup should not poison
    the cache for the rest of the session.  Bounded to
    :data:`_TOC_CACHE_MAX` entries with FIFO eviction on success.
    """
    try:
        mtime = os.path.getmtime(resolved_file)
    except OSError:
        return []
    key = (resolved_file, mtime)
    if key in _TOC_CACHE:
        return _TOC_CACHE[key]
    try:
        toc_result = pet.toc(resolved_file)
        try:
            source = Path(resolved_file).read_text()
        except OSError:
            source = ""
        names = sorted(_collect_toc_names(toc_result, source=source))
    except Exception as e:
        # Do not cache failures: caller will retry next time.
        note_degraded("available_in_file:toc_failed", repr(e))
        return []
    if len(_TOC_CACHE) >= _TOC_CACHE_MAX:
        # Evict the oldest (insertion-order).
        _TOC_CACHE.pop(next(iter(_TOC_CACHE)))
    _TOC_CACHE[key] = names
    return names


_DEFAULT_TOC_LIMIT: int = 500


# Reasons that indicate the pet itself is stressed/dead.  When
# ``run_query`` failed for one of these, the ``available_in_file``
# enrichment skips the extra ``pet.toc`` call: the failure was not
# about the requested name and the pet should not be hammered further.
#
# ``"crashed"`` is intentionally listed here for the *transport* sense
# (pet process died, indicated by ``pet_restarted: True``).  It is also
# the reason ``_run_with_pet`` records for a *live* PetanqueError —
# typically a Coq error such as ``Reference foo not found.`` — where
# enrichment IS useful.  The runtime gate (in ``run_assumptions``)
# treats those two cases differently using ``pet_restarted``.
#
# This set is a strict subset of :data:`taxonomy.RECENT_ERROR_REASONS`
# (the larger set also includes validation-only and tool-specific
# values like ``"not_found"`` / ``"tactic_failed"``).  Derived from the
# shared :data:`taxonomy.PET_SIDE_FAILURE_REASONS` — the canonical set,
# derived from taxonomy.FailureReason, so the subset invariant across
# the reason-sets holds by construction (no import-time assert needed).
_TRANSPORT_FAILURE_REASONS: frozenset[str] = taxonomy.PET_SIDE_FAILURE_REASONS


def _truncate_names(
    names: list[str], limit: int = _DEFAULT_TOC_LIMIT
) -> tuple[list[str], bool]:
    """Cap *names* at *limit*; return ``(capped, truncated_flag)``.

    Lexicographic windowing on the requested name is the wrong recovery
    model for typos: a one-character difference at position 0 (e.g.
    ``fool_bound`` vs ``fuel_bound``) places the window in a different
    bucket than the target.  A simple first-N cap with a truncation
    marker lets the agent see the whole list for typical files
    (≤ ``limit`` definitions) and a clearly-marked prefix plus a
    pointer to ``rocq_toc`` for pathological large files.
    """
    if len(names) <= limit:
        return names, False
    return names[:limit], True


class _AvailableInFile(NamedTuple):
    """Result of :func:`_fetch_available_in_file` — the capped name list,
    a flag indicating whether ``names`` was truncated relative to the file,
    and the total count of names found in the file before truncation.

    Using a NamedTuple instead of a bare ``tuple[list[str], bool, int]``
    eliminates positional misorder bugs at the call sites (which juggle
    truncation-marker fields conditionally) while staying ``isinstance``-
    compatible with plain tuples.
    """

    names: list[str]
    truncated: bool
    total: int


def _attach_available_in_file(resp: dict[str, Any], result: _AvailableInFile) -> None:
    """Add ``available_in_file*`` recovery hints to a failure response.

    No-op when *result* is empty (the helper returned no names — keeps
    the failure response unchanged).  Used by both ``run_assumptions``
    and ``_build_theorem_start_result`` so the enrichment shape is
    identical across the two not-found flows.
    """
    if not result.names:
        return
    resp["available_in_file"] = result.names
    if result.truncated:
        resp["available_in_file_truncated"] = True
        resp["available_in_file_total"] = result.total
        resp["available_in_file_limit"] = _DEFAULT_TOC_LIMIT


async def _fetch_available_in_file(
    *,
    file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    tool: str,
) -> _AvailableInFile:
    """Async wrapper that fetches the (capped) name list for *file*.

    Resolves *file* against *workspace*, runs ``pet.toc`` (cached) under
    the pet lock, and returns an :class:`_AvailableInFile` with
    ``names``, ``truncated``, and ``total``.  On any error returns an
    empty result (``names=[]``, ``truncated=False``, ``total=0``) —
    this is best-effort enrichment that must never break the primary
    failure response.

    *tool* is forwarded to ``_run_with_pet`` so any pet-level failure
    during the toc lookup is attributed to the calling tool in
    ``recent_errors``.  Required (no default) because there is no
    sensible fallback — silently mis-attributing a future caller's
    failure to ``rocq_assumptions`` would be a bug.
    """
    try:
        resolved = _server._resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError, OSError):
        return _AvailableInFile([], False, 0)

    def _do_toc(pet: Any) -> list[str]:
        return _toc_names_cached(pet, resolved)

    try:
        names = await _server._run_with_pet(
            _do_toc,
            lifespan_state,
            tool,
        )
    except Exception as e:
        note_degraded("available_in_file:pet_failed", repr(e))
        return _AvailableInFile([], False, 0)
    if not isinstance(names, list):
        # _run_with_pet returns a failure dict on errors; treat as empty.
        note_degraded(
            "available_in_file:pet_failed",
            str(names.get("reason")) if isinstance(names, dict) else None,
        )
        return _AvailableInFile([], False, 0)
    total = len(names)
    capped, truncated = _truncate_names(names)
    return _AvailableInFile(capped, truncated, total)


@collects_degraded
async def run_toc(
    file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    *,
    timeout: float | None = None,
) -> dict[str, Any]:
    """Core implementation of rocq_toc (testable without FastMCP Context).

    ``timeout`` (when not ``None``) is forwarded to :func:`_run_with_pet`;
    otherwise the helper falls back to ``lifespan_state["pet_timeout"]``.
    Caller (the MCP wrapper) is expected to apply ``ROCQ_QUERY_TIMEOUT_CAP``.
    """
    # Path traversal + existence check (before entering thread)
    try:
        file_path = _server._resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError) as e:
        return _server._fail(lifespan_state, "rocq_toc", str(e))

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
        "rocq_toc",
        timeout=timeout,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_notations
# ---------------------------------------------------------------------------


@collects_degraded
async def run_notations(
    statement: str,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    *,
    timeout: float | None = None,
) -> dict[str, Any]:
    """Core implementation of rocq_notations (testable without FastMCP Context).

    ``timeout`` (when not ``None``) is forwarded to :func:`_run_with_pet`;
    otherwise the helper falls back to ``lifespan_state["pet_timeout"]``.
    Caller (the MCP wrapper) is expected to apply ``ROCQ_QUERY_TIMEOUT_CAP``.
    """
    forbidden = _check_forbidden_commands(statement)
    if forbidden:
        return _server._fail(lifespan_state, "rocq_notations", forbidden)
    forbidden = _check_forbidden_commands(preamble)
    if forbidden:
        return _server._fail(lifespan_state, "rocq_notations", forbidden)

    _temp_files: list[str] = []

    def _do_notations(pet: Any) -> dict[str, Any]:
        _server._set_workspace_if_needed(pet, workspace, lifespan_state)
        ws = str(Path(workspace).resolve())

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
        "rocq_notations",
        on_timeout=_on_timeout,
        timeout=timeout,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_start
# ---------------------------------------------------------------------------

_MAX_STEP_MULTI_TACTICS = 20

#: The standard automation battery for ``rocq_step_multi(preset="auto")``,
#: cheapest first.  (Restores the convenience of the removed
#: ``rocq_auto_solve`` tool as a parameter instead of a tool slot.)
#: lia/lra/nia/nra/ring/field need the matching imports in scope.
_AUTO_SOLVE_TACTICS: tuple[str, ...] = (
    "trivial.",
    "reflexivity.",
    "assumption.",
    "exact I.",
    "auto.",
    "eauto.",
    "tauto.",
    "intuition.",
    "lia.",
    "lra.",
    "nia.",
    "nra.",
    "ring.",
    "field.",
    "decide equality.",
    "firstorder.",
)


def _build_position_start_result(
    pet: Any,
    *,
    file: str,
    resolved_file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    line: int,
    character: int,
    track_staleness: bool = True,
    goals_format: str = "pretty",
) -> dict[str, Any]:
    """Return the rocq_start-style payload for a position-based state.

    ``line`` / ``character`` are 0-indexed.  Petanque rounds the cursor
    forward through the sentence it lies in: a cursor on any character
    of a sentence (first letter through terminating period) yields the
    state AFTER that sentence; a cursor in the whitespace before a
    sentence yields the state BEFORE it.  See ``rocq_start`` for the
    full rule.
    """
    _server._set_workspace_if_needed(pet, workspace, lifespan_state)
    state = pet.get_state_at_pos(resolved_file, line, character)

    file_mtime: float | None = None
    tracked_file: str | None = None
    if track_staleness:
        try:
            file_mtime = os.path.getmtime(resolved_file)
        except OSError:
            file_mtime = None
        tracked_file = resolved_file

    theorem = f"@pos({line},{character})"
    state_id = _state_add(
        state=state,
        file=file,
        theorem=theorem,
        workspace=workspace,
        parent_id=None,
        tactic=None,
        step=0,
        file_mtime=file_mtime,
        resolved_file=tracked_file,
    )
    goals, focus_depth = _try_render_goals_with_depth(pet, state, goals_format)
    result: dict[str, Any] = {
        "success": True,
        "state_id": state_id,
        "goals": goals if goals is not None else "",
        "file": file,
        "theorem": theorem,
        "proof_finished": getattr(state, "proof_finished", False),
    }
    if focus_depth is not None:
        result["focus_depth"] = focus_depth
    return result


def _build_theorem_start_result(
    pet: Any,
    *,
    file: str,
    resolved_file: str,
    theorem: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    goals_format: str = "pretty",
) -> dict[str, Any]:
    """Return the rocq_start-style payload for a theorem-based state."""
    _server._set_workspace_if_needed(pet, workspace, lifespan_state)
    try:
        state = pet.start(resolved_file, theorem)
    except Exception as e:
        # Best-effort enrichment: when pet rejects ``theorem`` (typically
        # because no such name exists in *file*), attach the file's symbol
        # list so the agent can fuzzy-match without a separate tool call.
        # If pet died, re-raise so ``_run_with_pet`` reports
        # ``pet_restarted=True`` to the client.
        if _PetanqueError is not None and isinstance(e, _PetanqueError):
            if not _server._pet_alive(lifespan_state.get("pet_client")):
                raise
            try:
                all_names = _toc_names_cached(pet, resolved_file)
                capped, truncated = _truncate_names(all_names)
                avail = _AvailableInFile(capped, truncated, len(all_names))
            except Exception:
                avail = _AvailableInFile([], False, 0)
            resp: dict[str, Any] = {
                "success": False,
                "error": e.message,
                "reason": "not_found",
            }
            _attach_available_in_file(resp, avail)
            _server._record_error(
                lifespan_state, "rocq_start", e.message, reason="not_found"
            )
            return resp
        raise
    # Capture mtime after pet.start to avoid TOCTOU gap.
    try:
        file_mtime: float | None = os.path.getmtime(resolved_file)
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
    goals, focus_depth = _try_render_goals_with_depth(pet, state, goals_format)
    result: dict[str, Any] = {
        "success": True,
        "state_id": state_id,
        "goals": goals if goals is not None else "",
        "file": file,
        "theorem": theorem,
        "proof_finished": getattr(state, "proof_finished", False),
    }
    if focus_depth is not None:
        result["focus_depth"] = focus_depth
    return result


def _build_preamble_start_result(
    pet: Any,
    *,
    preamble: str,
    workspace: str,
    lifespan_state: dict[str, Any],
) -> dict[str, Any]:
    """Return the rocq_start-style payload for a preamble-based state."""
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


async def capture_position_state(
    *,
    file: str,
    resolved_file: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    line: int,
    character: int,
    tool: str,
    track_staleness: bool = True,
    timeout: float | None = None,
) -> dict[str, Any]:
    """Capture a position-based proof state via the async PET helper.

    *tool* is forwarded to ``_run_with_pet`` as both the canonical tool
    name in user-facing error messages and the ``tool`` field on
    ``recent_errors`` entries.  Pass the public MCP tool name of the
    caller (e.g. ``"rocq_compile"`` for state capture from a coqc error
    position).

    ``timeout`` (seconds) is forwarded to ``_run_with_pet``; when ``None``
    the lifespan default is used.
    """

    def _execute(pet: Any) -> dict[str, Any]:
        return _build_position_start_result(
            pet,
            file=file,
            resolved_file=resolved_file,
            workspace=workspace,
            lifespan_state=lifespan_state,
            line=line,
            character=character,
            track_staleness=track_staleness,
        )

    return await _server._run_with_pet(
        _execute,
        lifespan_state,
        tool,
        timeout=timeout,
    )


@collects_degraded
async def run_start(
    file: str,
    theorem: str,
    workspace: str,
    lifespan_state: dict[str, Any],
    line: int | None = None,
    character: int | None = None,
    preamble: str = "",
    force_restart: bool = False,
    timeout: float | None = None,
    goals_format: str = "pretty",
) -> dict[str, Any]:
    """Open a proof context and return a state_id.

    Three start modes (precedence: theorem > position > preamble):
    1. By theorem: file + theorem -> pet.start()
    2. By position: file + line + character -> pet.get_state_at_pos()
    3. From imports: preamble -> _get_or_create_import_state()

    If force_restart is True, kill the current PET process and clear
    all cached state before starting the new session.
    """
    if goals_format not in GOALS_RENDER_FORMATS:
        return _server._fail(
            lifespan_state,
            "rocq_start",
            f"Invalid goals_format {goals_format!r}; expected one of "
            "pretty | structured | names_only.",
        )
    # Mode detection
    _start_by_theorem = bool(file and theorem)
    _start_by_pos = bool(
        file and not theorem and line is not None and character is not None
    )
    _start_by_preamble = bool(
        not file and not theorem and preamble and preamble.strip()
    )

    if not (_start_by_theorem or _start_by_pos or _start_by_preamble):
        return _server._fail(
            lifespan_state,
            "rocq_start",
            (
                "No valid start mode. Provide file+theorem, "
                "file+line+character, or preamble."
            ),
        )

    if _start_by_pos:
        if not (0 <= line <= _MAX_LINE_CHAR_RANGE) or not (
            0 <= character <= _MAX_LINE_CHAR_RANGE
        ):
            return _server._fail(
                lifespan_state,
                "rocq_start",
                f"line and character must be in range [0, {_MAX_LINE_CHAR_RANGE}].",
            )

    # Path traversal + existence check (early validation before entering thread)
    resolved_file: str = ""
    if _start_by_theorem or _start_by_pos:
        try:
            resolved_file = _server._resolve_file_in_workspace(file, workspace)
        except (ValueError, FileNotFoundError) as e:
            return _server._fail(lifespan_state, "rocq_start", str(e))

    # Forbidden commands check for preamble
    if _start_by_preamble:
        forbidden = _check_forbidden_commands(preamble)
        if forbidden:
            return _server._fail(lifespan_state, "rocq_start", forbidden)

    def _execute(pet: Any) -> dict[str, Any]:
        if _start_by_theorem:
            return _build_theorem_start_result(
                pet,
                file=file,
                resolved_file=resolved_file,
                theorem=theorem,
                workspace=workspace,
                lifespan_state=lifespan_state,
                goals_format=goals_format,
            )
        if _start_by_pos:
            return _build_position_start_result(
                pet,
                file=file,
                resolved_file=resolved_file,
                workspace=workspace,
                lifespan_state=lifespan_state,
                goals_format=goals_format,
                line=line,
                character=character,
            )
        return _build_preamble_start_result(
            pet,
            preamble=preamble,
            workspace=workspace,
            lifespan_state=lifespan_state,
        )

    if force_restart:
        _server._invalidate_pet(lifespan_state)

    return await _server._run_with_pet(
        _execute,
        lifespan_state,
        "rocq_start",
        timeout=timeout,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_check
# ---------------------------------------------------------------------------


def _run_one_check_command(
    pet: Any,
    state: Any,
    cmd: str,
    *,
    entry: _StateEntry,
    prev_state_id: int,
    command_index: int,
    total_commands: int,
    is_single: bool,
    timeout: float,
    include_warnings: bool,
    feedback_pairs: list[list[str]],
    total_feedback_size: int,
    stale_warning: str | None,
    lifespan_state: dict[str, Any],
) -> tuple[Any, int, list[str] | None, dict[str, Any] | None]:
    """Run one ``run_check`` command and report its outcome.

    Returns ``(new_state, new_state_id, feedback_entry, failure_dict)``.
    On success ``failure_dict`` is ``None`` and ``feedback_entry`` is
    either the ``[cmd, fb_text]`` pair to append (when feedback was
    produced and the budget allows) or ``None``.  On a tactic-level
    failure ``failure_dict`` is the fully assembled envelope ready for
    the driver to return verbatim, ``new_state`` is the pre-call
    ``state`` and ``new_state_id`` is ``prev_state_id``.  When the pet
    process itself died the underlying :class:`PetanqueError` is
    re-raised so ``_run_with_pet`` can surface ``pet_restarted=True``.
    """
    from pytanque import PetanqueError

    try:
        if _is_timeout_eligible(cmd) and timeout >= 1:
            if is_single:
                rocq_timeout: int | None = int(timeout)
            else:
                rocq_timeout = max(1, int(timeout / total_commands))
        else:
            rocq_timeout = None

        new_state = pet.run(state, cmd, timeout=rocq_timeout)

        feedback_entry: list[str] | None = None
        if total_feedback_size < _MAX_TOTAL_FEEDBACK:
            fb_text = _extract_feedback(new_state, include_warnings=include_warnings)
            if fb_text is not None:
                feedback_entry = [cmd, fb_text]

        new_state_id = _state_add(
            state=new_state,
            file=entry.file,
            theorem=entry.theorem,
            workspace=entry.workspace,
            parent_id=prev_state_id,
            tactic=cmd,
            step=entry.step + command_index + 1,
            file_mtime=entry.file_mtime,
            resolved_file=entry.resolved_file,
        )
        return new_state, new_state_id, feedback_entry, None
    except PetanqueError as e:
        if not _server._pet_alive(lifespan_state.get("pet_client")):
            raise
        _server._record_error(
            lifespan_state,
            "rocq_check",
            e.message,
            reason="tactic_failed",
        )
        failure = _build_check_failure_dict(
            error_message=e.message,
            failed_command=cmd,
            command_index=command_index,
            last_valid_state_id=prev_state_id,
            goals_at_failure=_try_get_goals(pet, state),
            feedback_pairs=feedback_pairs,
            stale_warning=stale_warning,
        )
        return state, prev_state_id, None, failure


def _build_check_failure_dict(
    *,
    error_message: str,
    failed_command: str,
    command_index: int,
    last_valid_state_id: int | None,
    goals_at_failure: str | None,
    feedback_pairs: list[list[str]],
    stale_warning: str | None,
) -> dict[str, Any]:
    """Assemble the result dict for a mid-batch ``run_check`` failure.

    Tags ``reason="tactic_failed"`` so the unified envelope is consistent:
    agents can programmatically distinguish "your tactic was rejected by
    Coq" from a transport-level ``"crashed"`` (pet died) or ``"timeout"``.
    """
    result: dict[str, Any] = {
        "success": False,
        "reason": "tactic_failed",
        "error": error_message,
        "failed_command": failed_command,
        "command_index": command_index,
        "commands_run": command_index,
        "last_valid_state_id": last_valid_state_id,
        "goals_at_failure": goals_at_failure,
    }
    if feedback_pairs:
        result["feedback"] = feedback_pairs
    if stale_warning:
        result["stale_warning"] = stale_warning
    if last_valid_state_id is not None:
        result["hint"] = (
            f"Use rocq_check(body='...', from_state={last_valid_state_id}) "
            f"or rocq_step_multi(tactics=[...], from_state={last_valid_state_id})."
        )
    return result


def _build_check_success_dict(
    *,
    goals_text: str,
    proof_finished: bool,
    commands_run: int,
    check_time_ms: int,
    state_id: int,
    from_state_id: int,
    feedback_pairs: list[list[str]],
    stale_warning: str | None,
    complete: Any,
    goals_format: str = "pretty",
    goals_list: list[Any] | None = None,
    goals_diff: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Assemble the result dict for a successful ``run_check`` batch.

    ``goals_format`` selects the goals representation: ``"pretty"``
    (string, default), ``"structured"`` / ``"names_only"`` (lists —
    require *goals_list*; fall back to the pretty text when goal
    retrieval degraded), ``"diff"`` (emits ``goals_diff`` instead of
    ``goals``; falls back to pretty when the parent lookup degraded),
    or ``"none"`` (omits goals entirely).
    """
    result: dict[str, Any] = {
        "success": True,
        "proof_finished": proof_finished,
        "commands_run": commands_run,
        "check_time_ms": check_time_ms,
        "state_id": state_id,
        "from_state_id": from_state_id,
    }
    if goals_format == "none":
        pass
    elif goals_format == "diff" and goals_diff is not None:
        result["goals_diff"] = goals_diff
    elif goals_format in ("structured", "names_only") and goals_list is not None:
        result["goals"] = _render_goals(goals_list, goals_format)
    else:
        # pretty, or any degraded non-pretty mode falls back to the text.
        result["goals"] = goals_text or "No goals remaining."
    if feedback_pairs:
        result["feedback"] = feedback_pairs
    if stale_warning:
        result["stale_warning"] = stale_warning
    if complete and complete.shelf:
        result["shelved_goals"] = len(complete.shelf)
    if complete and complete.given_up:
        result["given_up_goals"] = len(complete.given_up)
    depth = _focus_depth(complete)
    if depth is not None:
        result["focus_depth"] = depth
    if proof_finished and state_id is not None:
        path = _reconstruct_tactic_path(state_id)
        if path.status == "complete":
            if path.tactics:
                result["proof_tactics"] = path.tactics
            leaf = _state_get(state_id)
            script_fields = _assemble_proof_script(leaf, path.tactics) if leaf else {}
            result.update(script_fields)
            if "proof_script" in script_fields:
                result["proof_hint"] = (
                    "Proof complete. Validate proof_script with "
                    "rocq_compile_file (after writing it into the .v) "
                    "and rocq_verify."
                )
            else:
                result["proof_hint"] = (
                    "Proof complete. Assemble the .v (imports + statement "
                    "+ Proof. + proof_tactics + Qed.), then validate with "
                    "rocq_compile_file and rocq_verify."
                )
        else:
            result["proof_tactics_status"] = path.status
            result["proof_tactics_broken_at"] = path.broken_at
            result["proof_tactics_hint"] = (
                f"Tactic chain unrecoverable ({path.status} at state "
                f"{path.broken_at}). Call rocq_check(from_state="
                f"{state_id}) to commit the proof, or rocq_start to "
                f"restart from a fresh session."
            )
    return result


@collects_degraded
async def run_check(
    body: str,
    lifespan_state: dict[str, Any],
    from_state: int,
    *,
    timeout: float | None = None,
    include_warnings: bool = True,
    goals_format: str = "pretty",
) -> dict[str, Any]:
    """Execute commands sequentially from a state.

    One command = step. Multiple commands = batch.
    Returns state_id, goals, proof_finished, and timing info.
    On error mid-batch, returns last_valid_state_id for recovery.

    When ``include_warnings=False``, per-step feedback drops entries at
    LSP Warning severity (level 2) so warning noise does not crowd out
    tool output (Print / Search / vm_compute traces).

    ``goals_format`` selects the goals representation: ``pretty``
    (default), ``structured``, ``names_only``, ``diff`` (delta vs the
    ``from_state`` parent — one extra pet round-trip), or ``none``.
    """
    if goals_format not in ("pretty", "structured", "names_only", "diff", "none"):
        return _server._fail(
            lifespan_state,
            "rocq_check",
            f"Invalid goals_format {goals_format!r}; expected one of "
            "pretty | structured | names_only | diff | none.",
        )
    if len(body) > _server.ROCQ_MAX_SOURCE_SIZE:
        return _server._fail(
            lifespan_state,
            "rocq_check",
            (
                f"Body too large ({len(body)} bytes, "
                f"max {_server.ROCQ_MAX_SOURCE_SIZE})."
            ),
        )

    forbidden = _check_forbidden_commands(body)
    if forbidden:
        return _server._fail(lifespan_state, "rocq_check", forbidden)

    commands = _split_rocq_sentences(body) if body.strip() else []

    entry, base_state_id, err = _resolve_check_base_state(from_state)
    if err:
        return _server._fail(lifespan_state, "rocq_check", err)
    assert entry is not None and base_state_id is not None  # err is None here

    # Empty body — return early.
    if not commands:
        return {
            "success": True,
            "commands_run": 0,
            "state_id": base_state_id,
            "from_state_id": base_state_id,
            "goals": "",
            "proof_finished": entry.proof_finished,
            "check_time_ms": 0,
        }

    _timeout: float = (
        timeout
        if timeout is not None and timeout > 0
        else lifespan_state["pet_timeout"]
    )
    is_single = len(commands) == 1

    # Track progress so partial work survives an asyncio-level timeout.
    partial_state: dict[str, Any] = {"commands_run": 0}

    def _execute(pet: Any) -> dict[str, Any]:
        try:
            import pytanque  # noqa: F401
        except ImportError:
            return {
                "success": False,
                "error": _server._PYTANQUE_NOT_INSTALLED_HINT,
            }

        # Re-validate under the lock — pet may have restarted between the
        # outer check and now, invalidating the entry.
        entry_to_use, _re_base_id, re_err = _resolve_check_base_state(base_state_id)
        if re_err or entry_to_use is None:
            return _server._fail(
                lifespan_state,
                "rocq_check",
                re_err or "Internal: state lost.",
            )

        stale_warning = _check_staleness(entry_to_use)
        start_time = time.monotonic()
        _server._set_workspace_if_needed(pet, entry_to_use.workspace, lifespan_state)

        state = entry_to_use.state
        parent_state = entry_to_use.state  # kept for goals_format="diff"
        prev_state_id = base_state_id
        feedback_pairs: list[list[str]] = []
        total_feedback_size = 0

        for i, cmd in enumerate(commands):
            new_state, new_state_id, feedback_entry, failure = _run_one_check_command(
                pet,
                state,
                cmd,
                entry=entry_to_use,
                prev_state_id=prev_state_id,
                command_index=i,
                total_commands=len(commands),
                is_single=is_single,
                timeout=_timeout,
                include_warnings=include_warnings,
                feedback_pairs=feedback_pairs,
                total_feedback_size=total_feedback_size,
                stale_warning=stale_warning,
                lifespan_state=lifespan_state,
            )
            if failure is not None:
                return failure
            if feedback_entry is not None:
                feedback_pairs.append(feedback_entry)
                total_feedback_size += len(feedback_entry[1])
            state = new_state
            prev_state_id = new_state_id
            partial_state["commands_run"] = i + 1
            partial_state["last_valid_state_id"] = new_state_id

        elapsed = time.monotonic() - start_time

        goals_list: list[Any] | None
        try:
            complete = pet.complete_goals(state)
            goals_list = complete.goals if complete else []
            goals_text = _format_goals(goals_list)
        except Exception as e:
            note_degraded("goals:pet_call_failed", repr(e))
            goals_text = "(goals unavailable)"
            complete = None
            goals_list = None

        goals_diff: dict[str, Any] | None = None
        if goals_format == "diff" and goals_list is not None:
            try:
                parent_complete = pet.complete_goals(parent_state)
                parent_goals = parent_complete.goals if parent_complete else []
                goals_diff = _goals_diff(parent_goals, goals_list)
            except Exception as e:
                # Fall back to full pretty goals (builder handles it).
                note_degraded("goals_diff:pet_call_failed", repr(e))

        return _build_check_success_dict(
            goals_text=goals_text,
            proof_finished=state.proof_finished,
            commands_run=len(commands),
            check_time_ms=int(elapsed * 1000),
            state_id=prev_state_id,
            from_state_id=base_state_id,
            feedback_pairs=feedback_pairs,
            stale_warning=stale_warning,
            complete=complete,
            goals_format=goals_format,
            goals_list=goals_list,
            goals_diff=goals_diff,
        )

    # Timeout strategy: both single and multi-command use two-tier when eligible
    if _timeout >= 1:
        hard_timeout = _compute_hard_timeout(_timeout)
    else:
        hard_timeout = _timeout

    return await _server._run_with_pet(
        _execute,
        lifespan_state,
        "rocq_check",
        timeout=float(hard_timeout),
        partial_state=partial_state,
    )


# ---------------------------------------------------------------------------
# Tool: rocq_step_multi (with from_state support)
# ---------------------------------------------------------------------------


@collects_degraded
async def run_step_multi(
    tactics: list[str],
    lifespan_state: dict[str, Any],
    from_state: int,
    *,
    include_warnings: bool = True,
    timeout: float | None = None,
    goals_format: str = "pretty",
    timeouts: list[float] | None = None,
    preset: str = "",
) -> dict[str, Any]:
    """Core implementation of rocq_step_multi (testable without FastMCP Context).

    Supports ``from_state`` to try tactics from a specific state.
    Results are ephemeral — commit with ``rocq_check(body=..., from_state=...)``.

    When ``include_warnings=False``, per-tactic feedback drops entries at
    LSP Severity (level 2).

    Identical outcomes are deduplicated: the first tactic reaching a
    proof state carries the full payload; subsequent tactics reaching
    the *same* state carry ``same_outcome_as: <index into results>``
    instead of repeating goals.  The response carries
    ``distinct_outcomes`` (count of unique successful outcomes).
    """
    if goals_format not in GOALS_RENDER_FORMATS:
        return _server._fail(
            lifespan_state,
            "rocq_step_multi",
            f"Invalid goals_format {goals_format!r}; expected one of "
            "pretty | structured | names_only.",
        )
    if preset not in ("", "auto"):
        return _server._fail(
            lifespan_state,
            "rocq_step_multi",
            f'Invalid preset {preset!r}; expected "auto" or omit.',
        )
    preset_truncated = False
    if preset == "auto":
        if timeouts is not None:
            return _server._fail(
                lifespan_state,
                "rocq_step_multi",
                "timeouts cannot be combined with preset (the battery "
                "changes the tactic list length).",
            )
        seen = {t.strip() for t in tactics}
        battery = [t for t in _AUTO_SOLVE_TACTICS if t not in seen]
        room = _MAX_STEP_MULTI_TACTICS - len(tactics)
        if room < len(battery):
            preset_truncated = True
        tactics = list(tactics) + battery[: max(0, room)]
        if not tactics:
            return _server._fail(
                lifespan_state, "rocq_step_multi", "No tactics to try."
            )
    if timeouts is not None:
        if len(timeouts) != len(tactics):
            return _server._fail(
                lifespan_state,
                "rocq_step_multi",
                f"timeouts has {len(timeouts)} entries for " f"{len(tactics)} tactics.",
            )
        if any(t <= 0 for t in timeouts):
            return _server._fail(
                lifespan_state,
                "rocq_step_multi",
                "every timeouts entry must be > 0.",
            )

    # Validate each tactic up front
    if len(tactics) > _MAX_STEP_MULTI_TACTICS:
        return _server._fail(
            lifespan_state,
            "rocq_step_multi",
            (
                f"Too many tactics: {len(tactics)} "
                f"exceeds maximum of {_MAX_STEP_MULTI_TACTICS}."
            ),
        )

    for tac in tactics:
        forbidden = _check_forbidden_commands(tac)
        if forbidden:
            return _server._fail(
                lifespan_state,
                "rocq_step_multi",
                f"Forbidden in tactic {tac!r}: {forbidden}",
            )

    _timeout: float = (
        timeout
        if timeout is not None and timeout > 0
        else lifespan_state["pet_timeout"]
    )
    if timeouts is not None:
        # Per-tactic budgets: the batch's wall clock is their sum.
        hard_timeout = _compute_hard_timeout(sum(timeouts))
    else:
        hard_timeout = _compute_hard_timeout(_timeout)

    # Quick pre-check to avoid acquiring lock for invalid states.
    # Re-validated inside _execute (state may be invalidated between checks).
    _, _, err = _resolve_check_base_state(from_state)
    if err:
        return _server._fail(lifespan_state, "rocq_step_multi", err)

    # Shared list so partial results survive a timeout via partial_state
    partial_state: dict[str, Any] = {"partial_results": []}

    def _execute(pet: Any) -> dict[str, Any]:
        try:
            from pytanque import PetanqueError
        except ImportError:
            return {
                "success": False,
                "error": _server._PYTANQUE_NOT_INSTALLED_HINT,
            }

        # Re-validate under lock — pet may have restarted since the outer check.
        entry_to_use, base_state_id, err = _resolve_check_base_state(from_state)
        if err or entry_to_use is None:
            return _server._fail(
                lifespan_state,
                "rocq_step_multi",
                err or "Internal: state lost.",
            )

        _server._set_workspace_if_needed(pet, entry_to_use.workspace, lifespan_state)
        parent_state = entry_to_use.state

        # Check for file staleness (non-blocking warning)
        stale_warning = _check_staleness(entry_to_use)

        total_feedback_size = 0
        # Outcome dedup: fingerprint -> index of the first results entry
        # that reached this proof state.
        outcome_index: dict[tuple[Any, ...], int] = {}

        for tactic_index, tactic in enumerate(tactics):
            tac = tactic.strip()
            # Focus/bullet tokens ({, }, -, +, * runs) must stay bare:
            # Rocq rejects a trailing dot (e.g. "-." is a syntax error).
            if not _is_focus_token(tac) and not tac.endswith("."):
                tac += "."

            if timeouts is not None:
                per_tactic_budget = max(1, int(timeouts[tactic_index]))
                budget_eligible = _is_timeout_eligible(tac)
            else:
                per_tactic_budget = max(1, int(_timeout / len(tactics)))
                budget_eligible = _is_timeout_eligible(tac) and _timeout >= 1
            tac_rocq_timeout = per_tactic_budget if budget_eligible else None

            entry_dict: dict[str, Any] = {"tactic": tac}
            tactic_started = time.monotonic()
            try:
                new_state = pet.run(parent_state, tac, timeout=tac_rocq_timeout)

                # Collect per-tactic feedback if any.
                if total_feedback_size < _MAX_TOTAL_FEEDBACK:
                    fb_text = _extract_feedback(
                        new_state, include_warnings=include_warnings
                    )
                    if fb_text is not None:
                        entry_dict["feedback"] = fb_text
                        total_feedback_size += len(fb_text)

                complete = pet.complete_goals(new_state)
                goals_list = complete.goals if complete else []

                goals_text = _format_goals(goals_list)
                depth = _focus_depth(complete)
                shelved = len(complete.shelf) if complete and complete.shelf else 0
                given_up = (
                    len(complete.given_up) if complete and complete.given_up else 0
                )
                entry_dict["success"] = True
                entry_dict["proof_finished"] = new_state.proof_finished

                entry_dict["goals_count"] = len(goals_list)

                fingerprint = (
                    goals_text,
                    new_state.proof_finished,
                    depth,
                    shelved,
                    given_up,
                )
                first_idx = outcome_index.get(fingerprint)
                if first_idx is not None:
                    # Same proof state as an earlier tactic: reference it
                    # instead of repeating up to 8KB of goals.
                    entry_dict["same_outcome_as"] = first_idx
                else:
                    outcome_index[fingerprint] = len(partial_state["partial_results"])
                    if goals_format == "pretty":
                        entry_dict["goals"] = goals_text or "No goals remaining."
                    else:
                        entry_dict["goals"] = _render_goals(goals_list, goals_format)
                    if shelved:
                        entry_dict["shelved_goals"] = shelved
                    if given_up:
                        entry_dict["given_up_goals"] = given_up
                    if depth is not None:
                        entry_dict["focus_depth"] = depth
            except PetanqueError as e:
                # If pet died, re-raise so outer handler detects it.
                if not _server._pet_alive(lifespan_state.get("pet_client")):
                    raise
                # Tag the same reason rocq_check uses for mid-batch
                # failures so an agent dispatcher can treat per-tactic
                # entries with a uniform key.  The tactic was rejected
                # by Coq (live PetanqueError, pet still alive) — not a
                # transport-level crash.
                entry_dict["success"] = False
                entry_dict["reason"] = "tactic_failed"
                entry_dict["error"] = e.message

            entry_dict["time_ms"] = int((time.monotonic() - tactic_started) * 1000)
            partial_state["partial_results"].append(entry_dict)

        # Read-only exploration — do NOT update state table
        results = list(partial_state["partial_results"])
        successes = [e for e in results if e.get("success")]
        finished = [e["tactic"] for e in successes if e.get("proof_finished")]
        best: dict[str, Any] | None = None
        for e in successes:
            count = e.get("goals_count")
            if count is None:
                continue
            key = (not e.get("proof_finished", False), count)
            if best is None or key < (
                not best.get("proof_finished", False),
                best.get("goals_count", 1 << 30),
            ):
                best = e
        resp: dict[str, Any] = {
            "success": True,
            "results": results,
            "distinct_outcomes": len(outcome_index),
            "summary": {
                "tried": len(results),
                "succeeded": len(successes),
                "finished": finished,
                "distinct_outcomes": len(outcome_index),
                **(
                    {
                        "best": {
                            "tactic": best["tactic"],
                            "goals_count": best["goals_count"],
                        }
                    }
                    if best is not None
                    else {}
                ),
            },
        }
        if preset_truncated:
            resp["preset_truncated"] = True
        if base_state_id is not None:
            resp["from_state_id"] = base_state_id
        if stale_warning:
            resp["stale_warning"] = stale_warning
        return resp

    return await _server._run_with_pet(
        _execute,
        lifespan_state,
        "rocq_step_multi",
        timeout=hard_timeout,
        partial_state=partial_state,
    )
