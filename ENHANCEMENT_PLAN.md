# rocq-mcp-v2 Enhancement Plan

**Date**: 2026-03-09
**Status**: Proposed
**Based on**: Expert review of lean-lsp-mcp (20+ tools) vs. rocq-mcp-v2 (4 tools)

## Executive Summary

Add **4 new tools + 1 enhancement** to rocq-mcp-v2, bringing the total from 4 to 8 tools.
These were selected from 20+ lean-lsp-mcp candidates by a panel of 4 expert agents
(Architecture, Pytanque, Search, Devil's Advocate) with consensus-based resolution.

The additions focus on **low-cost, concrete efficiency gains**. The experts unanimously
agreed that the gap between 81% and 100% on miniF2F is a mathematical reasoning gap,
not a tooling gap. These tools reduce token waste and iteration cycles, but the biggest
wins will come from agent-level improvements.

## Current Tools (4)

| Tool | Transport | Purpose |
|------|-----------|---------|
| `rocq_compile` | coqc subprocess | Compile full .v file, return errors |
| `rocq_verify` | coqc subprocess | Verify proof matches statement via Module M |
| `rocq_query` | pytanque (pet) | Run Search/Check/Print/About queries |
| `rocq_step` | pytanque (pet) | Execute tactic, return goals |

## Planned Additions

### 1. `rocq_toc` — File Table of Contents

**Purpose**: Return the structure of a .v file (all definitions, lemmas, theorems, sections)
without reading the entire file.

**Pytanque method**: `toc(file)` → `TocResponse` containing `List[Tuple[str, List[TocElement]]]`

**Type details** (from protocol.py):
```
TocElement:
  name: Name         # Name.v: Optional[str] (the identifier)
  detail: str        # kind string ("Lemma", "Definition", etc.)
  kind: int          # numeric kind code
  range: Range       # Range(start: Position, end: Position)
  children: Optional[List[TocElement]]  # nested definitions
```

**Signature**:
```python
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
```

**Output format** (formatted text for LLM readability):
```
File: test.v
  Definition my_fn (line 5)
  Lemma helper1 (line 12)
  Theorem main_thm (line 20)
    Lemma sub_lemma (line 22)
```

**Implementation notes**:
- Requires pet subprocess (lazy init via `_ensure_pet`)
- Calls `pet.set_workspace()` + `pet.toc(file)` under `_pet_lock`
- Does NOT mutate `_session` state — no conflict with active `rocq_step` sessions
- Format `TocElement` tree recursively into indented text
- Truncate output at `_MAX_QUERY_OUTPUT` (8000 chars)
- Estimated effort: ~60 lines

**Route**: `petanque/toc` (UniversalRoute — no session state needed)

---

### 2. `rocq_step_multi` — Try Multiple Tactics

**Purpose**: Try N candidate tactics against the current proof state and return all results,
WITHOUT advancing the session. The LLM then picks the winner and commits via `rocq_step`.

**Motivation**: Reduces tool call overhead for trial-and-error interactive proving. The
experiment data shows ~34 tool calls per solved problem. When the LLM wants to try
`lia`, `omega`, `ring`, and `auto`, that's currently 4 sequential `rocq_step` calls
with session management complexity (rolling back on failure). This tool does it in one call.

**Key design decision**: Pytanque states are immutable references — `pet.run(state, tactic)`
returns a NEW state without modifying the old one. So we can safely try each tactic against
the same parent state and report all results.

**Signature**:
```python
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

    Args:
        tactics: List of tactics to try (max 20).
    """
```

**Output format**:
```json
{
  "success": true,
  "results": [
    {"tactic": "auto", "success": false, "error": "..."},
    {"tactic": "lia", "success": true, "goals": "No goals remaining.", "proof_finished": true},
    {"tactic": "lra", "success": false, "error": "..."}
  ]
}
```

**Implementation notes**:
- Read `_session["state"]` as parent state
- For each tactic: `new_state = pet.run(parent_state, tactic)` + `pet.goals(new_state)`
- Catch `PetanqueError` per-tactic (tactic failure ≠ tool failure)
- Do NOT update `_session["state"]` — this is read-only exploration
- Cap at 20 tactics to prevent abuse
- Use same `_pet_lock` + `_pet_semaphore` pattern as `rocq_step`
- On timeout: kill pet, report partial results for tactics already tried
- Estimated effort: ~100 lines

---

### 3. `rocq_auto_solve` — Try Standard Automation

**Purpose**: One-shot "can automation solve this?" check. Generates a .v file that
tries all standard decision procedures via Rocq's `first` combinator.

**Motivation**: Before the LLM spends tokens on manual proof construction, this
answers: "is this trivially automatable?" The 81% compile-first success rate could
improve if the LLM tries automation first.

**Key design decision**: coqc-only implementation (no pytanque needed). This avoids
pet subprocess contention and works even when pytanque is not installed.

**Signature**:
```python
@mcp.tool
def rocq_auto_solve(
    problem: str,
    preamble_tactics: str = "",
    workspace: str = "",
    timeout: int = 0,
) -> dict[str, Any]:
    """Try to prove a theorem using standard automation tactics.

    Attempts the following tactics (in order of speed):
    trivial, reflexivity, assumption, auto, eauto, tauto, intuition,
    lia, lra, nia, nra, ring, field, decide, firstorder.

    Optionally run preamble tactics first (e.g., "intros. simpl.").

    Does NOT require pytanque — uses coqc directly.

    Args:
        problem: Complete .v file with Admitted/Abort as placeholder.
        preamble_tactics: Optional tactics to run before automation
                         (e.g., "intros." or "intros. simpl. unfold foo.").
        workspace: Workspace directory (default: ROCQ_WORKSPACE env var).
        timeout: Timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
    """
```

**Generated proof strategy**:
```coq
(* Original imports and definitions from problem *)
...
Theorem name : statement.
Proof.
  intros.  (* or user-provided preamble_tactics *)
  first [
    trivial | reflexivity | assumption |
    auto | eauto | tauto | intuition |
    lia | lra | nia | nra |
    ring | field |
    decide |
    firstorder
  ].
Qed.
```

**Output format**:
```json
{
  "solved": true,
  "tactic": "lia",
  "proof": "Proof.\n  intros.\n  lia.\nQed."
}
```
or
```json
{
  "solved": false,
  "error": "None of the standard automation tactics succeeded.",
  "partial_results": "auto reduced to 2 subgoals; lia failed with ..."
}
```

**Implementation notes**:
- Parse the problem file to extract: imports/preamble, theorem name, theorem statement
- Generate a .v file with `first [tac1 | tac2 | ...]`
- Run via `_run_coqc(source, workspace, timeout)`
- If it succeeds, determine which tactic worked by trying each individually
- Reuses existing `_run_coqc`, `_check_forbidden_commands`, `_validate_workspace`
- No pytanque dependency — pure coqc subprocess
- Estimated effort: ~80 lines (including problem parsing)

**Future upgrade (Phase 2)**: pytanque-based version that works mid-proof on the
current `rocq_step` session state. This would try each tactic interactively and
report partial progress (e.g., "lia closed 2 of 3 goals").

---

### 4. `rocq_notations` — List Notations in a Statement

**Purpose**: Show all notations appearing in a theorem statement and how they resolve
(which scope, which module). Helps debug notation ambiguity — a recurring failure mode
observed in the miniF2F audit (4 theorems had Leibniz `=` vs `Qeq` confusion on Q).

**Pytanque method**: `list_notations_in_statement(state, statement)` → `List[NotationInfo]`

**Type details** (from protocol.py):
```
NotationInfo:
  path: str           # module path (e.g., "Coq.Init.Peano")
  secpath: str        # section path
  notation: str       # notation string (e.g., "_ + _")
  scope: Optional[str]  # scope name (e.g., "nat_scope", "Z_scope")
  locations: List[Any]  # source locations where notation appears
```

**Signature**:
```python
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
```

**Output format** (formatted text):
```
Notations found in statement:
  "_ + _"  →  Coq.Init.Nat  (scope: nat_scope)
  "_ = _"  →  Coq.Init.Logic  (scope: type_scope)
  "_ * _"  →  Coq.Init.Nat  (scope: nat_scope)
```

**Implementation notes**:
- Similar to `rocq_query`: create dummy lemma with the statement, call `pet.start`,
  then call `pet.list_notations_in_statement(state, statement)`
- Uses existing `_pet_lock` + `_pet_semaphore` pattern
- Route: `petanque/list_notations_in_statement`
  (`ListNotationsInStatementRoute` — returns `List[NotationInfo]`)
- Format NotationInfo list into readable text
- Estimated effort: ~50 lines

---

### 5. Enhancement: Enrich `rocq_step` with Complete Goals

**Purpose**: Surface shelved and given-up goals in `rocq_step` responses.

**Current behavior**: `rocq_step` calls `pet.goals(state)` which internally calls
`pet.complete_goals(state)` but strips it down to just the active goals list.

**GoalsResponse type** (from protocol.py):
```
GoalsResponse:
  goals: List[Goal]                          # active goals
  stack: List[Tuple[List[Any], List[Any]]]   # focus stack (bullets/braces)
  shelf: List[Any]                           # shelved goals
  given_up: List[Any]                        # given-up goals
```

**Change**: In `run_step`'s `_execute()`, replace `pet.goals()` with
`pet.complete_goals()` and add extra fields when non-empty:

```python
# Before:
goals = pet.goals(new_state)
goals_list = goals or []

# After:
complete = pet.complete_goals(new_state)
goals_list = complete.goals if complete else []
# ... existing goals_text formatting using pp_goal ...
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
```

**Implementation notes**:
- ~10 lines changed in `run_step`
- No new tool — enriches existing `rocq_step` response
- `stack` is omitted (internal focus structure, not useful for LLM)
- `shelf`/`given_up` only appear when non-empty (backward compatible)

---

## What We Explicitly Chose NOT to Add

| Category | Candidates | Reason | Expert Consensus |
|----------|-----------|--------|-----------------|
| **File I/O** | read/write/dir | MCP client (Claude Code) already provides Read/Write/Edit/Glob/Grep | 4/4 REJECT |
| **Completions** | auto-complete | IDE pattern, LLMs generate tokens, don't need dropdown suggestions | 4/4 REJECT |
| **Hover** | type at position | `Check`/`About` via `rocq_query` covers this | 4/4 REJECT |
| **AI Provers** | Gemini/GPT prove | Recursive architecture (LLM→MCP→LLM), out of scope | 4/4 REJECT |
| **AST Tools** | ast, ast_at_pos | Raw AST not interpretable by LLM | 4/4 REJECT |
| **State Compare** | state_equal, state_hash | Programmatic search infra, not LLM-useful | 4/4 REJECT/SKIP |
| **NL Search** | natural language | No Rocq equivalent of LeanSearch exists | 4/4 SKIP |
| **Premises** | full premise list | Output too large (10K+), untyped, `Search` is better | 3/4 REJECT |
| **Diagnostics** | errors at positions | `rocq_compile` stderr already provides this | 3/4 REJECT |
| **Local Search** | ripgrep on .v files | MCP client already has Grep | 3/4 REJECT |
| **State at Pos** | get_state_at_pos | Conflicts with single-session model, position-based interaction poorly suited to LLM | 3/4 REJECT |
| **Structured Search** | search with presets | Low ROI over `rocq_query` with manual preamble | 2/4 SKIP |

## Implementation Order

| Phase | Item | Effort | Pytanque? | Risk |
|-------|------|--------|-----------|------|
| **1a** | `rocq_auto_solve` (coqc-only) | ~80 lines | No | None |
| **1b** | Enrich `rocq_step` | ~10 lines | Yes (existing) | None |
| **1c** | `rocq_toc` | ~60 lines | Yes (toc route) | Low |
| **1d** | `rocq_notations` | ~50 lines | Yes (list_notations route) | Low |
| **1e** | `rocq_step_multi` | ~100 lines | Yes (run + goals) | Medium |
| **Total** | | ~300 lines | | |

All 5 items are Phase 1. No Phase 2 dependencies. Can be implemented in any order.

## Post-Phase 1 Considerations

- **CoqHammer integration**: If `coq-hammer` is installed in the workspace, the LLM can
  already use `hammer.` as a tactic via `rocq_step`/`rocq_compile`. No MCP tool needed.
  Document this in the README.

- **Pytanque-based hammer (Phase 2)**: Upgrade `rocq_auto_solve` to also work mid-proof on
  the current `rocq_step` session. Try each automation tactic interactively and report
  partial progress.

- **Premise-ranked search**: If/when a Rocq premise selection backend exists (akin to
  LeanHammer's neural premise selection), add a `rocq_suggest_premises` tool. Not
  feasible today.

- **Multi-file project support**: If rocq-mcp-v2 is used outside Claude Code (e.g., with
  a custom agent that lacks file I/O), consider adding `rocq_search_files` (ripgrep) and
  `rocq_read_file`. Defer until there's a concrete use case.

## Final Tool Inventory (after Phase 1)

| # | Tool | Transport | Category |
|---|------|-----------|----------|
| 1 | `rocq_compile` | coqc | Compile & error check |
| 2 | `rocq_verify` | coqc | Proof verification |
| 3 | `rocq_auto_solve` | coqc | Automated proving |
| 4 | `rocq_query` | pytanque | Search/Check/Print/About |
| 5 | `rocq_step` | pytanque | Interactive tactic (enhanced) |
| 6 | `rocq_step_multi` | pytanque | Multi-tactic exploration |
| 7 | `rocq_toc` | pytanque | File structure |
| 8 | `rocq_notations` | pytanque | Notation disambiguation |
