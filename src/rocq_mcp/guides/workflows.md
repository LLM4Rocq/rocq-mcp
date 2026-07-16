# rocq-mcp workflows — choosing tools and proof patterns

Deep reference for agents. The tool descriptions carry the contracts; this
guide carries the patterns.

## Choosing a tool

| If you want to... | Use |
|---|---|
| Iteratively develop a single proof, trying tactics | `rocq_start` + `rocq_check` / `rocq_step_multi` |
| Inspect proof state at a specific line / character | `rocq_start(file=..., line=..., character=...)` — see Position semantics below |
| Search for a lemma by pattern (e.g. `Search _.`) | `rocq_query` |
| Compile a finished `.v` file (whole-file check, axiom audit) | `rocq_compile_file` |
| Compile a finished proof from a string buffer | `rocq_compile` |
| Probe a scratch file in `/tmp` | `rocq_start(file='/tmp/probe.v', theorem=...)` — **never `coqc /tmp/probe.v`** (coqc reloads all imports each call; the session keeps them warm) |
| Verify a proof matches its stated theorem | `rocq_verify` |
| Audit which axioms a proof depends on | `rocq_assumptions` |
| List definitions / lemmas in a file | `rocq_toc` |
| List notations in a statement and how they resolve | `rocq_notations` |
| Check pet health, memory, recent errors, lock contention | `rocq_diag` |
| Check which opam switch / binaries the server resolves | `rocq_health` |
| Change the server's opam switch in-session | `rocq_switch` (sharp — see the concurrency guide) |

## The core proof loop

1. `s0 = rocq_start(file=..., theorem=...)["state_id"]` — opens the proof,
   returns the goals.
2. `rocq_step_multi(from_state=s0, tactics=[...])` — try candidates
   (read-only; does not advance anything).
3. `s1 = rocq_check(from_state=s0, body="winning_tactic.")["state_id"]` —
   commit the winner; repeat 2–3 from `s1`.
4. When `proof_finished: true` — assemble the final `.v` (imports +
   statement + `Proof.` + the returned `proof_tactics` + `Qed.`), then
   `rocq_compile_file` + `rocq_verify` (+ `rocq_assumptions` for an axiom
   audit).

## Multi-tactic exploration: advance, then branch

To explore N alternative tactics after a confident prefix, commit the
prefix with `rocq_check` first, then branch with `rocq_step_multi` — do
NOT repeat the prefix inside every `tactics` entry (each entry would
re-run it):

    result = rocq_check(from_state=S, body="intros n m H.")
    rocq_step_multi(from_state=result["state_id"],
                    tactics=["by ring.", "by lia.", "by reflexivity."])

Standard automation battery for auto-solving a subgoal (cheapest first):

    ["trivial.", "reflexivity.", "assumption.", "exact I.",
     "auto.", "eauto.", "tauto.", "intuition.", "lia.", "lra.",
     "nia.", "nra.", "ring.", "field.", "decide equality.", "firstorder."]

Note: `lia`/`lra`/`ring`/`field` require the file/preamble to import
`Lia`/`Lra`/`Ring`/`Field`.

Structure exploration: `tactics=["destruct n.", "induction n.", "case_eq n."]`.

## Imports and scopes in rocq_query

Statements like `Require Import`, `From X Require Y`, `Open Scope`,
`Set`, `Unset`, `Local`, and `Section` must go in `preamble=` (a
multi-line string), not in `command=`. Each statement in `command=` runs
in isolation, so an `Open Scope` there would not propagate to the next
statement:

    rocq_query(preamble="From Coq Require Import Reals.\nOpen Scope R_scope.",
               command="Search (_ + _).")

For multi-import contexts prefer `file=<path>` to a `.v` file containing
the imports — more reliable when the imports include `Set` / `Unset`
directives that need a specific order.

For mid-proof queries — e.g. `Search` against the live proof state — use
`from_state=<state_id>`; the live state already has all imports and
scopes set up. The query runs against a transient child state which is
discarded; the parent state is unchanged. Prefer this over
`rocq_check(body="Search ...")` for pure queries — no new `state_id` is
allocated and the state table is not polluted:

    state_id = rocq_check(body=..., from_state=...)["state_id"]
    rocq_query(command="Search _.", from_state=state_id)

## Scratch iteration without a project

`rocq_start(preamble='Require Import ...')` sets up an import-only
session — no project files needed. The import set is content-hashed and
stays warm across iterations even when the lemma body changes. For a
scratch file under `/tmp` that needs the project's load path, keep the
file name stable across iterations (e.g. `/tmp/probe.v`) — Fleche caches
per file path, so rotating probe names defeats the warmth.

## Position semantics (rocq_start by position)

`line` and `character` are 0-indexed. Petanque resolves the cursor to a
sentence boundary by *rounding forward* through the sentence containing
the cursor:

- Cursor on any character of a sentence — its first letter, any character
  inside, or its terminating period — yields the state **after** that
  whole sentence has executed.
- Cursor in the whitespace **before** a sentence's first non-whitespace
  character yields the state **before** that sentence (= after the
  previous one).
- Cursor in the whitespace **after** a sentence's terminating period
  yields the state **after** that sentence.

So: to inspect goals **before** a tactic, point at the whitespace just
before its first character; to inspect goals **after** it, point at any
character of the tactic (including its period).

## Stale files

Interactive sessions read the `.v` file at session start and do not track
edits. If any process modifies the file while a session is active, the
proof state is stale — tactics may fail or lie. Responses carry
`stale_warning` when this is detected. In multi-agent setups, work on a
**copy** of the file for interactive proving, or `rocq_start` again after
edits. See the concurrency guide for per-agent isolation patterns.

## Briefing sub-agents

When spawning a sub-agent that will write or check Rocq/Coq proofs,
prefix its task prompt with:

    Before any Write or `coqc` on a .v file:
      1. Consult project-specific Rocq guidance first (CLAUDE.md,
         AGENTS.md, or a Skill if available).
      2. For scratch iteration on a single proof, use rocq-mcp:
           rocq_start file=/tmp/<name>.v theorem=<lemma>
           rocq_step_multi tactics=[...]   (NOT  coqc /tmp/<name>.v)
      3. Use `coqc` only for: full-project rebuilds, axiom audits via
         `Print Assumptions`, and final compile verification.

Without it, sub-agents fall into a `Write` → `coqc /tmp/<file>.v` → grep
loop that re-pays the import cost on every iteration.
