# rocq-mcp

[![CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/rocq-mcp/ci.yml?branch=main&style=for-the-badge)](https://github.com/LLM4Rocq/rocq-mcp/actions/workflows/ci.yml)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg?style=for-the-badge)](https://github.com/LLM4Rocq/rocq-mcp/blob/main/LICENSE)

An [MCP](https://modelcontextprotocol.io/) server for [Rocq](https://rocq-prover.org/) (formerly Coq) proof development. It exposes compilation, verification, querying, and interactive tactic stepping as MCP tools, so that LLM agents can write and check Rocq proofs.

## Prerequisites

- **Rocq / Coq** -- `coqc` must be on your `PATH` (needed by all tools). If the workspace contains a `_RocqProject` or `_CoqProject` file, the server parses it for load-path flags (`-Q`, `-R`, `-I`). For **dune projects** (no `_CoqProject` but a `dune-project` file present), the server auto-detects load paths via `dune coq top` (once per `(coq.theory ...)` stanza, so multi-theory workspaces resolve cross-theory imports correctly) and writes a `_RocqProject` file in the workspace so that coq-lsp also picks them up. This generated file stays in the workspace and should be added to `.gitignore`. Otherwise it defaults to `-Q <workspace> Test`.
- **pet** (from [coq-lsp](https://github.com/ejgallego/coq-lsp)) -- optional, needed only for the interactive tools (`rocq_query`, `rocq_assumptions`, `rocq_start`, `rocq_check`, `rocq_step_multi`, `rocq_toc`, `rocq_notations`). If `pet` is not installed, the compile and verify tools still work.
- **Python 3.11+**

## Installation

Using [uv](https://docs.astral.sh/uv/):

```bash
# Install (includes pytanque for interactive tools)
uv pip install -e .
```

For development (includes pytest):

```bash
uv pip install -e ".[dev]"
```

## Tools

The server exposes eleven MCP tools:

### Compilation tools (coqc-based, no pytanque needed)

| Tool | Description |
|------|-------------|
| **`rocq_compile`** | Batch-compile Rocq source code via coqc. Best for checking a finished proof. On error, returns error positions and a `state_capture_status` field; when `pet`/coq-lsp is available and the failure is inside a proof, also returns a reusable `state_id` and the goals at the error position. For iterative development, prefer `rocq_check`. |
| **`rocq_compile_file`** | Like `rocq_compile` but takes a file path instead of source string. More efficient for large files (avoids transmitting full source over MCP). Cleans up compilation artifacts but preserves the source file. When `pet`/coq-lsp is available and the failure is inside a proof, also returns a reusable `state_id` and the goals at the error position via `state_capture_status`. |
| **`rocq_verify`** | Verify that a proof actually proves the original statement. Wraps in a `Module M.` sandbox to catch type redefinition, `Admitted`/`Abort`, custom axioms, and statement mismatches. Run after `rocq_compile` succeeds. |

### Interactive tools (pytanque-based, require `pet`)

| Tool | Description |
|------|-------------|
| **`rocq_query`** | Search the Rocq environment — find lemmas, check types, inspect definitions. Three context modes: **preamble** (import commands as a string), **file** (a `.v` file path whose definitions are in scope), or **from_state** (a live `state_id` from a `rocq_check` session — the query sees opened scopes, hypotheses, and local definitions). Use `from_state=<state_id>` to introspect mid-proof without re-specifying preamble. Optional `max_results` parameter limits output for broad searches. Does not modify any proof state. |
| **`rocq_assumptions`** | List the axioms a theorem depends on. Takes a required `file` parameter (path to the `.v` file where the theorem is defined) to set up the full environment. Returns `assumptions: list[str]` of `"name : type"` pairs from `Print Assumptions` (empty when the theorem is closed under the global context) plus the full `raw_output` for agents that want it. No classification — `rocq_assumptions` is pure introspection; the agent decides what's safe to trust. Use `rocq_verify` for a sandboxed admit-free / axiom-policy decision on a candidate proof. |
| **`rocq_start`** | Start an interactive proof session and return proof goals. Three modes: (1) by theorem name, (2) by position — jump to any point in a file to inspect proof goals there (e.g., error positions from `rocq_compile`), (3) from imports. Returns a `state_id` for use with `rocq_check` and `rocq_step_multi`. Optional `force_restart=True` kills pet and clears the state table — recovery primitive for accumulated RAM bloat, indexing corruption, or a state expiry that repeats after a plain retry (see Concurrency model). |
| **`rocq_check`** | Run proof commands with cached imports — fast iterative checking. On error, returns `last_valid_state_id` for immediate recovery via `rocq_check(from_state=...)` or `rocq_step_multi(from_state=...)`. Includes `stale_warning` if the source file was modified since session start. |
| **`rocq_step_multi`** | Try multiple tactics at once — find what works without guessing. Useful for auto-solving subgoals (pass standard automation tactics) or exploring proof structure. Does not advance the state; commit the winner with `rocq_check`. Max 20 tactics per call. |
| **`rocq_toc`** | Get the structure of a `.v` file: all definitions, lemmas, theorems, and sections as a hierarchical outline. Does not require an active session. |
| **`rocq_notations`** | List all notations in a Rocq statement and how they resolve (which scope, which module). Helps debug notation ambiguity (e.g., is `+` in `nat_scope` or `Z_scope`?). |
| **`rocq_diag`** | Operational diagnostics: pet health, memory headroom, recent errors. Use after `pet_restarted: True` to diagnose what happened, or before a long `vm_compute` to check memory headroom. |

> **Stale file warning:** Interactive sessions (`rocq_start` / `rocq_check` / `rocq_step_multi`) read the `.v` file at session start and do not track subsequent edits. If another process or agent modifies the file while a session is active, the proof state becomes stale and tactics may fail or produce wrong results. In multi-agent setups, **work on a copy of the file** for interactive proving, or restart the session with `rocq_start` after edits. A `stale_warning` field is returned when a file modification is detected. See also the [Concurrency model](#concurrency-model) section below.

> **Workspace auto-detection:** When a file-accepting tool (`rocq_compile_file`, `rocq_query`, `rocq_assumptions`, `rocq_toc`, `rocq_start`) is called without an explicit `workspace`, the server walks up from the file's directory looking for `_RocqProject`, `_CoqProject`, or `dune-project` markers and uses the directory of the innermost match. Falls back to `ROCQ_WORKSPACE` if no marker is found. Pass `workspace=` explicitly to override (e.g. for monorepos with nested project files).

## Recommended usage patterns

### Multi-tactic exploration: `rocq_check` then `rocq_step_multi`

To explore N alternative tactics from a known good state, advance the
state with `rocq_check` first, then branch with `rocq_step_multi`:

    # Step 1: confirm the prefix and advance.
    result = rocq_check(from_state=S, body="intros n m H.")
    new_state = result["state_id"]

    # Step 2: try alternatives from that state.
    rocq_step_multi(from_state=new_state, tactics=[
        "by ring.",
        "by lia.",
        "by reflexivity.",
    ])

This is more efficient than passing the prefix repeatedly inside
`tactics=[...]` (each tactic would re-run the prefix).  It also makes
the agent's intent — "I'm confident in the prefix; explore the next
step" — explicit.

### Imports and scopes in `rocq_query`

Statements like `Require Import`, `From X Require Y`, `Open Scope`,
`Set`, `Unset`, `Local`, and `Section` must go in the `preamble=`
parameter (a multi-line string), not in `body=`:

    rocq_query(
        preamble="From Coq Require Import Reals.\nOpen Scope R_scope.",
        command="Search (_ + _).",
    )

Why: each statement in `body=` runs in isolation, so `Open Scope`
in body would not propagate to the next statement.  For multi-import
preambles, prefer `file=<path>` to a `.v` file containing the imports
— more reliable when the imports include `Set` / `Unset` directives
that may need a specific ordering.

For mid-proof queries — e.g. `Search` against the live proof state —
use `from_state=<state_id>` instead of preamble; the live state
already has all imports and scopes set up.

### Failure envelope and `reason` taxonomy

Every failure response carries `{success: False, error: str, reason: str}` so an agent can dispatch on `reason` without parsing message text. The same `reason` is recorded into the `recent_errors` ring buffer that `rocq_diag` returns. Values:

- **Validation / lookup** (set by tools before reaching `pet`): `"validation"`, `"not_found"` (typo on `rocq_start` / `rocq_assumptions`).
- **Pet-side** (set by `_run_with_pet` on subprocess-level failures): `"timeout"`, `"crashed"`, `"memory_exhausted"`, `"lock_contended"`, `"unavailable"`. When pet had to be killed, the response also carries `pet_restarted: True`.
- **`rocq_check` mid-batch**: `"tactic_failed"` (Coq rejected the tactic — distinct from a transport-level `"crashed"`).
- **`rocq_compile` / `rocq_compile_file`**: `"compile_error"` (coqc returned non-zero).
- **`rocq_verify`-specific**: `"compile_error"`, `"axiom_dependency"` (proof relies on `Admitted`/admit/custom axiom), `"type_mismatch"` (Phase 3 found the proof's type differs from the problem's type).

When a tool returns `pet_restarted: True`, call `rocq_diag` for memory headroom and recent-error history.

### `file_diagnostics`: surfacing silent file-level errors

`rocq_start` and `rocq_toc` may attach a `file_diagnostics: str` field to their response when the file under inspection has coqc-visible errors that pet's RPC interface doesn't expose. Two common triggers:

- A `Require Import` resolves to no physical path (`-Q` flag missing or wrong) — pet silently treats the module body as empty, so any downstream `pet.start` finds no theorems and pet.toc returns an empty outline. The user gets `Theorem_not_found` or an empty TOC instead of "your load path is broken."
- An earlier declaration in the file failed to type-check (e.g. referenced a symbol from the failed import). The target theorem might still parse fine, so `rocq_start` returns `success=True` with no warning — yet the file's environment is degraded.

When a `file_diagnostics` field is present, **trust it as the actual cause**. The primary error message (`Theorem_not_found`, empty TOC) is downstream; `file_diagnostics` carries the upstream coqc output that explains why.

The check uses coqc out-of-band (independent of pet) and skips silently if coqc isn't on PATH, the file compiles cleanly, or the check times out. Latency cost is one coqc invocation per call site that triggers the check (theorem-mode `rocq_start` success and failure; `rocq_toc` when pet returns an empty outline).

### Concurrency model

*Background (both audiences):* `rocq-mcp` is **single-tenant per process**.  All agent-facing state — the live `state_id` table, the import cache, the active workspace, and the single `pet` subprocess — is process-global.  Actively-used states are LRU-protected: a `state_id` you keep querying via `from_state` will not be evicted by a peer caller churning through new states (see `ROCQ_MAX_STATES`).  The remaining cross-agent costs are workspace-swap latency, pet RAM growth from accumulated Fleche cache, and the rare case of a peer calling `force_restart=True` (which kills pet under everyone).

**Agent-side recovery: `rocq_start(..., force_restart=True)`.**  When a `state_id` you actively depend on goes missing despite the LRU floor — typically because a peer just force-restarted pet — `rocq_start` with `force_restart=True` is the recovery.  This kills pet, clears the state table, respawns a fresh pet, and returns a new `state_id`.  Note that "fresh" is point-in-time: a different concurrent caller can `force_restart` again right after, so this is recovery, not enforced isolation.  For non-contention triggers (RAM bloat, indexing corruption) the same call applies.

**Operator-side hardening:** the cleanest deployment is one `rocq-mcp` subprocess per concurrent agent.  Over stdio this happens naturally when each MCP client launches its own server; the case that needs care is parallel sub-agents within one client, which inherit the parent's MCP connections and share one `rocq-mcp`.  If you're orchestrating parallel Rocq work, prefer separate top-level invocations over one parent with concurrent sub-agents.

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `ROCQ_WORKSPACE` | current directory | Working directory for Rocq compilation; used as the final fallback when no project marker is found by walking up from the file. When set explicitly, all workspace parameters are constrained to this directory or its subdirectories. |
| `ROCQ_COQC_TIMEOUT` | `60` | Timeout (seconds) for `rocq_compile` |
| `ROCQ_VERIFY_TIMEOUT` | `120` | Timeout (seconds) for `rocq_verify` |
| `ROCQ_PET_TIMEOUT` | `30` | Timeout (seconds) for pytanque-based tools |
| `ROCQ_QUERY_TIMEOUT_CAP` | `300` | Cap (seconds) on the per-call `timeout` parameter of `rocq_query`; larger values are clamped and the response carries `clamped_timeout: <cap>` |
| `ROCQ_ENRICHMENT_TIMEOUT_CAP` | `5.0` | Cap (seconds) on per-call proof-state capture after a `rocq_compile` / `rocq_compile_file` failure |
| `ROCQ_MAX_PET_RSS_MB` | `min(50% of system RAM, 16384)` | Maximum pet subprocess RSS (MB). On breach, the call aborts via the timeout recovery path; response includes `reason: "memory_exhausted"` and `pet_restarted: True`. |
| `ROCQ_MAX_STATES` | `1000` | Cap on the in-memory state table (LRU-evicted). The entry itself is tiny; the real cost lives in pet's Fleche cache and is bounded by `ROCQ_MAX_PET_RSS_MB`. Bump if two or more callers share this process (e.g. parallel sub-agents) and parked states get evicted before they're reused. |
| `ROCQ_COQC_BINARY` | `coqc` | Path to the `coqc` binary |
| `ROCQ_MAX_SOURCE_SIZE` | `1000000` | Maximum source size in bytes |

## Security Model

The verification tool (`rocq_verify`) uses defense in depth with three verification phases and multiple security layers.

### Verification phases

`rocq_verify` tries up to three phases in sequence, falling back to the next if the previous one times out:

1. **Phase 1 -- Module M sandbox.** The proof is wrapped inside `Module M. ... End M.`. The theorem is re-stated outside and proved via `exact M.<name>`. This is the strongest sandbox but can time out on compute-heavy proofs.

2. **Phase 2 -- Shared-defs template.** For problems with Inductive/Record/Definition types, type definitions are placed outside Module M to avoid nominal typing mismatches, while the proof stays inside the sandbox. Uses pytanque's `toc` to extract problem structure. Falls back from Phase 1 when type incompatibilities are detected.

3. **Phase 3 -- Direct verification.** When Phase 1 or Phase 2 times out or fails, the proof is compiled standalone (no Module M) with the full original timeout budget. Correctness is verified by comparing `Check <name>.` output against the problem statement's expected type after normalization. Additional security checks compensate for the lack of a sandbox (see below). This phase handles compute-heavy proofs that are too slow under Module M wrapping.

### Layer 1: Module M sandbox (Phases 1 & 2)

The Module M sandbox prevents:

- **Type redefinition cheating** -- Inductive/Record types are generative in Rocq, so redefining `nat` as `bool` inside Module M creates an incompatible type that cannot unify with the real `nat` outside.
- **Axiom spoofing** -- User-declared axioms receive an `M.` prefix in `Print Assumptions` output, which the stdlib whitelist rejects.
- **`Admitted`/`Abort` usage** -- Caught by `Print Assumptions`.
- **Module escape** -- `End M.` and `Reset`/`Back`/`Undo` are forbidden commands (see Layer 2).

### Layer 2: Forbidden command scanning

Source code is scanned for dangerous commands **after stripping comments**. The comment scanner matches Rocq's lexer exactly, including string literal tracking inside comments (preventing desynchronization attacks like `(* " (* " *) End M.`). Comments are replaced with spaces to preserve word boundaries.

Forbidden commands:

| Category | Commands |
|----------|----------|
| Filesystem | `Redirect`, `Extraction "..."`, `Separate Extraction`, `Recursive Extraction`, `Extraction Library`, `Cd`, `Load` |
| Code loading | `Declare ML Module`, `Add LoadPath`, `Add Rec LoadPath`, `Add ML Path` |
| Sandbox escape | `End M.`, `Reset`, `Back`, `Undo` |
| Safety bypass | `bypass_check`, `Unset Guard Checking`, `Unset Positivity Checking`, `Unset Universe Checking` |
| Escape hatches | `Drop` (OCaml toplevel) |

### Layer 3: Print Assumptions axiom whitelist

After compilation, `Print Assumptions` is checked against a whitelist of standard library axioms (classical logic, functional extensionality, Reals axioms, primitive int/float/array/string operations, mathcomp.classical re-exports, etc.). Axioms with qualified names must have a recognized stdlib prefix (`Coq.*`, `Rocq.*`, `Stdlib.*`, `Corelib.*`, the full `mathcomp.classical.boolp.*` / `mathcomp.classical.classical_sets.*`, or known module prefixes like `ClassicalDedekindReals.*`). Bare module-name prefixes (e.g. a workspace-supplied `boolp.v`) are intentionally **not** trusted, so a user `Axiom EM : False.` cannot be auto-trusted just because it mimics mathcomp's short form. The `M.` prefix on user-declared axioms inside Phase 1 / 2 Module M sandboxing ensures they are always rejected.

Printing flags (`Set Printing All`, `Set Printing Universes`, `Set Printing Width`) are reset after `End M.` to prevent corruption of `Print Assumptions` output format.

### Phase 3 security checks

Without the Module M sandbox, Phase 3 applies additional checks to compensate:

- **Forbidden commands** -- Same scanning as Phases 1 & 2 (Layer 2).
- **Incomplete proof rejection** -- `Admitted`, `admit`, and `give_up` in the proof source are rejected outright.
- **Axiom-introducing commands blocked** -- `Axiom`, `Parameter`, and `Conjecture` declarations are rejected. (`Variable` and `Hypothesis` are allowed since they are section-local and become parameters after `End Section`, not global axioms.)
- **Print Assumptions check** -- Same axiom whitelist as Phases 1 & 2 (Layer 3). However, without the `M.` prefix from Module M, user-declared axioms could potentially spoof whitelisted names.
- **Type comparison** -- The proven type (via `Check @<name>.` with `Set Printing All`) is normalized and compared to the expected type from the problem statement. Universe annotations are stripped before comparison.

**Known limitations of Phase 3:**

- Without Module M, type redefinition attacks are not caught (e.g., redefining `nat` as `bool` then proving a trivially true statement).
- Notation/scope redefinition before identically-texted definitions can change kernel semantics without being detected by type comparison.
- Stdlib function shadowing (redefining functions called by the problem's definition) is not covered.

The `verification_method` field in the result indicates which phase was used (`"module_m"`, `"shared_defs"`, or `"direct"`).

### Trusted anchor

**Important:** The `problem_statement` parameter is treated as a **trusted anchor**. The server verifies that the proof proves the given statement, but does NOT verify that the statement itself is the correct problem. Callers must ensure `problem_statement` comes from a trusted source (e.g., a file on disk), not from the LLM being evaluated.

### Path validation

All tools that accept file paths validate that resolved paths stay within the configured workspace directory (preventing path traversal attacks).

### Project file security

When `_RocqProject` or `_CoqProject` is present, the server parses it for coqc load-path flags (`-Q`, `-R`, `-I`). For **dune projects** (no project file but a `dune-project` file exists), the server runs `dune coq top` once per `(coq.theory ...)` stanza in the workspace and unions the resulting flags into a generated `_RocqProject` so coq-lsp also picks them up. Querying every theory is required for multi-theory workspaces; querying just one would leave cross-theory imports broken. This generated file (marked with a `# Auto-generated by rocq-mcp from dune` header) stays in the workspace and should be added to `.gitignore`. Existing user-created project files are never overwritten. For safety:

- **`-arg` allowlist** -- Only known-safe flags are passed through (e.g., `-noinit`, `-w`, `-impredicative-set`). Dangerous flags like `-load-vernac-source` are silently dropped.
- **Path containment** -- For `_RocqProject`/`_CoqProject`, directories in `-Q`/`-R`/`-I` must resolve within the workspace. Absolute paths and `../` traversals outside the workspace are rejected. For dune-detected paths, containment is checked against the dune project root (the directory containing `dune-project`), since build artifacts typically live in `_build/` at the project root.

## Running

The server uses stdio transport:

```bash
rocq-mcp
```

### MCP client configuration

Add to your MCP client configuration (e.g., Claude Desktop, Claude Code):

```json
{
  "mcpServers": {
    "rocq-mcp": {
      "command": "rocq-mcp",
      "env": {
        "ROCQ_WORKSPACE": "/path/to/your/rocq/project"
      }
    }
  }
}
```

## Running Tests

```bash
uv run pytest
```

Tests for pytanque-based tools (`rocq_query`, `rocq_assumptions`, `rocq_start`, `rocq_check`, `rocq_step_multi`, `rocq_toc`, `rocq_notations`) require `pet` to be installed. Integration tests will be skipped automatically if it is not available.

## Project Structure

```
src/rocq_mcp/
  __init__.py            Package init
  server.py              MCP server, 11 @mcp.tool wrappers, pet subprocess management
  compile.py             coqc-based tools: compile, compile_file, verify
  compile_enrichment.py  Compile-error-state orchestration (PET state capture)
  diag.py                rocq_diag snapshot builder (pet uptime, memory, recent errors)
  interactive.py         pytanque-based tools: start, check, step_multi, query, assumptions, toc, notations
  verify.py              Rocq lexer scanner, Module M. verification, Print Assumptions parsing
tests/
  conftest.py           Shared fixtures
  test_compile.py       Tests for rocq_compile
  test_compile_file.py  Tests for rocq_compile_file
  test_verify.py        Tests for rocq_verify
  test_assumptions.py   Tests for rocq_assumptions
  test_auto_solve.py    Tests for sentence utilities and step_multi auto-solving
  test_server.py        Tests for server helpers (_format_error, _parse_project_flags, etc.)
  test_format_error.py  Tests for error formatting
  test_query.py         Tests for rocq_query (requires pet)
  test_start.py         Tests for rocq_start (requires pet)
  test_check.py         Tests for rocq_check (requires pet)
  test_step_multi.py    Tests for rocq_step_multi
  test_toc.py           Tests for rocq_toc
  test_notations.py     Tests for rocq_notations
  test_timeout.py       Tests for timeout handling
  test_integration.py   Integration tests
```

## License

Apache 2.0 -- see [LICENSE](LICENSE) for details.
