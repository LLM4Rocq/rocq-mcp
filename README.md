# rocq-mcp

[![CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/rocq-mcp/ci.yml?branch=main&style=for-the-badge)](https://github.com/LLM4Rocq/rocq-mcp/actions/workflows/ci.yml)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg?style=for-the-badge)](https://github.com/LLM4Rocq/rocq-mcp/blob/main/LICENSE)

An [MCP](https://modelcontextprotocol.io/) server for [Rocq](https://rocq-prover.org/) (formerly Coq) proof development. It exposes compilation, verification, querying, and interactive tactic stepping as MCP tools, so that LLM agents can write and check Rocq proofs.

## Prerequisites

- **Rocq / Coq** -- `coqc` must be on your `PATH` (needed by all tools). If the workspace contains a `_RocqProject` or `_CoqProject` file, the server parses it for load-path flags (`-Q`, `-R`, `-I`). Otherwise it defaults to `-Q <workspace> Test`.
- **pet** (from [coq-lsp](https://github.com/ejgallego/coq-lsp)) -- optional, needed only for the interactive tools (`rocq_query`, `rocq_assumptions`, `rocq_start`, `rocq_check`, `rocq_step_multi`, `rocq_toc`, `rocq_notations`). If `pet` is not installed, the compile and verify tools still work.
- **Python 3.11+**

## Installation

Using [uv](https://docs.astral.sh/uv/):

```bash
# Core (compile + verify tools only)
uv pip install -e .

# With interactive pytanque support (all 11 tools)
uv pip install -e ".[interactive]"
```

pytanque is installed from Git:

```bash
uv pip install "pytanque @ git+https://github.com/LLM4Rocq/pytanque"
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
| **`rocq_compile`** | Batch-compile Rocq source code via coqc. Best for checking a finished proof. On error, returns error positions for jumping to interactive mode. For iterative development, prefer `rocq_check`. |
| **`rocq_compile_file`** | Like `rocq_compile` but takes a file path instead of source string. More efficient for large files (avoids transmitting full source over MCP). Cleans up compilation artifacts but preserves the source file. |
| **`rocq_verify`** | Verify that a proof actually proves the original statement. Wraps in a `Module M.` sandbox to catch type redefinition, `Admitted`/`Abort`, custom axioms, and statement mismatches. Run after `rocq_compile` succeeds. |

### Interactive tools (pytanque-based, require `pet`)

| Tool | Description |
|------|-------------|
| **`rocq_query`** | Search the Rocq environment — find lemmas, check types, inspect definitions. Two context modes: **preamble** (import commands as a string) or **file** (a `.v` file path whose definitions are in scope). Optional `max_results` parameter limits output for broad searches. Does not modify any proof state. |
| **`rocq_assumptions`** | Check what axioms a theorem depends on. Takes a required `file` parameter (path to the `.v` file where the theorem is defined) to set up the full environment. Returns `"closed"` (no axioms), `"standard_only"` (classical logic, Reals, etc.), or `"suspicious"` (unproved assumptions). |
| **`rocq_start`** | Start an interactive proof session and return proof goals. Three modes: (1) by theorem name, (2) by position — jump to any point in a file to inspect proof goals there (e.g., error positions from `rocq_compile`), (3) from imports. Returns a `state_id` for use with `rocq_check` and `rocq_step_multi`. |
| **`rocq_check`** | Run proof commands with cached imports — fast iterative checking. On error, returns `last_valid_state_id` for immediate recovery via `rocq_check(from_state=...)` or `rocq_step_multi(from_state=...)`. Includes `stale_warning` if the source file was modified since session start. |
| **`rocq_step_multi`** | Try multiple tactics at once — find what works without guessing. Useful for auto-solving subgoals (pass standard automation tactics) or exploring proof structure. Does not advance the state; commit the winner with `rocq_check`. Max 20 tactics per call. |
| **`rocq_toc`** | Get the structure of a `.v` file: all definitions, lemmas, theorems, and sections as a hierarchical outline. Does not require an active session. |
| **`rocq_notations`** | List all notations in a Rocq statement and how they resolve (which scope, which module). Helps debug notation ambiguity (e.g., is `+` in `nat_scope` or `Z_scope`?). |

> **Stale file warning:** Interactive sessions (`rocq_start` / `rocq_check` / `rocq_step_multi`) read the `.v` file at session start and do not track subsequent edits. If another process or agent modifies the file while a session is active, the proof state becomes stale and tactics may fail or produce wrong results. In multi-agent setups, **work on a copy of the file** for interactive proving, or restart the session with `rocq_start` after edits. A `stale_warning` field is returned when a file modification is detected.

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `ROCQ_WORKSPACE` | current directory | Working directory for Rocq compilation. When set, all workspace parameters are constrained to this directory or its subdirectories. |
| `ROCQ_COQC_TIMEOUT` | `60` | Timeout (seconds) for `rocq_compile` |
| `ROCQ_VERIFY_TIMEOUT` | `120` | Timeout (seconds) for `rocq_verify` |
| `ROCQ_PET_TIMEOUT` | `30` | Timeout (seconds) for pytanque-based tools |
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

After compilation, `Print Assumptions` is checked against a whitelist of standard library axioms (classical logic, functional extensionality, Reals axioms, etc.). Axioms with qualified names must have a recognized stdlib prefix (`Coq.*`, `Rocq.*`, `Stdlib.*`, or known module prefixes like `ClassicalDedekindReals.*`). The `M.` prefix on user-declared axioms ensures they are always rejected.

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

When `_RocqProject` or `_CoqProject` is present, the server parses it for coqc load-path flags (`-Q`, `-R`, `-I`). For safety:

- **`-arg` allowlist** -- Only known-safe flags are passed through (e.g., `-noinit`, `-w`, `-impredicative-set`). Dangerous flags like `-load-vernac-source` are silently dropped.
- **Path containment** -- Directories in `-Q`/`-R`/`-I` must resolve within the workspace. Absolute paths and `../` traversals outside the workspace are rejected.

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
  __init__.py       Package init
  server.py         MCP server, 11 tool definitions, pet subprocess management
  compile.py        coqc-based tools: compile, compile_file, verify
  interactive.py    pytanque-based tools: start, check, step_multi, query, assumptions, toc, notations
  verify.py         Rocq lexer scanner, Module M. verification, Print Assumptions parsing
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
