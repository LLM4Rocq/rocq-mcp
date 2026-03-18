# rocq-mcp

[![CI](https://img.shields.io/github/actions/workflow/status/LLM4Rocq/rocq-mcp/ci.yml?branch=main&style=for-the-badge)](https://github.com/LLM4Rocq/rocq-mcp/actions/workflows/ci.yml)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg?style=for-the-badge)](https://github.com/LLM4Rocq/rocq-mcp/blob/main/LICENSE)

An [MCP](https://modelcontextprotocol.io/) server for [Rocq](https://rocq-prover.org/) (formerly Coq) proof development. It exposes compilation, verification, automated proving, querying, and interactive tactic stepping as MCP tools, so that LLM agents can write and check Rocq proofs.

## Prerequisites

- **Rocq / Coq** -- `coqc` must be on your `PATH` (needed by all tools).
- **pet** (from [coq-lsp](https://github.com/ejgallego/coq-lsp)) -- optional, needed only for the interactive tools (`rocq_query`, `rocq_step`, `rocq_step_multi`, `rocq_toc`, `rocq_notations`). If `pet` is not installed, the compile, verify, and auto_solve tools still work.
- **Python 3.11+**

## Installation

Using [uv](https://docs.astral.sh/uv/):

```bash
# Core (compile + verify + auto_solve tools only)
uv pip install -e .

# With interactive pytanque support (all 8 tools)
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

The server exposes eight MCP tools:

### Compilation tools (coqc-based, no pytanque needed)

| Tool | Description |
|------|-------------|
| **`rocq_compile`** | Compile Rocq source code and return structured errors. Use this as the first step for any proof -- 81% of proofs succeed via direct compilation. |
| **`rocq_verify`** | Verify that a proof actually proves the original statement. Uses a conservative `Module M.` template to catch type redefinition cheating, `Admitted`/`Abort`, custom axioms, and statement mismatches. Standard mathematical axioms (classical logic, Reals, etc.) are accepted. |
| **`rocq_auto_solve`** | Try to prove a theorem using standard automation tactics (`trivial`, `reflexivity`, `auto`, `lia`, `lra`, `ring`, `field`, `firstorder`, etc.). Useful as a quick check before manual proof construction. Optionally accepts preamble tactics (e.g., `intros. simpl.`). |

### Interactive tools (pytanque-based, require `pet`)

| Tool | Description |
|------|-------------|
| **`rocq_query`** | Run a Rocq query command (`Search`, `Check`, `Print`, `About`) and return results. Does not modify any proof state. |
| **`rocq_step`** | Execute a tactic in an interactive proof session and return goals (including shelved and given-up goals). Provide a `.v` file path and `theorem` name on the first call to start a session; subsequent calls only need the tactic. |
| **`rocq_step_multi`** | Try multiple tactics against the current proof state and return all results without advancing the session. Useful for quickly testing which automation tactic works. The LLM then picks the winner and commits via `rocq_step`. Max 20 tactics per call. |
| **`rocq_toc`** | Get the structure of a `.v` file: all definitions, lemmas, theorems, and sections as a hierarchical outline. Does not require an active session. |
| **`rocq_notations`** | List all notations in a Rocq statement and how they resolve (which scope, which module). Helps debug notation ambiguity (e.g., is `+` in `nat_scope` or `Z_scope`?). |

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `ROCQ_WORKSPACE` | current directory | Working directory for Rocq compilation. When set, all workspace parameters are constrained to this directory or its subdirectories. |
| `ROCQ_COQC_TIMEOUT` | `60` | Timeout (seconds) for `rocq_compile` and `rocq_auto_solve` |
| `ROCQ_VERIFY_TIMEOUT` | `120` | Timeout (seconds) for `rocq_verify` |
| `ROCQ_PET_TIMEOUT` | `30` | Timeout (seconds) for pytanque-based tools |
| `ROCQ_COQC_BINARY` | `coqc` | Path to the `coqc` binary |
| `ROCQ_MAX_SOURCE_SIZE` | `1000000` | Maximum source size in bytes |

## Security Model

The verification tool (`rocq_verify`) uses defense in depth with three layers:

### Layer 1: Module M sandbox

The submitted proof is wrapped inside `Module M. ... End M.`. The theorem is re-stated outside the module and proved via `exact M.<name>`. This prevents:

- **Type redefinition cheating** -- Inductive/Record types are generative in Rocq, so redefining `nat` as `bool` inside Module M creates an incompatible type that cannot unify with the real `nat` outside.
- **Axiom spoofing** -- User-declared axioms receive an `M.` prefix in `Print Assumptions` output, which the stdlib whitelist rejects.
- **`Admitted`/`Abort` usage** -- Caught by `Print Assumptions`.
- **Module escape** -- `End M.` and `Reset`/`Back`/`Undo` are forbidden commands (see Layer 2).

For problems containing Inductive/Record/Definition types, a **Phase 2 fallback** (shared-defs template) automatically places type definitions outside Module M to avoid nominal typing mismatches, while keeping the proof inside the sandbox. This uses pytanque's `toc` to extract problem structure.

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

### Trusted anchor

**Important:** The `problem_statement` parameter is treated as a **trusted anchor**. The server verifies that the proof proves the given statement, but does NOT verify that the statement itself is the correct problem. Callers must ensure `problem_statement` comes from a trusted source (e.g., a file on disk), not from the LLM being evaluated.

### Path validation

All tools that accept file paths validate that resolved paths stay within the configured workspace directory (preventing path traversal attacks).

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

Tests for pytanque-based tools (`rocq_query`, `rocq_step`, `rocq_step_multi`, `rocq_toc`, `rocq_notations`) require `pet` to be installed. Integration tests will be skipped automatically if it is not available.

## Project Structure

```
src/rocq_mcp/
  __init__.py       Package init
  server.py         MCP server, 8 tool definitions, pet subprocess management
  verify.py         Rocq lexer scanner, Module M. verification, Print Assumptions parsing
tests/
  test_compile.py       Tests for rocq_compile
  test_verify.py        Tests for rocq_verify
  test_auto_solve.py    Tests for rocq_auto_solve (unit + integration)
  test_query.py         Tests for rocq_query (requires pet)
  test_step.py          Tests for rocq_step (requires pet)
  test_step_enhanced.py Tests for rocq_step complete_goals enhancement
  test_step_multi.py    Tests for rocq_step_multi
  test_toc.py           Tests for rocq_toc
  test_notations.py     Tests for rocq_notations
  test_integration.py   Integration tests
```

## License

Apache 2.0 -- see [LICENSE](LICENSE) for details.
