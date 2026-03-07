# rocq-mcp

[![CI](https://img.shields.io/github/actions/workflow/status/llm4rocq/rocq-mcp-v2/ci.yml?branch=main&style=for-the-badge)](https://github.com/llm4rocq/rocq-mcp-v2/actions/workflows/ci.yml)
[![Python 3.11+](https://img.shields.io/badge/python-3.11+-blue.svg?style=for-the-badge)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg?style=for-the-badge)](https://github.com/llm4rocq/rocq-mcp-v2/blob/main/LICENSE)

An [MCP](https://modelcontextprotocol.io/) server for [Rocq](https://rocq-prover.org/) (formerly Coq) proof development. It exposes compilation, verification, querying, and interactive tactic stepping as MCP tools, so that LLM agents can write and check Rocq proofs.

## Prerequisites

- **Rocq / Coq** -- `coqc` must be on your `PATH` (needed by all tools).
- **pet** (from [coq-lsp](https://github.com/ejgallego/coq-lsp)) -- optional, needed only for the `rocq_query` and `rocq_step` tools. If `pet` is not installed, the compile and verify tools still work.
- **Python 3.11+**

## Installation

Using [uv](https://docs.astral.sh/uv/):

```bash
# Core (compile + verify tools only)
uv pip install -e .

# With interactive pytanque support (query + step tools)
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

The server exposes four MCP tools:

| Tool | Description |
|------|-------------|
| **`rocq_compile`** | Compile Rocq source code and return structured errors. Use this as the first step for any proof -- 81% of proofs succeed via direct compilation. |
| **`rocq_verify`** | Verify that a proof actually proves the original statement. Uses a conservative `Module M.` template to catch type redefinition cheating, `Admitted`/`Abort`, custom axioms, and statement mismatches. Standard mathematical axioms (classical logic, Reals, etc.) are accepted. |
| **`rocq_query`** | Run a Rocq query command (`Search`, `Check`, `Print`, `About`) and return results. Requires `pet`. Does not modify any proof state. |
| **`rocq_step`** | Execute a tactic in an interactive proof session and return goals. Requires `pet`. Provide a `.v` file path and `theorem` name on the first call to start a session; subsequent calls only need the tactic. Unlike `rocq_compile`/`rocq_verify` which accept source code strings, this tool requires the proof to be written to a file first. |

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `ROCQ_WORKSPACE` | current directory | Working directory for Rocq compilation |
| `ROCQ_COQC_TIMEOUT` | `60` | Timeout (seconds) for `rocq_compile` |
| `ROCQ_VERIFY_TIMEOUT` | `120` | Timeout (seconds) for `rocq_verify` |
| `ROCQ_PET_TIMEOUT` | `30` | Timeout (seconds) for `rocq_query` and `rocq_step` |
| `ROCQ_COQC_BINARY` | `coqc` | Path to the `coqc` binary |
| `ROCQ_MAX_SOURCE_SIZE` | `1000000` | Maximum source size in bytes |

## Security Model

The verification tool (`rocq_verify`) wraps the submitted proof inside a Rocq `Module M.` sandbox. This prevents:

- **Type redefinition cheating** (e.g., redefining `nat` as `bool`)
- **Axiom spoofing** (user-declared axioms get an `M.` prefix, rejected by the stdlib whitelist)
- **`Admitted`/`Abort` usage** (caught by `Print Assumptions`)
- **Module escape attempts** (Rocq prevents reopening `Module M`)

**Important:** The `problem_statement` parameter is treated as a **trusted anchor**. The server verifies that the proof proves the given statement, but does NOT verify that the statement itself is the correct problem. Callers must ensure `problem_statement` comes from a trusted source (e.g., a file on disk), not from the LLM being evaluated.

Source code containing dangerous commands is rejected to prevent filesystem side effects: `Redirect`, `Extraction "..."`, `Separate Extraction`, `Extraction Library`, `Drop`, `Cd`, `Load`, and `Declare ML Module`.

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

Tests for `rocq_query` and `rocq_step` require `pet` to be installed and will be skipped automatically if it is not available.

## Project Structure

```
src/rocq_mcp/
  __init__.py       Package init
  server.py         MCP server, tool definitions, pet subprocess management
  verify.py         Module M. verification template, Print Assumptions parsing
tests/
  test_compile.py   Tests for rocq_compile
  test_verify.py    Tests for rocq_verify
  test_query.py     Tests for rocq_query (requires pet)
  test_step.py      Tests for rocq_step (requires pet)
  test_integration.py  Integration tests
```

## License

Apache 2.0 — see [LICENSE](LICENSE) for details.
