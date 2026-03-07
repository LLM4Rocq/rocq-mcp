# rocq-mcp

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
| **`rocq_step`** | Execute a tactic in an interactive proof session and return goals. Requires `pet`. Provide `file` and `theorem` on the first call to start a session; subsequent calls only need the tactic. |

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `ROCQ_WORKSPACE` | current directory | Working directory for Rocq compilation |
| `ROCQ_COQC_TIMEOUT` | `60` | Timeout (seconds) for `rocq_compile` |
| `ROCQ_VERIFY_TIMEOUT` | `120` | Timeout (seconds) for `rocq_verify` |
| `ROCQ_PET_TIMEOUT` | `30` | Timeout (seconds) for `rocq_query` and `rocq_step` |
| `ROCQ_COQC_BINARY` | `coqc` | Path to the `coqc` binary |
| `ROCQ_MAX_SOURCE_SIZE` | `1000000` | Maximum source size in bytes |

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

TBD
