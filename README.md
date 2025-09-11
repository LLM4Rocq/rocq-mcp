# Rocq MCP Server

[![Tests](https://github.com/llm4rocq/rocq-mcp/actions/workflows/tests.yml/badge.svg?branch=main)](https://github.com/llm4rocq/rocq-mcp/actions/workflows/tests.yml)
[![Python 3.10+](https://img.shields.io/badge/python-3.10+-blue.svg)](https://www.python.org/downloads/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](https://github.com/llm4rocq/rocq-mcp/blob/main/LICENSE)

## Overview

This MCP server exposes the functionality of the Rocq/Coq proof assistant through a set of tools that can be used by MCP-compatible clients (like Claude Desktop). It uses the [Pytanque](https://github.com/LLM4Rocq/pytanque.git) to communicate with a [coq-lsp](https://github.com/LLM4Rocq/pytanque.git) via a Petanque server.

## Features

### Available Tools

- **rocq_start_proof**: Start a proof session for a specific theorem in a Coq/Rocq file
- **rocq_run_tactic**: Execute tactics or commands on the current proof state  
- **rocq_get_goals**: Get the current proof goals for a session
- **rocq_get_premises**: Get available premises (lemmas, definitions) for the current proof state
- **rocq_get_file_toc**: Get table of contents (available definitions and theorems) for a Coq/Rocq file
- **rocq_search**: Search for theorems, definitions, and other objects in the current context
- **rocq_parse_ast**: Parse a command and return its Abstract Syntax Tree _(only with the dev version of coq-lsp)_
- **rocq_get_state_at_position**: Get the proof state at a specific position in a file _(only with the dev version of coq-lsp)_

### Key Capabilities

- **Two communication modes**: 
  - **Stdio mode (default)**: direct communication with `pet` process via stdin/stdout.
  - **TCP mode**: socket-based communication with `pet-server` via TCP.
- **Interactive theorem proving**: Execute tactics and commands step by step
- **Comprehensive feedback**: Access all Rocq messages (errors, warnings, search results)
- **State management**: Navigate proof states and compare them
- **Session management**: Support multiple concurrent proof sessions

- **AST parsing**: Get abstract syntax trees for commands and file positions _(only with the dev version of coq-lsp)_
- **Position-based queries**: Get states at specific file positions _(only with the dev version of coq-lsp)_

## Prerequisites

**Install coq-lsp with Petanque support**:
```bash
# Install dependencies
opam install lwt logs coq-lsp

# Or install one of the dev versions of coq-lsp, e.g., for Coq.8.20
opam install lwt logs coq.8.20.0
opam pin add coq-lsp https://github.com/ejgallego/coq-lsp.git#v8.20
```

## Installation

### Install from GitHub (Recommended)

```bash
uv pip install git+https://github.com/llm4rocq/rocq-mcp.git
```

### Development Installation

1. Clone this repository
2. Use the project workflow:
   ```bash
   cd rocq-mcp
   uv sync
   ```

## Usage

### Running the MCP Server

```bash
# Default: stdio mode (uses 'pet' command directly)
rocq-mcp

# Use TCP mode for multi-client usage
rocq-mcp --tcp

# TCP mode with custom server configuration  
rocq-mcp --tcp --host 127.0.0.1 --port 8833
```

**Development mode (if using `uv sync`):**
```bash
uv run rocq-mcp
uv run rocq-mcp --tcp
```

**Communication Modes:**

- **Stdio mode (default)**: Spawns and communicates directly with the `pet` process via stdin/stdout. This is more efficient and simpler as it doesn't require a separate server process.
- **TCP mode**: Starts a `pet-server` process and communicates via TCP socket. Use this for multi-client usage scenarios where multiple applications need to connect to the same Petanque instance.

### MCP Client Configuration

Run the following command to install rocq-mcp for claude code.

```bash
claude mcp add rocq-mcp -- rocq-mcp

# if using uv
claude mcp add rocq-mcp -- uv run rocq-mcp
```

When you start a claude session, you can check the server with:

```
> /mcp
```

Then, simply ask claude a question.

```
> help me prove addnC in test.v
```

### Testing

```bash
# Install with dev dependencies
uv sync --dev

# Run tests
uv run pytest tests/
```

## Troubleshooting

### Common Issues

**Server Connection Errors**
- Verify port availability
- Check that coq-lsp is properly installed

**Installation Issues**
- Ensure coq-lsp is properly installed
- Install `lwt` and `logs` before `coq-lsp` (required for `pet-server`)
- Verify pytanque dependency is correctly resolved


_Note: This project was build with the help of Claude from the code of [pytanque](https://github.com/LLM4Rocq/pytanque.git)._


## Related Projects

- [pytanque](https://github.com/LLM4Rocq/pytanque.git): Python client for the Petanque protocol
- [coq-lsp](https://github.com/ejgallego/coq-lsp): Language server for Coq/Rocq
- [MCP](https://github.com/modelcontextprotocol): Model Context Protocol specification