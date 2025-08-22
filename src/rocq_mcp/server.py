#!/usr/bin/env python3
"""
Rocq MCP Server

A Model Context Protocol server that provides tools for interacting with
the Rocq/Coq proof assistant using the Petanque protocol.
"""

import argparse
import asyncio
import atexit
import logging
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from mcp.server import Server, NotificationOptions
from mcp.server.models import InitializationOptions
import mcp.server.stdio
import mcp.types as types

from pytanque import Pytanque, PetanqueError

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global variables to maintain connection state
petanque_client: Optional[Pytanque] = None
petanque_process: Optional[subprocess.Popen] = None
current_states: Dict[str, Any] = {}  # Store proof states by session ID


def cleanup_petanque_process():
    """Clean up the petanque process on exit."""
    global petanque_process
    if petanque_process is not None:
        logger.info("Shutting down pet-server process...")
        try:
            petanque_process.terminate()
            # Give it a moment to terminate gracefully
            petanque_process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            logger.warning("pet-server didn't terminate gracefully, killing...")
            petanque_process.kill()
            petanque_process.wait()
        except Exception as e:
            logger.error(f"Error during pet-server cleanup: {e}")
        finally:
            petanque_process = None
            logger.info("pet-server process cleaned up")


def start_petanque_server(host: str = "127.0.0.1", port: int = 8833) -> None:
    """Start the petanque server process."""
    global petanque_process
    
    if petanque_process is not None:
        return  # Already running
    
    try:
        # Start pet-server process
        logger.info(f"Starting pet-server on {host}:{port}")
        petanque_process = subprocess.Popen(
            ["pet-server", "--address", host, "--port", str(port)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )
        
        # Give the server a moment to start
        time.sleep(2)
        
        # Check if process is still running
        if petanque_process.poll() is not None:
            stdout, stderr = petanque_process.communicate()
            raise RuntimeError(f"pet-server failed to start: {stderr}")
        
        logger.info(f"pet-server started successfully (PID: {petanque_process.pid})")
        
        # Register cleanup handlers
        atexit.register(cleanup_petanque_process)
        
        # Handle signals for graceful shutdown
        def signal_handler(signum, frame):
            logger.info(f"Received signal {signum}, shutting down...")
            cleanup_petanque_process()
            sys.exit(0)
        
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        
    except FileNotFoundError:
        raise RuntimeError("pet-server command not found. Please ensure it's installed and in PATH.")
    except Exception as e:
        cleanup_petanque_process()
        raise RuntimeError(f"Failed to start pet-server: {e}")


def get_client() -> Pytanque:
    """Get or create Petanque client connection."""
    global petanque_client
    if petanque_client is None:
        # Default connection parameters - these can be made configurable
        host = os.environ.get("PETANQUE_HOST", "127.0.0.1")
        port = int(os.environ.get("PETANQUE_PORT", "8833"))
        
        # Start petanque server if not already running
        start_petanque_server(host, port)
        
        # Wait a bit more for the server to be fully ready
        time.sleep(1)
        
        petanque_client = Pytanque(host, port)
        petanque_client.connect()
        logger.info(f"Connected to Petanque server at {host}:{port}")
    return petanque_client


# Create the MCP server
server = Server("rocq-mcp")


@server.list_tools()
async def handle_list_tools() -> List[types.Tool]:
    """List available tools."""
    return [
        types.Tool(
            name="rocq_start_proof",
            description="Start a proof session for a specific theorem in a Coq/Rocq file",
            inputSchema={
                "type": "object",
                "properties": {
                    "file_path": {
                        "type": "string",
                        "description": "Path to the Coq/Rocq file containing the theorem",
                    },
                    "theorem_name": {
                        "type": "string",
                        "description": "Name of the theorem to prove",
                    },
                    "session_id": {
                        "type": "string",
                        "description": "Unique session identifier for this proof session",
                    },
                    "pre_commands": {
                        "type": "string",
                        "description": "Optional commands to execute before starting the proof",
                        "default": None,
                    },
                },
                "required": ["file_path", "theorem_name", "session_id"],
            },
        ),
        types.Tool(
            name="rocq_run_tactic",
            description="Execute a tactic or command on the current proof state",
            inputSchema={
                "type": "object",
                "properties": {
                    "session_id": {
                        "type": "string",
                        "description": "Session identifier for the proof session",
                    },
                    "command": {
                        "type": "string",
                        "description": "The tactic or command to execute (e.g., 'induction n.', 'auto.', 'Search nat.')",
                    },
                    "timeout": {
                        "type": "integer",
                        "description": "Optional timeout in seconds for command execution",
                        "default": None,
                    },
                },
                "required": ["session_id", "command"],
            },
        ),
        types.Tool(
            name="rocq_get_goals",
            description="Get the current proof goals for a session",
            inputSchema={
                "type": "object",
                "properties": {
                    "session_id": {
                        "type": "string",
                        "description": "Session identifier for the proof session",
                    }
                },
                "required": ["session_id"],
            },
        ),
        types.Tool(
            name="rocq_get_premises",
            description="Get available premises (lemmas, definitions) for the current proof state",
            inputSchema={
                "type": "object",
                "properties": {
                    "session_id": {
                        "type": "string",
                        "description": "Session identifier for the proof session",
                    }
                },
                "required": ["session_id"],
            },
        ),
        types.Tool(
            name="rocq_parse_ast",
            description="Parse a command and return its Abstract Syntax Tree",
            inputSchema={
                "type": "object",
                "properties": {
                    "session_id": {
                        "type": "string",
                        "description": "Session identifier for the proof session (provides parsing context)",
                    },
                    "text": {
                        "type": "string",
                        "description": "The command text to parse (e.g., 'induction n', 'Search nat')",
                    },
                },
                "required": ["session_id", "text"],
            },
        ),
        types.Tool(
            name="rocq_get_state_at_position",
            description="Get the proof state at a specific position in a file",
            inputSchema={
                "type": "object",
                "properties": {
                    "file_path": {
                        "type": "string",
                        "description": "Path to the Coq/Rocq file",
                    },
                    "line": {
                        "type": "integer",
                        "description": "Line number (0-based indexing)",
                    },
                    "character": {
                        "type": "integer",
                        "description": "Character position within the line (0-based indexing)",
                    },
                },
                "required": ["file_path", "line", "character"],
            },
        ),
        types.Tool(
            name="rocq_get_file_toc",
            description="Get table of contents (available definitions and theorems) for a Coq/Rocq file",
            inputSchema={
                "type": "object",
                "properties": {
                    "file_path": {
                        "type": "string",
                        "description": "Path to the Coq/Rocq file",
                    }
                },
                "required": ["file_path"],
            },
        ),
        types.Tool(
            name="rocq_search",
            description="Search for theorems, definitions, and other objects in the current context",
            inputSchema={
                "type": "object",
                "properties": {
                    "session_id": {
                        "type": "string",
                        "description": "Session identifier for the proof session",
                    },
                    "query": {
                        "type": "string",
                        "description": "Search query (e.g., 'nat', '_ + _', 'forall n, n + 0 = n')",
                    },
                },
                "required": ["session_id", "query"],
            },
        ),
    ]


@server.call_tool()
async def handle_call_tool(
    name: str, arguments: Dict[str, Any]
) -> List[types.TextContent]:
    """Handle tool calls."""

    try:
        client = get_client()

        if name == "rocq_start_proof":
            file_path = arguments["file_path"]
            theorem_name = arguments["theorem_name"]
            session_id = arguments["session_id"]
            pre_commands = arguments.get("pre_commands")

            # Resolve absolute path
            abs_path = str(Path(file_path).resolve())

            # Start the proof session
            state = client.start(abs_path, theorem_name, pre_commands)

            # Store the state for this session
            current_states[session_id] = state

            # Get initial goals
            goals = client.goals(state)
            goals_text = "\n".join(
                [f"Goal {i+1}:\n{goal.pp}" for i, goal in enumerate(goals)]
            )

            result = (
                f"Started proof session for theorem '{theorem_name}' in {file_path}\n"
            )
            result += f"Session ID: {session_id}\n"
            result += f"State ID: {state.st}\n"
            result += f"Proof finished: {state.proof_finished}\n"
            result += f"Initial goals ({len(goals)}):\n{goals_text}"

            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_run_tactic":
            session_id = arguments["session_id"]
            command = arguments["command"]
            timeout = arguments.get("timeout")

            if session_id not in current_states:
                return [
                    types.TextContent(
                        type="text",
                        text=f"Error: No active session found for ID '{session_id}'. Use rocq_start_proof first.",
                    )
                ]

            # Get current state and run the command
            current_state = current_states[session_id]
            new_state = client.run(current_state, command, timeout=timeout)

            # Update stored state
            current_states[session_id] = new_state

            # Get feedback messages
            feedback_text = ""
            if new_state.feedback:
                feedback_text = "\nFeedback:\n" + "\n".join(
                    [f"[Level {level}] {msg}" for level, msg in new_state.feedback]
                )

            # Get current goals after command
            goals = client.goals(new_state)
            goals_text = ""
            if goals:
                goals_text = f"\nCurrent goals ({len(goals)}):\n" + "\n".join(
                    [f"Goal {i+1}:\n{goal.pp}" for i, goal in enumerate(goals)]
                )
            else:
                goals_text = "\nNo remaining goals - proof may be complete!"

            result = f"Executed: {command}\n"
            result += f"New state ID: {new_state.st}\n"
            result += f"Proof finished: {new_state.proof_finished}"
            result += feedback_text + goals_text

            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_get_goals":
            session_id = arguments["session_id"]

            if session_id not in current_states:
                return [
                    types.TextContent(
                        type="text",
                        text=f"Error: No active session found for ID '{session_id}'. Use rocq_start_proof first.",
                    )
                ]

            current_state = current_states[session_id]
            goals = client.goals(current_state)

            if not goals:
                result = "No current goals - proof may be complete!"
            else:
                result = f"Current goals ({len(goals)}):\n"
                result += "\n".join(
                    [f"Goal {i+1}:\n{goal.pp}" for i, goal in enumerate(goals)]
                )

            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_get_premises":
            session_id = arguments["session_id"]

            if session_id not in current_states:
                return [
                    types.TextContent(
                        type="text",
                        text=f"Error: No active session found for ID '{session_id}'. Use rocq_start_proof first.",
                    )
                ]

            current_state = current_states[session_id]
            premises = client.premises(current_state)

            result = f"Available premises ({len(premises)} total):\n"
            # Show first 20 premises to avoid overwhelming output
            for i, premise in enumerate(premises[:20]):
                result += f"{i+1}. {premise}\n"

            if len(premises) > 20:
                result += f"... and {len(premises) - 20} more premises"

            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_parse_ast":
            session_id = arguments["session_id"]
            text = arguments["text"]

            if session_id not in current_states:
                return [
                    types.TextContent(
                        type="text",
                        text=f"Error: No active session found for ID '{session_id}'. Use rocq_start_proof first.",
                    )
                ]

            current_state = current_states[session_id]
            ast = client.ast(current_state, text)

            result = f"AST for: {text}\n{ast}"
            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_get_state_at_position":
            file_path = arguments["file_path"]
            line = arguments["line"]
            character = arguments["character"]

            abs_path = str(Path(file_path).resolve())
            state = client.get_state_at_pos(abs_path, line, character)

            # Get goals at this position
            goals = client.goals(state)
            goals_text = ""
            if goals:
                goals_text = f"Goals at position ({len(goals)}):\n"
                goals_text += "\n".join(
                    [f"Goal {i+1}:\n{goal.pp}" for i, goal in enumerate(goals)]
                )
            else:
                goals_text = "No goals at this position"

            result = f"State at {file_path}:{line}:{character}\n"
            result += f"State ID: {state.st}\n"
            result += f"Proof finished: {state.proof_finished}\n"
            result += goals_text

            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_get_file_toc":
            file_path = arguments["file_path"]

            abs_path = str(Path(file_path).resolve())
            toc = client.toc(abs_path)

            result = f"Table of contents for {file_path}:\n"
            for name, definition in toc:
                result += f"- {name}: {definition}\n"

            return [types.TextContent(type="text", text=result)]

        elif name == "rocq_search":
            session_id = arguments["session_id"]
            query = arguments["query"]

            if session_id not in current_states:
                return [
                    types.TextContent(
                        type="text",
                        text=f"Error: No active session found for ID '{session_id}'. Use rocq_start_proof first.",
                    )
                ]

            current_state = current_states[session_id]
            # Execute search command and capture feedback
            # If query contains spaces or special characters, wrap in quotes
            if ' ' in query or any(c in query for c in ['_', '+', '-', '*', '(', ')', '[', ']']):
                search_command = f'Search "{query}".'
            else:
                search_command = f"Search {query}."
            new_state = client.run(current_state, search_command)

            # Extract search results from feedback
            if new_state.feedback:
                result = f"Search results for '{query}':\n"
                result_lines = []
                for level, msg in new_state.feedback:
                    result_lines.append(msg)
                
                # Limit output to avoid overwhelming responses
                max_results = 50
                if len(result_lines) > max_results:
                    result += "\n".join(result_lines[:max_results])
                    result += f"\n\n... and {len(result_lines) - max_results} more results (truncated for brevity)"
                else:
                    result += "\n".join(result_lines)
            else:
                result = f"No results found for search query: {query}"

            return [types.TextContent(type="text", text=result)]

        else:
            return [
                types.TextContent(type="text", text=f"Error: Unknown tool '{name}'")
            ]

    except PetanqueError as e:
        error_msg = f"Petanque error (code {e.code}): {e.message}"
        logger.error(error_msg)
        return [types.TextContent(type="text", text=f"Error: {error_msg}")]

    except Exception as e:
        error_msg = f"Unexpected error: {str(e)}"
        logger.error(error_msg, exc_info=True)
        return [types.TextContent(type="text", text=f"Error: {error_msg}")]


async def main():
    """Main entry point for the server."""
    parser = argparse.ArgumentParser(description="Rocq MCP Server")
    parser.add_argument(
        "--host", default="127.0.0.1", help="Petanque server host (default: 127.0.0.1)"
    )
    parser.add_argument(
        "--port", type=int, default=8833, help="Petanque server port (default: 8833)"
    )
    args = parser.parse_args()

    # Set environment variables for client configuration
    os.environ["PETANQUE_HOST"] = args.host
    os.environ["PETANQUE_PORT"] = str(args.port)

    # Run the MCP server
    async with mcp.server.stdio.stdio_server() as (read_stream, write_stream):
        await server.run(
            read_stream,
            write_stream,
            InitializationOptions(
                server_name="rocq-mcp",
                server_version="0.1.0",
                capabilities=server.get_capabilities(
                    notification_options=NotificationOptions(),
                    experimental_capabilities={},
                ),
            ),
        )


def cli():
    """CLI entry point for Poetry script."""
    asyncio.run(main())


if __name__ == "__main__":
    cli()
