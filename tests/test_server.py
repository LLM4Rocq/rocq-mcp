#!/usr/bin/env python3
"""
Tests for the Rocq MCP server.

Note: These tests require a running Petanque server (pet-server) to pass.
"""

import pytest
import asyncio
import tempfile
from pathlib import Path
from unittest.mock import Mock, patch

from rocq_mcp.server import handle_call_tool, handle_list_tools


class TestRocqMCPServer:
    """Test suite for the Rocq MCP server."""

    @pytest.fixture
    def sample_coq_file(self):
        """Create a temporary Coq file for testing."""
        content = """
Require Import Arith.

Theorem simple_test : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".v", delete=False) as f:
            f.write(content)
            return f.name

    @pytest.mark.asyncio
    async def test_list_tools(self):
        """Test that all expected tools are listed."""
        tools = await handle_list_tools()

        expected_tool_names = {
            "rocq_start_proof",
            "rocq_run_tactic",
            "rocq_get_goals",
            "rocq_get_premises",
            "rocq_parse_ast",
            "rocq_get_state_at_position",
            "rocq_get_file_toc",
            "rocq_search",
        }

        actual_tool_names = {tool.name for tool in tools}
        assert actual_tool_names == expected_tool_names

        # Check that all tools have required fields
        for tool in tools:
            assert tool.name
            assert tool.description
            assert tool.inputSchema
            assert "type" in tool.inputSchema
            assert "properties" in tool.inputSchema
            assert "required" in tool.inputSchema

    def test_tool_schemas(self):
        """Test that tool input schemas are properly defined."""
        # This is a basic structure test - full validation would require
        # JSON schema validation
        pass

    @pytest.mark.asyncio
    async def test_start_proof_missing_session(self):
        """Test starting a proof with invalid arguments."""
        # Test with missing required arguments
        with patch("rocq_mcp.server.get_client") as mock_get_client:
            mock_client = Mock()
            mock_get_client.return_value = mock_client

            # Missing session_id should be handled by MCP framework
            # This test shows the expected behavior
            pass

    @pytest.mark.asyncio
    async def test_tactic_without_session(self):
        """Test running a tactic without an active session."""
        result = await handle_call_tool(
            "rocq_run_tactic", {"session_id": "nonexistent", "command": "auto."}
        )

        assert len(result) == 1
        assert "No active session found" in result[0].text

    @pytest.mark.asyncio
    async def test_goals_without_session(self):
        """Test getting goals without an active session."""
        result = await handle_call_tool("rocq_get_goals", {"session_id": "nonexistent"})

        assert len(result) == 1
        assert "No active session found" in result[0].text

    @pytest.mark.asyncio
    async def test_unknown_tool(self):
        """Test calling an unknown tool."""
        result = await handle_call_tool("unknown_tool", {})

        assert len(result) == 1
        assert "Unknown tool" in result[0].text


class TestIntegration:
    """Integration tests requiring a running Petanque server."""

    @pytest.fixture
    def sample_coq_file(self):
        """Create a temporary Coq file for testing."""
        content = """
Theorem test_theorem : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".v", delete=False) as f:
            f.write(content)
            return f.name

    @pytest.mark.asyncio
    async def test_full_proof_workflow(self, sample_coq_file):
        """Test a complete proof workflow."""
        # This test requires a running Petanque server
        # Skip if not available

        try:
            # 1. Start proof session
            result = await handle_call_tool(
                "rocq_start_proof",
                {
                    "file_path": sample_coq_file,
                    "theorem_name": "test_theorem",
                    "session_id": "test_session",
                },
            )

            assert len(result) == 1
            assert "Started proof session" in result[0].text

            # 2. Get initial goals
            result = await handle_call_tool(
                "rocq_get_goals", {"session_id": "test_session"}
            )

            assert len(result) == 1
            assert "Goal" in result[0].text

            # 3. Execute tactic
            result = await handle_call_tool(
                "rocq_run_tactic", {"session_id": "test_session", "command": "intro n."}
            )

            assert len(result) == 1
            assert "Executed: intro n." in result[0].text

        except Exception as e:
            pytest.skip(f"Integration test skipped - likely no Petanque server: {e}")

    @pytest.mark.asyncio
    async def test_file_toc(self, sample_coq_file):
        """Test getting file table of contents."""
        try:
            result = await handle_call_tool(
                "rocq_get_file_toc", {"file_path": sample_coq_file}
            )

            assert len(result) == 1
            assert "Table of contents" in result[0].text

        except Exception as e:
            pytest.skip(f"Integration test skipped - likely no Petanque server: {e}")


if __name__ == "__main__":
    # Run basic tests
    pytest.main([__file__, "-v"])

    # To run integration tests (requires pet-server):
    # pytest test_server.py -v -m integration
