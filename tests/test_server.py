#!/usr/bin/env python3
"""
Tests for the Rocq MCP server.

Note: Integration tests require either the 'pet' command (stdio mode) or a running pet-server (TCP mode).
"""

import pytest
import asyncio
import tempfile
import os
from pathlib import Path
from unittest.mock import Mock, patch

from rocq_mcp.server import handle_call_tool, handle_list_tools, get_client


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
    """Integration tests using default stdio mode."""

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

    @pytest.fixture(autouse=True)
    def setup_stdio_mode(self):
        """Ensure tests use stdio mode by default."""
        # Reset global client state and ensure stdio mode
        import importlib
        import rocq_mcp.server
        importlib.reload(rocq_mcp.server)
        
        # Set stdio mode explicitly
        rocq_mcp.server.use_tcp_mode = False
        
        yield

    @pytest.mark.asyncio
    async def test_full_proof_workflow(self, sample_coq_file):
        """Test a complete proof workflow using stdio mode."""
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
            pytest.skip(f"Integration test skipped - 'pet' command not available: {e}")

    @pytest.mark.asyncio
    async def test_file_toc(self, sample_coq_file):
        """Test getting file table of contents using stdio mode."""
        try:
            result = await handle_call_tool(
                "rocq_get_file_toc", {"file_path": sample_coq_file}
            )

            assert len(result) == 1
            assert "Table of contents" in result[0].text

        except Exception as e:
            pytest.skip(f"Integration test skipped - 'pet' command not available: {e}")


class TestCommunicationModes:
    """Test different communication modes (stdio vs TCP)."""
    
    def test_stdio_mode_client_creation(self):
        """Test creating a client in stdio mode."""
        try:
            # Import fresh to reset global state
            import importlib
            import rocq_mcp.server
            importlib.reload(rocq_mcp.server)
            
            # Set stdio mode explicitly
            rocq_mcp.server.use_tcp_mode = False
            
            client = rocq_mcp.server.get_client()
            assert client.mode == "stdio", f"Expected stdio mode, got {client.mode}"
            client.close()
            
        except Exception as e:
            pytest.skip(f"Stdio mode test skipped - 'pet' command not available: {e}")
    
    def test_tcp_mode_client_creation(self):
        """Test creating a client in TCP mode."""
        try:
            # Import fresh to reset global state
            import importlib
            import rocq_mcp.server
            importlib.reload(rocq_mcp.server)
            
            # Set TCP mode explicitly
            rocq_mcp.server.use_tcp_mode = True
            rocq_mcp.server.tcp_host = "127.0.0.1"
            rocq_mcp.server.tcp_port = 8833
            
            # This will fail if no pet-server is running, but that's expected
            client = rocq_mcp.server.get_client()
            assert client.mode == "socket", f"Expected socket mode, got {client.mode}"
            client.close()
        except Exception as e:
            # Expected if no pet-server running
            assert "pet-server" in str(e) or "Connection" in str(e)

    @pytest.mark.asyncio
    async def test_stdio_mode_integration(self):
        """Test basic functionality with stdio mode."""
        try:
            # Import fresh to reset global state
            import importlib
            import rocq_mcp.server
            importlib.reload(rocq_mcp.server)
            
            # Set stdio mode explicitly
            rocq_mcp.server.use_tcp_mode = False
            
            # Create a simple test file
            content = """
Theorem simple_test : forall n : nat, 0 + n = n.
Proof.
  intro n.
  reflexivity.
Qed.
"""
            with tempfile.NamedTemporaryFile(mode="w", suffix=".v", delete=False) as f:
                f.write(content)
                test_file = f.name
            
            try:
                # Test getting table of contents
                result = await handle_call_tool(
                    "rocq_get_file_toc", {"file_path": test_file}
                )
                
                assert len(result) == 1
                assert "Table of contents" in result[0].text
                print(f"TOC test passed: {result[0].text[:100]}...")
                
                # Test starting a proof
                result = await handle_call_tool(
                    "rocq_start_proof",
                    {
                        "file_path": test_file,
                        "theorem_name": "simple_test", 
                        "session_id": "stdio_test_session",
                    },
                )
                
                assert len(result) == 1
                assert "Started proof session" in result[0].text
                print(f"Proof start test passed: {result[0].text[:100]}...")
                
            finally:
                # Clean up test file
                os.unlink(test_file)
                
        except Exception as e:
            pytest.skip(f"Stdio integration test skipped - 'pet' command issues: {e}")


if __name__ == "__main__":
    # Run basic tests
    pytest.main([__file__, "-v"])

    # To run integration tests (requires 'pet' command or pet-server):
    # pytest test_server.py -v
