"""Tests for the rocq_assumptions tool (run_assumptions).

These tests mock run_query to avoid needing pet — they test the
classification and result formatting logic only.
"""

from __future__ import annotations

import pytest

from rocq_mcp.interactive import run_assumptions


class TestRunAssumptions:
    """Unit tests for run_assumptions using mocked run_query."""

    @pytest.fixture(autouse=True)
    def _patch_run_query(self, monkeypatch):
        """Patch run_query to avoid needing pet."""
        import rocq_mcp.interactive as _int

        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }

        async def mock_run_query(command, preamble, workspace, lifespan_state, **kw):
            return self._query_result

        monkeypatch.setattr(_int, "run_query", mock_run_query)

    @pytest.mark.asyncio
    async def test_closed_proof(self):
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        result = await run_assumptions(
            name="add_0_r",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["verdict"] == "closed"
        assert result["assumptions"] == []

    @pytest.mark.asyncio
    async def test_standard_axioms(self):
        self._query_result = {
            "success": True,
            "output": (
                "Axioms:\n"
                "Coq.Logic.Classical_Prop.classic"
                " : forall P : Prop, P \\/ ~ P"
            ),
        }
        result = await run_assumptions(
            name="my_thm",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["verdict"] == "standard_only"
        assert len(result["assumptions"]) == 1

    @pytest.mark.asyncio
    async def test_suspicious_axiom(self):
        self._query_result = {
            "success": True,
            "output": "Axioms:\nmy_custom_axiom : False",
        }
        result = await run_assumptions(
            name="bad_thm",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["verdict"] == "suspicious"
        assert len(result["assumptions"]) >= 1

    @pytest.mark.asyncio
    async def test_empty_name(self):
        result = await run_assumptions(
            name="",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "empty" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_whitespace_name(self):
        result = await run_assumptions(
            name="   ",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "empty" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_query_failure_propagated(self):
        self._query_result = {
            "success": False,
            "error": "Unknown reference: bogus",
        }
        result = await run_assumptions(
            name="bogus",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "bogus" in result["error"]

    @pytest.mark.asyncio
    async def test_result_includes_raw_output(self):
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        result = await run_assumptions(
            name="thm",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert "raw_output" in result
        assert "Closed" in result["raw_output"]

    @pytest.mark.asyncio
    async def test_result_includes_theorem_name(self):
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        result = await run_assumptions(
            name="my_theorem",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["theorem"] == "my_theorem"

    @pytest.mark.asyncio
    async def test_invalid_identifier_rejected(self):
        """Names with special characters should be rejected."""
        result = await run_assumptions(
            name="foo; bar",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "invalid" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_qualified_name_accepted(self):
        """Fully qualified names like Nat.add_comm should be accepted."""
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        result = await run_assumptions(
            name="Nat.add_comm",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["theorem"] == "Nat.add_comm"

    @pytest.mark.asyncio
    async def test_mixed_axioms(self):
        """Both standard and suspicious axioms should be classified correctly."""
        self._query_result = {
            "success": True,
            "output": (
                "Axioms:\n"
                "Coq.Logic.Classical_Prop.classic"
                " : forall P : Prop, P \\/ ~ P\n"
                "my_custom_axiom : False"
            ),
        }
        result = await run_assumptions(
            name="mixed_thm",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["verdict"] == "suspicious"
        # Should have suspicious assumptions
        assert len(result["assumptions"]) >= 1
        # Should also report standard assumptions
        assert "standard_assumptions" in result

    @pytest.mark.asyncio
    async def test_name_with_leading_trailing_whitespace(self):
        """Name with leading/trailing spaces should be trimmed and accepted."""
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        result = await run_assumptions(
            name="  add_0_r  ",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["theorem"] == "add_0_r"

    @pytest.mark.asyncio
    async def test_name_with_prime(self):
        """Rocq identifiers with primes (apostrophes) should be accepted."""
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        result = await run_assumptions(
            name="add_0_r'",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True

    @pytest.mark.asyncio
    async def test_parse_exception_returns_error(self, monkeypatch):
        """If parse_and_classify_assumptions raises, return error with raw_output."""
        self._query_result = {
            "success": True,
            "output": "some unparseable garbage",
        }
        import rocq_mcp.interactive as _int

        def _bad_parse(*args, **kwargs):
            raise ValueError("parse failed")

        # Patch the local import inside run_assumptions
        import rocq_mcp.verify as _verify

        monkeypatch.setattr(_verify, "parse_and_classify_assumptions", _bad_parse)

        result = await run_assumptions(
            name="thm",
            preamble="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "parse" in result["error"].lower()
        assert "raw_output" in result
