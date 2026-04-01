"""Tests for the rocq_assumptions tool (run_assumptions).

These tests mock run_query to avoid needing pet — they test the
classification and result formatting logic only.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from rocq_mcp.interactive import run_assumptions
from tests.conftest import PET_AVAILABLE

_pet_only = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


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
            self._last_query_kwargs = {
                "command": command,
                "preamble": preamble,
                "workspace": workspace,
                "file": kw.get("file", ""),
            }
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
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["verdict"] == "closed"
        assert result["assumptions"] == []

    @pytest.mark.asyncio
    async def test_delegates_to_run_query_with_file(self):
        """run_assumptions should call run_query with file=... and empty preamble."""
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        await run_assumptions(
            name="my_thm",
            file="proofs/test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert self._last_query_kwargs["file"] == "proofs/test.v"
        assert self._last_query_kwargs["preamble"] == ""

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
            file="test.v",
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
            file="test.v",
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
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "empty" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_whitespace_name(self):
        result = await run_assumptions(
            name="   ",
            file="test.v",
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
            file="test.v",
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
            file="test.v",
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
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["theorem"] == "my_theorem"

    @pytest.mark.asyncio
    async def test_invalid_identifier_rejected(self):
        """Names with special characters should be rejected."""
        result = await run_assumptions(
            name="foo; bar",
            file="test.v",
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
            file="test.v",
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
            file="test.v",
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
            file="test.v",
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
            file="test.v",
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
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "parse" in result["error"].lower()
        assert "raw_output" in result

    @pytest.mark.asyncio
    async def test_empty_file_rejected(self):
        """Empty file parameter should be rejected before reaching run_query."""
        result = await run_assumptions(
            name="my_thm",
            file="",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "required" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_whitespace_file_rejected(self):
        """Whitespace-only file parameter should be rejected."""
        result = await run_assumptions(
            name="my_thm",
            file="   ",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "required" in result["error"].lower()


# ---------------------------------------------------------------------------
# Integration tests (require pet)
# ---------------------------------------------------------------------------


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
        "current_workspace": None,
    }


@_pet_only
class TestAssumptionsFileModeIntegration:
    """Integration tests for run_assumptions with file mode (require pet)."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = _make_lifespan_state()
        yield state
        _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_closed_theorem_via_file(self, workspace, lifespan_state):
        """Theorem in a .v file should be checkable via run_assumptions."""
        vfile = Path(workspace) / "assumptions_int_test.v"
        vfile.write_text("Theorem simple : True.\nProof. exact I. Qed.\n")

        result = await run_assumptions(
            name="simple",
            file="assumptions_int_test.v",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is True
        assert result["verdict"] == "closed"


# ---------------------------------------------------------------------------
# MCP wrapper tests (no pet required)
# ---------------------------------------------------------------------------


class TestRocqAssumptionsWrapper:
    """Tests for the rocq_assumptions MCP wrapper in server.py."""

    @pytest.mark.asyncio
    async def test_ctx_none_returns_error(self):
        from rocq_mcp.server import rocq_assumptions

        result = await rocq_assumptions(name="foo", file="test.v", ctx=None)
        assert result["success"] is False
        assert "context" in result["error"].lower()

    @pytest.mark.asyncio
    async def test_invalid_workspace_returns_error(self):
        from rocq_mcp.server import rocq_assumptions
        from unittest.mock import MagicMock

        mock_ctx = MagicMock()
        mock_ctx.lifespan_context = {}
        result = await rocq_assumptions(
            name="foo",
            file="test.v",
            workspace="/nonexistent_rocq_workspace_xyz",
            ctx=mock_ctx,
        )
        assert result["success"] is False

    @pytest.mark.asyncio
    async def test_params_forwarded(self, monkeypatch, tmp_path):
        """Wrapper should forward all params to run_assumptions."""
        from rocq_mcp.server import rocq_assumptions
        from unittest.mock import MagicMock
        import rocq_mcp.server as _server

        captured = {}

        async def mock_run_assumptions(**kwargs):
            captured.update(kwargs)
            return {"success": True, "verdict": "closed", "assumptions": []}

        monkeypatch.setattr(_server, "run_assumptions", mock_run_assumptions)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        mock_ctx = MagicMock()
        mock_ctx.lifespan_context = {"pet_client": None}

        await rocq_assumptions(
            name="my_thm",
            file="proof.v",
            workspace=str(tmp_path),
            ctx=mock_ctx,
        )

        assert captured["name"] == "my_thm"
        assert captured["file"] == "proof.v"
        assert captured["lifespan_state"] is mock_ctx.lifespan_context
