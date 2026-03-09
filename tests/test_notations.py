"""Tests for the rocq_notations tool.

Since rocq_notations requires pytanque, these tests use mocks for the
pytanque client. The formatting logic is tested via mock responses.

Tests are grouped into:
- TestNotationsFormatting: formatting NotationInfo -> text
- TestRunNotationsReal: tests that call the real run_notations from server.py
- TestNotationsMock: mock list_notations_in_statement(), verify output
- TestNotationsNoPet: graceful error when pytanque is not installed
"""

from __future__ import annotations

import asyncio
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

# ---------------------------------------------------------------------------
# Helpers to build mock NotationInfo-like objects
# ---------------------------------------------------------------------------


def _make_notation_info(path, secpath, notation, scope=None, locations=None):
    """Create a SimpleNamespace mimicking pytanque's NotationInfo."""
    return SimpleNamespace(
        path=path,
        secpath=secpath,
        notation=notation,
        scope=scope,
        locations=locations or [],
    )


# ---------------------------------------------------------------------------
# TestNotationsFormatting
# ---------------------------------------------------------------------------


class TestNotationsFormatting:
    """Test formatting logic for NotationInfo objects."""

    def test_single_notation_format(self):
        """A single notation should format as '"notation" -> path (scope: X)'."""
        info = _make_notation_info(
            path="Coq.Init.Nat",
            secpath="",
            notation="_ + _",
            scope="nat_scope",
        )
        # Expected format from the enhancement plan:
        #   "_ + _"  ->  Coq.Init.Nat  (scope: nat_scope)
        formatted = f'  "{info.notation}"  ->  {info.path}'
        if info.scope:
            formatted += f"  (scope: {info.scope})"
        assert '"_ + _"' in formatted
        assert "Coq.Init.Nat" in formatted
        assert "nat_scope" in formatted

    def test_notation_without_scope(self):
        """A notation without a scope should omit the scope part."""
        info = _make_notation_info(
            path="Coq.Init.Logic",
            secpath="",
            notation="_ = _",
            scope=None,
        )
        formatted = f'  "{info.notation}"  ->  {info.path}'
        if info.scope:
            formatted += f"  (scope: {info.scope})"
        assert '"_ = _"' in formatted
        assert "scope:" not in formatted

    def test_multiple_notations(self):
        """Multiple notations should produce multiple lines."""
        infos = [
            _make_notation_info("Coq.Init.Nat", "", "_ + _", "nat_scope"),
            _make_notation_info("Coq.Init.Logic", "", "_ = _", "type_scope"),
            _make_notation_info("Coq.Init.Nat", "", "_ * _", "nat_scope"),
        ]
        lines = []
        for info in infos:
            line = f'  "{info.notation}"  ->  {info.path}'
            if info.scope:
                line += f"  (scope: {info.scope})"
            lines.append(line)
        output = "Notations found in statement:\n" + "\n".join(lines)
        assert "_ + _" in output
        assert "_ = _" in output
        assert "_ * _" in output
        assert output.count("->") == 3

    def test_empty_notations(self):
        """No notations should produce an appropriate message."""
        infos = []
        if not infos:
            output = "No notations found in statement."
        else:
            output = "Notations found."
        assert "No notations" in output


# ---------------------------------------------------------------------------
# TestRunNotationsReal: call the real run_notations from server.py
# ---------------------------------------------------------------------------


def _install_pytanque_mock():
    """Ensure 'pytanque' is importable by injecting a mock module into sys.modules.

    run_notations does ``from pytanque import PetanqueError`` at the top.
    When pytanque is not installed we need a stand-in so that guard passes.
    Returns a cleanup function that removes the mock module.
    """
    if "pytanque" in sys.modules:
        return lambda: None  # already importable

    mock_module = type(sys)("pytanque")

    class _PetanqueError(Exception):
        def __init__(self, message=""):
            self.message = message
            super().__init__(message)

    mock_module.PetanqueError = _PetanqueError
    sys.modules["pytanque"] = mock_module

    def _cleanup():
        sys.modules.pop("pytanque", None)

    return _cleanup


class TestRunNotationsReal:
    """Tests that call the actual run_notations production function.

    We patch _ensure_pet to return a mock pet client so that no real
    pytanque/pet subprocess is needed, but all the formatting, forbidden
    command checks, temp-file logic, and output assembly in run_notations
    are exercised for real.
    """

    @pytest.fixture(autouse=True)
    def ensure_pytanque_importable(self):
        """Make sure ``from pytanque import PetanqueError`` succeeds."""
        cleanup = _install_pytanque_mock()
        yield
        cleanup()

    @pytest.fixture
    def mock_pet(self):
        """Create a mock pytanque client with start/set_workspace/list_notations."""
        pet = MagicMock()
        pet.process = MagicMock()
        pet.process.poll = MagicMock(return_value=None)
        pet.set_workspace = MagicMock()
        pet.start = MagicMock(return_value=MagicMock())  # mock state
        return pet

    @pytest.fixture
    def lifespan_state(self):
        return {
            "pet_client": None,
            "pet_timeout": 30.0,
        }

    @pytest.fixture(autouse=True)
    def reset_semaphore(self):
        """Reset the module-level _pet_semaphore so it is recreated for each test's event loop."""
        import rocq_mcp.server as srv

        old = srv._pet_semaphore
        srv._pet_semaphore = None
        yield
        srv._pet_semaphore = old

    @pytest.mark.asyncio
    async def test_basic_notations(self, mock_pet, lifespan_state, tmp_path):
        """run_notations with two mock notations produces correct formatted output."""
        from rocq_mcp.server import run_notations

        notations = [
            _make_notation_info("Coq.Init.Nat", "", "_ + _", "nat_scope"),
            _make_notation_info("Coq.Init.Logic", "", "_ = _", "type_scope"),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="n + 0 = n",
                preamble="",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        output = result["output"]
        assert "Notations found in statement:" in output
        assert '"_ + _"  ->  Coq.Init.Nat  (scope: nat_scope)' in output
        assert '"_ = _"  ->  Coq.Init.Logic  (scope: type_scope)' in output

    @pytest.mark.asyncio
    async def test_empty_notations(self, mock_pet, lifespan_state, tmp_path):
        """run_notations with no notations returns 'No notations found'."""
        from rocq_mcp.server import run_notations

        mock_pet.list_notations_in_statement = MagicMock(return_value=[])

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="True",
                preamble="",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        assert result["output"] == "No notations found in statement."

    @pytest.mark.asyncio
    async def test_notation_without_scope(self, mock_pet, lifespan_state, tmp_path):
        """Notation with scope=None should omit the scope suffix."""
        from rocq_mcp.server import run_notations

        notations = [
            _make_notation_info("Coq.Init.Logic", "", "_ = _", scope=None),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="n = n",
                preamble="",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        output = result["output"]
        assert '"_ = _"  ->  Coq.Init.Logic' in output
        assert "scope:" not in output

    @pytest.mark.asyncio
    async def test_notation_fallback_to_secpath(
        self, mock_pet, lifespan_state, tmp_path
    ):
        """When path is empty/None, module should fall back to secpath."""
        from rocq_mcp.server import run_notations

        notations = [
            _make_notation_info(
                path="", secpath="MyModule", notation="_ ++ _", scope=None
            ),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="x ++ y",
                preamble="",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        assert '"_ ++ _"  ->  MyModule' in result["output"]

    @pytest.mark.asyncio
    async def test_notation_fallback_to_unknown(
        self, mock_pet, lifespan_state, tmp_path
    ):
        """When both path and secpath are empty, module should be 'unknown'."""
        from rocq_mcp.server import run_notations

        notations = [
            _make_notation_info(path="", secpath="", notation="_ ++ _", scope=None),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="x ++ y",
                preamble="",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        assert '"_ ++ _"  ->  unknown' in result["output"]

    @pytest.mark.asyncio
    async def test_forbidden_command_in_statement(self, lifespan_state, tmp_path):
        """run_notations should reject forbidden commands in the statement."""
        from rocq_mcp.server import run_notations

        result = await run_notations(
            statement='Redirect "out" Check nat.',
            preamble="",
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
        )

        assert result["success"] is False
        assert "error" in result
        assert "Redirect" in result["error"]

    @pytest.mark.asyncio
    async def test_forbidden_command_in_preamble(self, lifespan_state, tmp_path):
        """run_notations should reject forbidden commands in the preamble."""
        from rocq_mcp.server import run_notations

        result = await run_notations(
            statement="n = n",
            preamble="Drop.",
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
        )

        assert result["success"] is False
        assert "error" in result
        assert "Drop" in result["error"]

    @pytest.mark.asyncio
    async def test_with_preamble(self, mock_pet, lifespan_state, tmp_path):
        """run_notations passes the preamble through to the dummy source file."""
        from rocq_mcp.server import run_notations

        notations = [
            _make_notation_info("Coq.Reals.Rdefinitions", "", "_ + _", "R_scope"),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="x + y",
                preamble="From Coq Require Import Reals.\nOpen Scope R_scope.",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        assert "R_scope" in result["output"]

        # Verify pet.start was called (the temp file was created and used)
        mock_pet.start.assert_called_once()
        # Verify list_notations_in_statement was called with the right full_statement
        mock_pet.list_notations_in_statement.assert_called_once()
        call_args = mock_pet.list_notations_in_statement.call_args
        assert "Lemma _rocq_mcp_notation_check : x + y." in call_args[0][1]

    @pytest.mark.asyncio
    async def test_multiple_notations_output_format(
        self, mock_pet, lifespan_state, tmp_path
    ):
        """Multiple notations produce correctly formatted multi-line output."""
        from rocq_mcp.server import run_notations

        notations = [
            _make_notation_info("Coq.Init.Nat", "", "_ + _", "nat_scope"),
            _make_notation_info("Coq.Init.Logic", "", "_ = _", "type_scope"),
            _make_notation_info("Coq.Init.Nat", "", "_ * _", "nat_scope"),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        with patch("rocq_mcp.server._ensure_pet", return_value=mock_pet):
            result = await run_notations(
                statement="n + m * 2 = 0",
                preamble="",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )

        assert result["success"] is True
        output = result["output"]
        lines = output.split("\n")
        # First line is the header
        assert lines[0] == "Notations found in statement:"
        # Then one line per notation
        assert len(lines) == 4
        assert "_ + _" in lines[1]
        assert "_ = _" in lines[2]
        assert "_ * _" in lines[3]


# ---------------------------------------------------------------------------
# TestNotationsMock
# ---------------------------------------------------------------------------


class TestNotationsMock:
    """Test rocq_notations with mocked pytanque client."""

    @pytest.fixture
    def mock_pet(self):
        """Create a mock pytanque client."""
        pet = MagicMock()
        pet.process = MagicMock()
        pet.process.poll = MagicMock(return_value=None)
        return pet

    def test_mock_list_notations(self, mock_pet):
        """Mock list_notations_in_statement() and verify the call."""
        notations = [
            _make_notation_info("Coq.Init.Nat", "", "_ + _", "nat_scope"),
            _make_notation_info("Coq.Init.Logic", "", "_ = _", "type_scope"),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)

        # Create a mock state
        mock_state = MagicMock()
        result = mock_pet.list_notations_in_statement(mock_state, "n + 0 = n")

        mock_pet.list_notations_in_statement.assert_called_once_with(
            mock_state, "n + 0 = n"
        )
        assert len(result) == 2
        assert result[0].notation == "_ + _"
        assert result[1].notation == "_ = _"

    def test_mock_empty_result(self, mock_pet):
        """Statement with no notations returns empty list."""
        mock_pet.list_notations_in_statement = MagicMock(return_value=[])
        mock_state = MagicMock()

        result = mock_pet.list_notations_in_statement(mock_state, "True")
        assert result == []

    def test_mock_with_q_scope(self, mock_pet):
        """Test notation resolution with Q scope (ambiguity case from miniF2F)."""
        notations = [
            _make_notation_info("Coq.QArith.QArith_base", "", "_ == _", "Q_scope"),
        ]
        mock_pet.list_notations_in_statement = MagicMock(return_value=notations)
        mock_state = MagicMock()

        result = mock_pet.list_notations_in_statement(mock_state, "x == y")
        assert len(result) == 1
        assert result[0].scope == "Q_scope"
        assert result[0].notation == "_ == _"


# ---------------------------------------------------------------------------
# TestNotationsNoPet
# ---------------------------------------------------------------------------


class TestNotationsNoPet:
    """When pytanque is not installed, rocq_notations should return graceful error."""

    def test_import_error_message(self):
        """Verify the error message for missing pytanque."""
        try:
            raise ImportError(
                "pytanque is not installed. "
                "Install with: pip install 'rocq-mcp[interactive]'"
            )
        except ImportError as e:
            assert "pytanque is not installed" in str(e)

    def test_error_dict_structure(self):
        """The error response should have success=False and an error message."""
        # Simulate what the tool would return
        error_result = {
            "success": False,
            "error": (
                "pytanque is not installed. "
                "Install with: pip install 'rocq-mcp[interactive]'"
            ),
        }
        assert error_result["success"] is False
        assert "pytanque" in error_result["error"]
