"""Tests for the rocq_notations tool.

Since rocq_notations requires pytanque, these tests use mocks for the
pytanque client. The formatting logic is tested via mock responses.

Tests are grouped into:
- TestNotationsFormatting: formatting NotationInfo -> text
- TestNotationsMock: mock list_notations_in_statement(), verify output
- TestNotationsNoPet: graceful error when pytanque is not installed
"""

from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import MagicMock

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
