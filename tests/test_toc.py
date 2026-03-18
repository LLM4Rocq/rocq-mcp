"""Tests for the rocq_toc tool.

Since rocq_toc requires pytanque (pet subprocess), these tests use mocks
for the pytanque client. The formatting logic is tested as a pure function.

Tests are grouped into:
- TestFormatTocElementsReal: tests that call _format_toc_elements from server.py
- TestTocPathTraversal: path traversal validation
"""

from __future__ import annotations

import asyncio
from types import SimpleNamespace

import pytest

from rocq_mcp.server import _format_toc_elements, run_toc

# ---------------------------------------------------------------------------
# Helpers to build mock TocElement-like objects
# ---------------------------------------------------------------------------


def _make_toc_element(name, detail, kind=0, start_line=0, children=None):
    """Create a SimpleNamespace mimicking pytanque's TocElement."""
    return SimpleNamespace(
        name=SimpleNamespace(v=name),
        detail=detail,
        kind=kind,
        range=SimpleNamespace(
            start=SimpleNamespace(line=start_line, character=0),
            end=SimpleNamespace(line=start_line + 5, character=0),
        ),
        children=children,
    )


# ---------------------------------------------------------------------------
# TestFormatTocElementsReal: call the real _format_toc_elements from server.py
# ---------------------------------------------------------------------------


class TestFormatTocElementsReal:
    """Tests that call the actual _format_toc_elements production function."""

    def test_single_element(self):
        """A single element should produce one formatted line."""
        elem = _make_toc_element("my_fn", "Definition", start_line=5)
        result = _format_toc_elements([elem])
        assert len(result) == 1
        assert result[0] == "  Definition my_fn (line 5)"

    def test_multiple_elements(self):
        """Multiple elements should produce one line each."""
        elements = [
            _make_toc_element("my_fn", "Definition", start_line=5),
            _make_toc_element("helper1", "Lemma", start_line=12),
            _make_toc_element("main_thm", "Theorem", start_line=20),
        ]
        result = _format_toc_elements(elements)
        assert len(result) == 3
        assert result[0] == "  Definition my_fn (line 5)"
        assert result[1] == "  Lemma helper1 (line 12)"
        assert result[2] == "  Theorem main_thm (line 20)"

    def test_nested_children(self):
        """Children should be indented one level deeper than their parent."""
        child = _make_toc_element("sub_lemma", "Lemma", start_line=22)
        parent = _make_toc_element(
            "main_thm", "Theorem", start_line=20, children=[child]
        )
        result = _format_toc_elements([parent])
        assert len(result) == 2
        # Parent at indent=1 (default): "  " prefix
        assert result[0] == "  Theorem main_thm (line 20)"
        # Child at indent=2: "    " prefix
        assert result[1] == "    Lemma sub_lemma (line 22)"

    def test_deeply_nested_children(self):
        """Deeply nested elements should accumulate indentation."""
        grandchild = _make_toc_element("gc", "Definition", start_line=30)
        child = _make_toc_element(
            "child", "Lemma", start_line=22, children=[grandchild]
        )
        parent = _make_toc_element("parent", "Section", start_line=20, children=[child])
        result = _format_toc_elements([parent])
        assert len(result) == 3
        assert result[0] == "  Section parent (line 20)"
        assert result[1] == "    Lemma child (line 22)"
        assert result[2] == "      Definition gc (line 30)"

    def test_empty_list(self):
        """An empty elements list should return an empty lines list."""
        result = _format_toc_elements([])
        assert result == []

    def test_none_name_skipped(self):
        """Elements with None name should be skipped but children still processed."""
        # Production code: elem.name is checked for truthiness.
        # When elem.name is None, the element is skipped but children are recursed.
        child = _make_toc_element("inner", "Lemma", start_line=10)
        unnamed = SimpleNamespace(
            name=None,
            detail="Section",
            kind=0,
            range=SimpleNamespace(
                start=SimpleNamespace(line=5, character=0),
                end=SimpleNamespace(line=20, character=0),
            ),
            children=[child],
        )
        result = _format_toc_elements([unnamed])
        # The unnamed parent is skipped, but the child appears
        assert len(result) == 1
        # Child inherits the SAME indent level (not indent+1) because unnamed
        # parent passes its own indent to children
        assert result[0] == "  Lemma inner (line 10)"

    def test_none_name_no_children(self):
        """An unnamed element with no children produces no output."""
        unnamed = SimpleNamespace(
            name=None,
            detail="Section",
            kind=0,
            range=SimpleNamespace(
                start=SimpleNamespace(line=5, character=0),
                end=SimpleNamespace(line=20, character=0),
            ),
            children=None,
        )
        result = _format_toc_elements([unnamed])
        assert result == []

    def test_custom_indent(self):
        """The indent parameter controls the starting indentation level."""
        elem = _make_toc_element("my_fn", "Definition", start_line=5)
        result = _format_toc_elements([elem], indent=0)
        assert result[0] == "Definition my_fn (line 5)"

        result = _format_toc_elements([elem], indent=3)
        assert result[0] == "      Definition my_fn (line 5)"

    def test_none_range(self):
        """Elements with None range should show '?' for line number."""
        elem = SimpleNamespace(
            name=SimpleNamespace(v="my_fn"),
            detail="Definition",
            kind=0,
            range=None,
            children=None,
        )
        result = _format_toc_elements([elem])
        assert len(result) == 1
        assert result[0] == "  Definition my_fn (line ?)"


# ---------------------------------------------------------------------------
# TestTocPathTraversal
# ---------------------------------------------------------------------------


class TestTocPathTraversal:
    """Test that path traversal is rejected."""

    def test_absolute_path_rejected(self, tmp_path):
        """An absolute file path outside workspace is rejected."""
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_toc(
                file="/etc/passwd",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "workspace" in result["error"].lower()

    def test_dotdot_traversal_rejected(self, tmp_path):
        """A ../ traversal outside workspace is rejected."""
        lifespan_state = {"pet_timeout": 10}
        result = asyncio.run(
            run_toc(
                file="../../etc/passwd",
                workspace=str(tmp_path),
                lifespan_state=lifespan_state,
            )
        )
        assert result["success"] is False
        assert "workspace" in result["error"].lower()
