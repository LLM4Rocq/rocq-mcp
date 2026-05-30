"""Tests for diagnostic-pattern hints attached to compile errors.

When ``rocq_compile_file`` or ``rocq_compile`` fails with a coqc
error, the response carries an ``error`` string and (usually) an
``error_positions`` list.  The existing ``hint`` field tells the
agent how to *recover* (use ``rocq_start`` at the position, etc.)
but doesn't help diagnose the *cause* of common configuration
errors.

This module exercises a pattern-based diagnostic hint: a
``diagnostic_hint`` field that recognises common Coq error
shapes and tells the agent what's actually wrong, so it can fix
the configuration instead of grinding on the proof.
"""

from __future__ import annotations

import pytest


def test_diagnostic_hint_for_missing_load_path():
    """``Cannot find a physical path bound to logical path X`` is a
    load-path configuration error, not a proof bug.  The agent
    should be told to check ``_CoqProject`` / ``-Q``, not to retry
    proof tactics.
    """
    from rocq_mcp.compile import _diagnostic_hint_for_error  # noqa: PLC0415

    error = (
        'File "Sandbox.v", line 33, characters 15-44:\n'
        "Error: Cannot find a physical path bound to logical path\n"
        "RocqOfSolidity.RocqOfSolidity."
    )
    hint = _diagnostic_hint_for_error(error)
    assert hint is not None
    lower = hint.lower()
    # Hint should reference _CoqProject / -Q / load path config.
    assert any(
        clue in lower
        for clue in ("_coqproject", "_rocqproject", "-q", "load path", "library")
    )
    # And mention the missing logical name.
    assert "rocqofsolidity" in lower


def test_diagnostic_hint_for_coq_version_mismatch():
    """``makes inconsistent assumptions over library Coq.Init.Prelude``
    is the canonical signature of a Coq version mismatch: pet's coqc
    is from a different opam switch than the one that produced the
    workspace ``.vo`` files.  The hint should call this out by name.
    """
    from rocq_mcp.compile import _diagnostic_hint_for_error  # noqa: PLC0415

    error = (
        'File "./Foo.v", line 1, characters 0-30:\n'
        "Error:\n"
        "Compiled library RocqOfSolidity.RocqOfSolidity (in file "
        "/path/to/dep.vo) makes inconsistent assumptions over library "
        "Coq.Init.Prelude"
    )
    hint = _diagnostic_hint_for_error(error)
    assert hint is not None
    lower = hint.lower()
    assert "version" in lower or "switch" in lower or "rebuild" in lower
    assert "inconsistent" in lower or ".vo" in lower or "prelude" in lower


def test_diagnostic_hint_for_unrelated_error_returns_none():
    """Tactic-level errors are out of scope — ``Tactic failure`` is a
    proof issue and the existing recovery hint already covers it.
    """
    from rocq_mcp.compile import _diagnostic_hint_for_error  # noqa: PLC0415

    error = (
        'File "Foo.v", line 5, characters 0-10:\n'
        "Error: Tactic failure: no progress made."
    )
    hint = _diagnostic_hint_for_error(error)
    assert hint is None, (
        f"Expected no diagnostic_hint for a tactic failure (the existing "
        f"recovery hint already covers it). Got: {hint!r}"
    )


def test_diagnostic_hint_for_empty_error_returns_none():
    """Empty / None input must return None — never raise."""
    from rocq_mcp.compile import _diagnostic_hint_for_error  # noqa: PLC0415

    assert _diagnostic_hint_for_error("") is None
    assert _diagnostic_hint_for_error(None) is None  # type: ignore[arg-type]


class TestDiagnosticHintWiredIntoCompileFile:
    """Integration: ``rocq_compile_file`` should attach
    ``diagnostic_hint`` to the failure envelope when the coqc error
    matches a known configuration-failure pattern.
    """

    @pytest.mark.asyncio
    async def test_missing_load_path_surfaces_diagnostic_hint(self, tmp_path):
        from rocq_mcp.server import rocq_compile_file

        broken = tmp_path / "Broken.v"
        broken.write_text("Require Import NotAProject.Lib.\n")

        result = await rocq_compile_file(
            file=str(broken.name),
            workspace=str(tmp_path),
        )
        assert result["success"] is False
        assert result["reason"] == "compile_error"
        # The new field must be present and mention either the
        # logical name or load-path / _CoqProject.
        diag = result.get("diagnostic_hint") or ""
        assert diag, f"Expected diagnostic_hint, got: {result!r}"
        lower = diag.lower()
        assert any(
            clue in lower
            for clue in ("notaproject", "load path", "_coqproject", "-q")
        )
