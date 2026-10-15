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
            clue in lower for clue in ("notaproject", "load path", "_coqproject", "-q")
        )


def _coqc_failure(stderr: str) -> dict:
    return {"returncode": 1, "stdout": "", "stderr": stderr, "timed_out": False}


_HEADERLESS_LOAD_PATH = (
    "Error: Cannot find a physical path bound to logical path Foo.Bar.\n"
)
_HEADED_LOAD_PATH = (
    'File "Proof.v", line 1, characters 0-20:\n'
    "Error: Cannot find a physical path bound to logical path Foo.Bar.\n"
)


class TestDiagnosticHintBothFailurePaths:
    """``_build_compile_result`` has a structured and an unstructured
    (header-less) failure return; both must carry the hint."""

    def test_unstructured_fallback_path_gets_hint(self):
        from rocq_mcp.compile import _build_compile_result  # noqa: PLC0415

        res = _build_compile_result(_coqc_failure(_HEADERLESS_LOAD_PATH), "", 60, True)
        assert res["reason"] == "compile_error"
        assert "error_positions" not in res  # really the fallback path
        assert "Foo.Bar" in res["diagnostic_hint"]
        assert "hint" not in res

    def test_structured_path_gets_hint_and_drops_recovery_hint(self):
        from rocq_mcp.compile import _build_compile_result  # noqa: PLC0415

        res = _build_compile_result(
            _coqc_failure(_HEADED_LOAD_PATH), "Require Import Foo.Bar.\n", 60, True
        )
        assert "Foo.Bar" in res["diagnostic_hint"]
        assert "hint" not in res

    def test_proof_error_keeps_recovery_hint_only(self):
        from rocq_mcp.compile import _build_compile_result  # noqa: PLC0415

        stderr = 'File "Proof.v", line 1, characters 0-10:\nError: No such goal.\n'
        res = _build_compile_result(_coqc_failure(stderr), "Qed.\n", 60, True)
        assert "hint" in res
        assert "diagnostic_hint" not in res


class TestVersionMismatchWording:
    @pytest.mark.parametrize(
        "prelude", ["Coq.Init.Prelude", "Corelib.Init.Prelude", "Stdlib.Init.Prelude"]
    )
    def test_stdlib_prelude_points_at_toolchain_tools(self, prelude):
        from rocq_mcp.compile import _diagnostic_hint_for_error  # noqa: PLC0415

        err = (
            "Error: Compiled library A (in file a.vo) makes inconsistent "
            f"assumptions over library {prelude}"
        )
        hint = _diagnostic_hint_for_error(err)
        assert "rocq_health" in hint and "rocq_switch" in hint

    def test_other_library_says_rebuild_that_library(self):
        from rocq_mcp.compile import _diagnostic_hint_for_error  # noqa: PLC0415

        err = (
            "Error: Compiled library A (in file a.vo) makes inconsistent "
            "assumptions over library My.Dep"
        )
        hint = _diagnostic_hint_for_error(err)
        assert "'My.Dep'" in hint
        assert "install" not in hint.lower()
        assert "rocq_switch" not in hint


@pytest.mark.asyncio
async def test_enrichment_merge_keeps_diagnostic_hint():
    from rocq_mcp.compile_enrichment import _merge_compile_error_state  # noqa: PLC0415

    result = {"success": False, "diagnostic_hint": "fix the load path"}
    state = {
        "state_id": 7,
        "goals": ["g"],
        "file": "f.v",
        "theorem": "t",
        "proof_finished": False,
    }
    merged = _merge_compile_error_state(result, state)
    assert merged["diagnostic_hint"] == "fix the load path"
    assert "hint" not in merged
