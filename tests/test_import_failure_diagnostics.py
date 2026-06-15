"""Tests for surfacing silent import failures.

When a file's ``Require Import`` cannot resolve a logical path, pet
silently treats the module body as empty.  Downstream calls
(``rocq_start``, ``rocq_toc``, ``rocq_query``) then produce confusing
errors that don't mention the actual cause:

  - ``rocq_start`` says ``Theorem_not_found`` even though the theorem
    is defined in the source.
  - ``rocq_toc`` returns an empty outline even though the file has
    plenty of definitions.
  - ``rocq_query``'s ``Print Module`` shows ``:= Struct  End`` for a
    module whose body is full of definitions.

These are the symptoms of a load-path mismatch, but the user has no
way to tell from rocq-mcp's response.  These tests exercise the
diagnostic enhancement: surface the *actual* compile-time error so
the user knows what failed.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.conftest import PET_AVAILABLE

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


def _make_broken_project(root: Path) -> Path:
    """Create a workspace with a file that references a non-existent
    logical path AND defines a theorem that references symbols from
    that failed import.  Returns the file path.

    This reproduces the failure mode where:
    1. ``Require Import`` silently fails — pet's coq-lsp can't find
       the binding for the logical name.
    2. The subsequent theorem references ``Bogus.t`` (a type from the
       failed import), so the theorem itself fails to type-check.
    3. From the user's perspective, the file looks fine — the theorem
       is right there in the source — but ``rocq_start`` returns a
       confusing error that doesn't mention the *upstream* cause (the
       failed ``Require Import``).
    """
    (root / "_CoqProject").write_text("-Q . MyProj\n")
    test_file = root / "Broken.v"
    test_file.write_text(
        "Require Import Bogus.Lib.\n"
        "Module M.\n"
        "  Theorem my_theorem : Bogus.t = Bogus.t.\n"
        "  Proof. reflexivity. Qed.\n"
        "End M.\n"
    )
    return test_file


def _make_silently_empty_module_project(root: Path) -> Path:
    """Variant: a file where the failed import is the ROOT cause but
    pet doesn't expose it on the rocq_start path.

    Repro:
    - ``Require Import Bogus.Lib.`` fails silently.
    - The theorem statement is valid Coq (``True = True``) but lives
      inside a Module that also has earlier definitions that fail.
    - In some pet versions the entire module body never registers,
      and ``rocq_start theorem=my_theorem`` returns the bare
      ``[find_thm] Theorem not found!`` error with no clue about
      the upstream import failure.
    """
    (root / "_CoqProject").write_text("-Q . MyProj\n")
    test_file = root / "EmptyModule.v"
    test_file.write_text(
        "Require Import Bogus.Lib.\n"
        "Module M.\n"
        "  Definition broken : Bogus.t := Bogus.zero.\n"
        "  Theorem my_theorem : True = True.\n"
        "  Proof. reflexivity. Qed.\n"
        "End M.\n"
    )
    return test_file


class TestSilentImportFailureSurfaced:
    """When rocq_start fails to find a theorem because the file failed
    to parse (load-path / Require Import error), the error response
    should include enough information to diagnose the root cause —
    not just ``Theorem_not_found``.
    """

    @pytest.mark.asyncio
    async def test_start_surfaces_underlying_compile_error(self, tmp_path):
        """rocq_start on a theorem inside a file with a broken Require
        Import should surface the compile error in the response.
        """
        import rocq_mcp.interactive as _interactive

        test_file = _make_broken_project(tmp_path)

        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
            "pet_generation": 0,
        }

        result = await _interactive.run_start(
            file=test_file.name,
            theorem="my_theorem",
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
        )

        # Theorem is genuinely defined in the file but rocq_start can't
        # find it because the parent module is empty in pet's view.
        assert result["success"] is False
        assert result["reason"] in ("not_found", "compile_error")

        # The key assertion: response must include something
        # actionable about the load-path failure.  Today's behavior
        # is to return only ``Theorem_not_found`` — which is the
        # symptom, not the cause.
        error_text = (
            (result.get("error") or "")
            + " "
            + str(result.get("compile_diagnostic") or "")
        ).lower()

        # The actual error from coqc would mention "physical path",
        # "logical path", "cannot find", or the offending module name.
        diagnostic_clues = [
            "physical path",
            "bogus.lib",
            "bogus.t",
            "cannot find",
            "logical path",
            "require import",
        ]
        assert any(clue in error_text for clue in diagnostic_clues), (
            f"Expected the response to include a compile-side diagnostic "
            f"explaining the load-path failure. Got:\n"
            f"  error: {result.get('error')!r}\n"
            f"  compile_diagnostic: {result.get('compile_diagnostic')!r}\n"
            f"  reason: {result.get('reason')!r}\n"
            f"This is the silent-import-failure regression — see "
            f"test docstring for context."
        )

    @pytest.mark.asyncio
    async def test_start_on_silently_empty_module_surfaces_root_cause(self, tmp_path):
        """Targeted test for the real-world silent-failure case I hit
        repeatedly: the theorem name parses fine but its containing
        module never registers because an upstream definition in that
        module failed.  Today's behavior: ``Theorem_not_found`` with
        no upstream hint.  Desired: surface the actual compile error.
        """
        import rocq_mcp.interactive as _interactive

        test_file = _make_silently_empty_module_project(tmp_path)

        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
            "pet_generation": 0,
        }

        result = await _interactive.run_start(
            file=test_file.name,
            theorem="my_theorem",
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
        )

        # If pet returned success, the response must at minimum
        # acknowledge the upstream parse errors — currently it doesn't.
        # The user would proceed thinking the proof started cleanly
        # when in fact half the file failed to elaborate.
        if result.get("success") is True:
            # The desired behavior: a 'file_diagnostics' field
            # surfacing what failed in the file.
            assert (
                "warnings" in result
                or "parse_errors" in result
                or "compile_diagnostic" in result
                or "file_diagnostics" in result
            ), (
                f"rocq_start returned success=True for a file with broken "
                f"Require Import and broken Definition, but didn't surface "
                f"the parse errors. The user has no signal that elaboration "
                f"is degraded. Got: {result!r}"
            )
            # And the surfaced diagnostic must mention at least one of
            # the failing symbols / paths.
            diag = (
                str(result.get("file_diagnostics") or "")
                + " "
                + str(result.get("compile_diagnostic") or "")
            ).lower()
            assert any(
                clue in diag
                for clue in (
                    "bogus.lib",
                    "bogus.t",
                    "bogus.zero",
                    "physical path",
                    "cannot find",
                    "logical path",
                    "not found",
                    "require import",
                )
            ), f"file_diagnostics didn't mention the upstream cause: {diag!r}"
            return

        error_text = (
            (result.get("error") or "")
            + " "
            + str(result.get("compile_diagnostic") or "")
        ).lower()

        diagnostic_clues = [
            "physical path",
            "bogus.lib",
            "bogus.t",
            "bogus.zero",
            "cannot find",
            "logical path",
            "require import",
        ]
        assert any(clue in error_text for clue in diagnostic_clues), (
            f"rocq_start on a theorem whose enclosing module never "
            f"registered (due to upstream failures) should surface the "
            f"actual upstream error.  Got:\n"
            f"  error: {result.get('error')!r}\n"
            f"  compile_diagnostic: {result.get('compile_diagnostic')!r}\n"
        )

    @pytest.mark.asyncio
    async def test_toc_on_broken_file_reports_compile_error(self, tmp_path):
        """rocq_toc on a file with a broken Require Import should not
        silently return an empty outline.  The user has no way to
        distinguish that from a file with no definitions.
        """
        import rocq_mcp.interactive as _interactive

        test_file = _make_broken_project(tmp_path)

        lifespan_state = {
            "pet_client": None,
            "pet_timeout": 30.0,
            "current_workspace": None,
            "pet_generation": 0,
        }

        result = await _interactive.run_toc(
            file=test_file.name,
            workspace=str(tmp_path),
            lifespan_state=lifespan_state,
        )

        # Either return the outline (if pet recovers gracefully) OR
        # surface the compile error.  The current behavior — silently
        # returning an empty outline — is the regression we want to
        # avoid.
        output = (result.get("output") or "").lower()
        compile_diag = str(result.get("compile_diagnostic") or "").lower()

        # If pet returned content, fine.  If pet returned nothing, the
        # diagnostic must explain why.
        has_real_content = "lemma" in output or "theorem" in output or "module" in output
        has_compile_diagnostic = (
            "physical path" in compile_diag
            or "cannot find" in compile_diag
            or "bogus.lib" in compile_diag
        )
        assert has_real_content or has_compile_diagnostic, (
            f"rocq_toc on a file with broken Require Import returned a "
            f"useless empty outline. Expected either the actual content "
            f"or a compile_diagnostic field. Got: {result!r}"
        )
