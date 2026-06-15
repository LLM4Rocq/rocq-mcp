"""Tests for the rocq_compile_file tool."""

from __future__ import annotations

import asyncio
import glob as glob_mod
import pytest

from tests.conftest import (
    COQC_AVAILABLE,
    _MockContext,
    _fake_coqc_result,
    make_lifespan_state,
)
from rocq_mcp.compile import run_compile_file

pytestmark = pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")


# ---------------------------------------------------------------------------
# Success cases
# ---------------------------------------------------------------------------


class TestCompileFileSuccess:
    """Files that compile without error."""

    def test_simple_proof_file(self, workspace, simple_proof):
        path = workspace / "simple.v"
        path.write_text(simple_proof)
        result = run_compile_file(file="simple.v", workspace=str(workspace), timeout=60)
        assert result["success"] is True

    def test_empty_file(self, workspace):
        path = workspace / "empty.v"
        path.write_text("")
        result = run_compile_file(file="empty.v", workspace=str(workspace), timeout=60)
        assert result["success"] is True


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------


class TestCompileFileErrors:
    """Files that should fail compilation with a clear error."""

    def test_type_error(self, workspace):
        path = workspace / "type_err.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="type_err.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error" in result
        assert len(result["error"]) > 0

    def test_error_uses_file_label(self, workspace):
        """Error output should use the file name, not <proof>."""
        path = workspace / "label_test.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="label_test.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "label_test.v" in result["error"]
        assert "<proof>" not in result["error"]


# ---------------------------------------------------------------------------
# Input validation
# ---------------------------------------------------------------------------


class TestCompileFileValidation:
    """Edge cases around path validation."""

    def test_nonexistent_file(self, workspace):
        result = run_compile_file(
            file="nonexistent.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "not found" in result["error"].lower()

    def test_path_traversal(self, workspace):
        result = run_compile_file(
            file="../../../etc/passwd", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "within workspace" in result["error"].lower()

    def test_oversized_file(self, workspace, monkeypatch):
        path = workspace / "big.v"
        path.write_text("x" * 100)
        import rocq_mcp.server as _srv

        monkeypatch.setattr(_srv, "ROCQ_MAX_SOURCE_SIZE", 50)
        result = run_compile_file(file="big.v", workspace=str(workspace), timeout=60)
        assert result["success"] is False
        assert "size" in result["error"].lower()


# ---------------------------------------------------------------------------
# Cleanup
# ---------------------------------------------------------------------------


class TestCompileFileCleanup:
    """Compilation should clean artifacts but preserve the source .v file."""

    def test_source_preserved_artifacts_cleaned(self, workspace, simple_proof):
        path = workspace / "preserved.v"
        path.write_text(simple_proof)
        run_compile_file(file="preserved.v", workspace=str(workspace), timeout=60)
        # Source file must still exist
        assert path.exists(), "Source .v file was deleted"
        # Artifacts should be cleaned
        base = workspace / "preserved"
        for ext in [".vo", ".vok", ".vos", ".glob"]:
            assert not base.with_suffix(ext).exists(), f"Artifact {ext} not cleaned"

    def test_source_preserved_on_error(self, workspace):
        path = workspace / "err_preserve.v"
        path.write_text("Theorem bad : .\nQed.\n")
        run_compile_file(file="err_preserve.v", workspace=str(workspace), timeout=60)
        assert path.exists(), "Source .v file was deleted on error"


# ---------------------------------------------------------------------------
# Forbidden commands
# ---------------------------------------------------------------------------


class TestCompileFileForbidden:
    """Files with forbidden commands should be rejected before compilation."""

    def test_drop_command_rejected(self, workspace):
        path = workspace / "forbidden_drop.v"
        path.write_text("Drop.\n")
        result = run_compile_file(
            file="forbidden_drop.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error" in result

    def test_redirect_rejected(self, workspace):
        path = workspace / "forbidden_redirect.v"
        path.write_text('Redirect "/tmp/out" Check nat.\n')
        result = run_compile_file(
            file="forbidden_redirect.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error" in result


# ---------------------------------------------------------------------------
# Directory handling
# ---------------------------------------------------------------------------


class TestCompileFileDirectory:
    """Edge cases for directory paths."""

    def test_not_a_file(self, workspace):
        subdir = workspace / "subdir"
        subdir.mkdir(exist_ok=True)
        result = run_compile_file(file="subdir", workspace=str(workspace), timeout=60)
        assert result["success"] is False
        assert "not found" in result["error"].lower()


# ---------------------------------------------------------------------------
# Timeout (monkeypatched)
# ---------------------------------------------------------------------------


class TestCompileFileTimeout:
    """Test timeout handling via monkeypatched _run_coqc_file."""

    # Override module-level skip — these tests use monkeypatch, not real coqc
    pytestmark = []

    def test_timeout_returns_error(self, workspace, monkeypatch):
        """When _run_coqc_file reports timed_out=True, result shows timeout error."""
        path = workspace / "timeout_test.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        import rocq_mcp.compile as _compile

        monkeypatch.setattr(
            _compile,
            "_run_coqc_file",
            lambda fp, ws, to, keep_vo=False, mode="full", timing=False: {
                "returncode": -1,
                "stdout": "",
                "stderr": "",
                "timed_out": True,
            },
        )
        result = run_compile_file(
            file="timeout_test.v", workspace=str(workspace), timeout=5
        )
        assert result["success"] is False
        assert "timed out" in result["error"].lower()


# ---------------------------------------------------------------------------
# Structured error output
# ---------------------------------------------------------------------------


class TestCompileFileStructuredErrors:
    """Verify error_positions and hint keys in structured error output."""

    def test_error_positions_present(self, workspace):
        """Compilation error should include error_positions with line info."""
        path = workspace / "pos_test.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="pos_test.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "error_positions" in result
        assert len(result["error_positions"]) >= 1
        pos = result["error_positions"][0]
        assert "line" in pos
        assert "character" in pos
        assert "message" in pos

    def test_hint_present_on_error(self, workspace):
        """Compilation error should include a hint."""
        path = workspace / "hint_test.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")
        result = run_compile_file(
            file="hint_test.v", workspace=str(workspace), timeout=60
        )
        assert result["success"] is False
        assert "hint" in result


# ---------------------------------------------------------------------------
# Proof-state capture on compile errors
# ---------------------------------------------------------------------------


class TestCompileFileErrorStateCapture:
    """Compile-file orchestration: only the file-path-specific behaviours.

    Status-derivation logic is exercised by ``test_compile.TestStateCaptureStatus``
    via the inline-source path; the file-path code path shares the same
    ``_capture_compile_error_state`` machinery, so we only assert here the
    file-resolution glue (resolved_file, file_label).
    """

    pytestmark = []

    def test_compile_file_capture_receives_resolved_path(self, workspace, monkeypatch):
        """The resolved path and file_label flow through to capture_position_state."""
        import rocq_mcp.compile as _compile
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as _server

        path = workspace / "resolved_path_test.v"
        path.write_text("Theorem bad : True.\n  exact 0.\n")
        stderr = (
            'File "resolved_path_test.v", line 2, characters 1-8:\n'
            "Error: Real failure.\n"
        )
        captured = {}

        monkeypatch.setattr(
            _compile,
            "_run_coqc_file",
            lambda *a, **kw: _fake_coqc_result(stderr),
        )

        async def _mock_cps(**kwargs):
            captured.update(kwargs)
            return {"success": False, "error": "boom", "pet_restarted": True}

        monkeypatch.setattr(_interactive, "capture_position_state", _mock_cps)

        asyncio.run(
            _server.run_compile_file_with_state(
                file="resolved_path_test.v",
                workspace=str(workspace),
                timeout=60,
                lifespan_state=make_lifespan_state(),
            )
        )

        assert captured["file"] == "resolved_path_test.v"
        assert captured["resolved_file"] == str(path.resolve())

    def test_status_no_position_when_path_resolution_fails(
        self, workspace, monkeypatch
    ):
        """A path that escapes the workspace short-circuits with status='no_position'."""
        import rocq_mcp.compile as _compile
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as _server

        stderr = "Error: nonsense.\n"
        cps_called = {"called": False}

        monkeypatch.setattr(
            _compile,
            "_run_coqc_file",
            lambda *a, **kw: _fake_coqc_result(stderr),
        )

        async def _mock_cps(**kwargs):
            cps_called["called"] = True
            return {"success": False, "error": "should not be reached"}

        monkeypatch.setattr(_interactive, "capture_position_state", _mock_cps)

        result = asyncio.run(
            _server.run_compile_file_with_state(
                file="../escaping_path.v",
                workspace=str(workspace),
                timeout=60,
                lifespan_state=make_lifespan_state(),
            )
        )

        assert result["success"] is False
        assert result["state_capture_status"] == "no_position"
        assert "state_id" not in result
        assert cps_called["called"] is False


# ---------------------------------------------------------------------------
# Wrapper forwarding
# ---------------------------------------------------------------------------


class TestRocqCompileFileWrapper:
    """The server wrapper should forward ctx.lifespan_context."""

    pytestmark = []

    def test_ctx_forwarded(self, monkeypatch, tmp_path):
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        captured = {}

        async def mock_run_compile_file_with_state(
            file,
            workspace,
            timeout,
            include_warnings,
            lifespan_state=None,
            keep_vo=False,
            mode="full",
            timing=False,
        ):
            captured.update(
                {
                    "file": file,
                    "workspace": workspace,
                    "timeout": timeout,
                    "include_warnings": include_warnings,
                    "lifespan_state": lifespan_state,
                    "keep_vo": keep_vo,
                    "timing": timing,
                }
            )
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        monkeypatch.setattr(
            _server,
            "run_compile_file_with_state",
            mock_run_compile_file_with_state,
        )

        mock_ctx = _MockContext({"pet_client": None})

        result = asyncio.run(
            rocq_compile_file(
                file="proof.v",
                workspace=str(tmp_path),
                timeout=9,
                include_warnings=False,
                ctx=mock_ctx,
            )
        )

        assert result["success"] is True
        assert captured["file"] == "proof.v"
        assert captured["workspace"] == str(tmp_path)
        assert captured["timeout"] == 9
        assert captured["include_warnings"] is False
        assert captured["lifespan_state"] is mock_ctx.lifespan_context
        assert captured["timing"] is False


# ---------------------------------------------------------------------------
# keep_vo behaviour
# ---------------------------------------------------------------------------


_TRIVIAL_PROOF = "Theorem t : True. Proof. exact I. Qed.\n"


class TestKeepVo:
    """The ``keep_vo`` option toggles whether the .vo family survives cleanup.

    Contract (see SHARED DESIGN CONTRACT):

    * ``keep_vo=False`` (default): every extension in
      ``_CLEANUP_EXTENSIONS`` except ``.v`` is deleted — current behaviour.
    * ``keep_vo=True``: ``.vo`` / ``.vok`` / ``.vos`` (the ``_VO_FAMILY``
      set) are preserved; ``.glob`` / ``.aux`` / ``.vio`` / ``.timing`` /
      ``.coqaux`` are still cleaned.

    Plumbing chain exercised:
        ``rocq_compile_file`` (wrapper)
          -> ``run_compile_file_with_state`` (enrichment)
            -> ``run_compile_file``           (orchestrator)
              -> ``_run_coqc_file``           (subprocess + cleanup loop)
    """

    def test_default_cleans_vo(self, workspace):
        """Default ``keep_vo=False`` deletes the produced .vo (current behaviour)."""
        path = workspace / "kv_default.v"
        path.write_text(_TRIVIAL_PROOF)
        result = run_compile_file(
            file="kv_default.v", workspace=str(workspace), timeout=30
        )
        assert result["success"] is True
        assert not (
            workspace / "kv_default.vo"
        ).exists(), "Default keep_vo=False should still clean the .vo artifact."

    def test_keep_vo_true_preserves_vo(self, workspace):
        """``keep_vo=True`` preserves the .vo file next to the source."""
        path = workspace / "kv_keep.v"
        path.write_text(_TRIVIAL_PROOF)
        try:
            result = run_compile_file(
                file="kv_keep.v",
                workspace=str(workspace),
                timeout=30,
                keep_vo=True,
            )
            assert result["success"] is True
            assert (
                workspace / "kv_keep.vo"
            ).exists(), "keep_vo=True must preserve the .vo file."
        finally:
            # Test hygiene: don't leave a .vo behind for the next test.
            (workspace / "kv_keep.vo").unlink(missing_ok=True)
            (workspace / "kv_keep.vok").unlink(missing_ok=True)
            (workspace / "kv_keep.vos").unlink(missing_ok=True)

    def test_keep_vo_true_still_cleans_aux_artifacts(self, workspace):
        """``keep_vo`` is scoped to the .vo family only — .glob / .aux still go."""
        path = workspace / "kv_aux.v"
        path.write_text(_TRIVIAL_PROOF)
        try:
            result = run_compile_file(
                file="kv_aux.v",
                workspace=str(workspace),
                timeout=30,
                keep_vo=True,
            )
            assert result["success"] is True
            # The .vo survives.
            assert (workspace / "kv_aux.vo").exists()
            # But auxiliary artifacts are still cleaned.  coqc does not
            # always produce every one of these (e.g. .aux is rare on
            # modern Rocq), so we assert absence rather than presence-
            # then-absence — the cleanup loop should have unlinked any
            # that did appear.
            for ext in (".glob", ".aux", ".vio", ".timing", ".coqaux"):
                assert not (
                    workspace / f"kv_aux{ext}"
                ).exists(), f"keep_vo=True should still clean the {ext} artifact."
        finally:
            (workspace / "kv_aux.vo").unlink(missing_ok=True)
            (workspace / "kv_aux.vok").unlink(missing_ok=True)
            (workspace / "kv_aux.vos").unlink(missing_ok=True)

    def test_keep_vo_with_compile_error(self, workspace):
        """Cleanup loop tolerates missing .vo on a compile failure.

        coqc does not produce a .vo when compilation fails, so the
        cleanup loop runs against missing files regardless of
        ``keep_vo``.  Both branches must complete without raising.
        """
        path = workspace / "kv_err.v"
        path.write_text("Theorem bad : nat = bool.\nProof. reflexivity. Qed.\n")

        # Default — no exception, no .vo.
        result_default = run_compile_file(
            file="kv_err.v", workspace=str(workspace), timeout=30
        )
        assert result_default["success"] is False
        assert not (workspace / "kv_err.vo").exists()

        # keep_vo=True — still no exception, still no .vo (coqc never
        # made one).
        result_keep = run_compile_file(
            file="kv_err.v",
            workspace=str(workspace),
            timeout=30,
            keep_vo=True,
        )
        assert result_keep["success"] is False
        assert not (workspace / "kv_err.vo").exists()

    def test_keep_vo_plumbed_through_wrapper(self, tmp_path, monkeypatch):
        """The ``keep_vo`` kwarg must reach ``run_compile_file_with_state``."""
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        captured: dict = {}

        async def mock_run_compile_file_with_state(
            file,
            workspace,
            timeout,
            include_warnings,
            lifespan_state=None,
            keep_vo=False,
            mode="full",
            timing=False,
        ):
            captured.update(
                {
                    "file": file,
                    "workspace": workspace,
                    "timeout": timeout,
                    "include_warnings": include_warnings,
                    "lifespan_state": lifespan_state,
                    "keep_vo": keep_vo,
                    "timing": timing,
                }
            )
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        monkeypatch.setattr(
            _server,
            "run_compile_file_with_state",
            mock_run_compile_file_with_state,
        )

        mock_ctx = _MockContext({"pet_client": None})

        result = asyncio.run(
            rocq_compile_file(
                file="proof.v",
                workspace=str(tmp_path),
                timeout=9,
                include_warnings=True,
                keep_vo=True,
                ctx=mock_ctx,
            )
        )

        assert result["success"] is True
        assert captured["keep_vo"] is True

    def test_vok_and_vos_also_preserved(self):
        """``.vok`` and ``.vos`` belong to the preserved family.

        Coqc may not emit ``.vok``/``.vos`` by default (they are produced
        by ``-vos`` / ``-vok`` modes), so the most robust check is
        structural: the implementation must reference a ``_VO_FAMILY``
        set (or equivalent) that contains all three extensions.  This
        keeps the test stable across coqc versions and avoids mocking
        the subprocess just to seed artifacts.
        """
        import rocq_mcp.compile as _compile

        vo_family = getattr(_compile, "_VO_FAMILY", None)
        assert vo_family is not None, (
            "Expected ``_VO_FAMILY`` to be defined on rocq_mcp.compile "
            "as the set of extensions preserved by ``keep_vo=True``."
        )
        vo_family_set = set(vo_family)
        assert {".vo", ".vok", ".vos"}.issubset(
            vo_family_set
        ), f"_VO_FAMILY must contain .vo, .vok, .vos; got {vo_family_set!r}."
        # And the auxiliary extensions must NOT be in the preserved family.
        assert not vo_family_set & {
            ".glob",
            ".aux",
            ".vio",
            ".timing",
            ".coqaux",
        }, "_VO_FAMILY must not include the auxiliary artifacts."


# ---------------------------------------------------------------------------
# keep_vo — smoke / integration via the @mcp.tool wrapper
# ---------------------------------------------------------------------------


class TestKeepVoIntegration:
    """End-to-end behaviour through the @mcp.tool wrapper with a real coqc.

    Skipped automatically when ``coqc`` is not on PATH via the module-level
    ``pytestmark``.  Confirms the ``keep_vo=True`` behaviour is observable
    from the outermost entrypoint and does not perturb the envelope shape
    of a successful compile.
    """

    def test_wrapper_keep_vo_preserves_vo_and_shape(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "kv_e2e.v"
        path.write_text(_TRIVIAL_PROOF)
        mock_ctx = _MockContext(make_lifespan_state())

        try:
            result = asyncio.run(
                rocq_compile_file(
                    file="kv_e2e.v",
                    workspace=str(workspace),
                    timeout=60,
                    include_warnings=True,
                    keep_vo=True,
                    ctx=mock_ctx,
                )
            )
            assert result["success"] is True, result
            assert (
                workspace / "kv_e2e.vo"
            ).exists(), "Wrapper-level keep_vo=True must preserve the .vo file."
            # Envelope shape: no surprise new keys introduced by this flag.
            # ``keep_vo`` is a behaviour switch, not a payload field.
            assert "keep_vo" not in result
        finally:
            (workspace / "kv_e2e.vo").unlink(missing_ok=True)
            (workspace / "kv_e2e.vok").unlink(missing_ok=True)
            (workspace / "kv_e2e.vos").unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Per-sentence timing diagnostics (``timing=True``)
# ---------------------------------------------------------------------------


_SAMPLE_TIMING_OUTPUT = (
    "Chars 0 - 18 [Theorem~t1~:~True.] 0. secs (0.u,0.s)\n"
    "Chars 19 - 25 [Proof.] 0.001 secs (0.u,0.s)\n"
    "Chars 26 - 34 [exact~I.] 0.5 secs (0.u,0.s)\n"
    "Chars 35 - 39 [Qed.] 0.002 secs (0.u,0.s)\n"
)


class TestTiming:
    """The ``timing=True`` option surfaces coqc ``-time`` diagnostics.

    Contract:

    * ``timing=False`` (default) — no ``-time`` flag, no ``timing`` field.
    * ``timing=True`` — coqc is invoked with ``-time``; response gains a
      ``timing`` field carrying ``total_sentences``, ``top_slowest``
      (default top 5 by descending duration), and ``last_completed``.
    * On timeout, ``last_completed`` is the final emitted entry from the
      partial stderr buffer and is named in the ``error`` string.
    * Parser is tolerant: garbage in stderr is ignored; parse failures
      fall back to an empty timing list rather than crashing the response.
    """

    pytestmark = []

    # ------------------------------------------------------------------ #
    # Default path: no flag, no field                                    #
    # ------------------------------------------------------------------ #

    def test_default_timing_false_no_field(self, workspace, monkeypatch):
        """Without ``timing=True``, no ``-time`` flag is passed and no
        ``timing`` field appears in the response."""
        import rocq_mcp.compile as _compile

        path = workspace / "timing_default.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        seen_timing: dict = {"value": None}

        def fake_run(fp, ws, to, keep_vo=False, mode="full", *, timing=False):
            seen_timing["value"] = timing
            return _fake_coqc_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_coqc_file", fake_run)
        result = run_compile_file(
            file="timing_default.v", workspace=str(workspace), timeout=10
        )
        assert seen_timing["value"] is False
        assert "timing" not in result

    def test_timing_true_passes_flag(self, workspace, monkeypatch):
        """``timing=True`` propagates as a kwarg into ``_run_coqc_file``."""
        import rocq_mcp.compile as _compile

        path = workspace / "timing_flag.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        seen_timing: dict = {"value": None}

        def fake_run(fp, ws, to, keep_vo=False, mode="full", *, timing=False):
            seen_timing["value"] = timing
            return {
                "returncode": 0,
                # coqc 9.x emits ``-time`` to stdout
                "stdout": _SAMPLE_TIMING_OUTPUT,
                "stderr": "",
                "timed_out": False,
            }

        monkeypatch.setattr(_compile, "_run_coqc_file", fake_run)
        result = run_compile_file(
            file="timing_flag.v",
            workspace=str(workspace),
            timeout=10,
            timing=True,
        )
        assert seen_timing["value"] is True
        assert "timing" in result
        assert result["timing"]["total_sentences"] == 4
        # The success-path ``output`` field must not be flooded with the
        # timing-line firehose — they are stripped before truncation.
        assert "Chars 0 - 18" not in result["output"]

    def test_timing_true_passes_time_to_coqc(self, workspace, monkeypatch):
        """``timing=True`` adds ``-time`` to the subprocess args.

        Asserts at the lowest layer (``_run_coqc_process``) that the
        flag actually reaches coqc.
        """
        import rocq_mcp.compile as _compile

        path = workspace / "timing_argv.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        captured: dict = {}

        class _FakeProc:
            returncode = 0
            pid = 0

            def communicate(self, timeout=None):
                return ("", "")

        def fake_popen(args, **_kwargs):
            captured["args"] = list(args)
            return _FakeProc()

        monkeypatch.setattr(_compile.subprocess, "Popen", fake_popen)
        # Patch the cleanup target so we don't try to unlink real files.
        _compile._run_coqc_process(str(path), workspace, 10, timing=True)
        assert "-time" in captured["args"]

        # And without timing, no flag.
        captured.clear()
        _compile._run_coqc_process(str(path), workspace, 10, timing=False)
        assert "-time" not in captured["args"]

    # ------------------------------------------------------------------ #
    # Parser                                                             #
    # ------------------------------------------------------------------ #

    def test_timing_parser_basic(self):
        """Parser extracts canonical fields from coqc -time stderr."""
        from rocq_mcp.compile import _parse_timing_lines

        # Source matches char ranges so line conversion is deterministic.
        source = (
            "Theorem t1 : True.\n"  # 19 chars including \n  (0..18 + \n)
            "Proof.\n"  # 7 chars (19..25 + \n)
            "exact I.\n"  # 9 chars
            "Qed.\n"
        )
        entries = _parse_timing_lines(_SAMPLE_TIMING_OUTPUT, source)
        assert len(entries) == 4

        e0 = entries[0]
        assert e0["line"] == 1
        assert e0["characters"] == [0, 18]
        assert e0["name"] == "Theorem~t1~:~True."
        assert e0["duration_seconds"] == 0.0

        e2 = entries[2]
        assert e2["name"] == "exact~I."
        assert e2["duration_seconds"] == 0.5

    def test_timing_parser_tolerates_garbage(self):
        """Non-timing lines (warnings, blanks, errors) are silently skipped."""
        from rocq_mcp.compile import _parse_timing_lines

        stderr = (
            'File "/tmp/x.v", line 1, characters 15-20:\n'
            "Warning: Loading Stdlib without prefix is deprecated.\n"
            "[deprecated-missing-stdlib,deprecated-since-9.0,deprecated,default]\n"
            "\n"
            "Chars 0 - 18 [Theorem~t1~:~True.] 0.013 secs (0.u,0.s)\n"
            "Error: Whatever.\n"
            "Chars 19 - 25 [Proof.] 0.001 secs (0.u,0.s)\n"
        )
        entries = _parse_timing_lines(stderr, "Theorem t1 : True.\nProof.\n")
        assert len(entries) == 2
        assert entries[0]["duration_seconds"] == 0.013
        assert entries[1]["name"] == "Proof."

    def test_timing_parser_empty_stderr(self):
        """Empty stderr yields an empty entry list."""
        from rocq_mcp.compile import _parse_timing_lines

        assert _parse_timing_lines("", "Theorem t : True.\n") == []

    def test_timing_top_slowest_sorted(self):
        """``top_slowest`` is sorted by descending duration; default N=5."""
        from rocq_mcp.compile import _build_timing_field

        entries = [
            {
                "line": i,
                "characters": [0, 0],
                "name": f"s{i}",
                "duration_seconds": float(i),
            }
            for i in range(10)
        ]
        timing = _build_timing_field(entries)
        assert timing["total_sentences"] == 10
        assert len(timing["top_slowest"]) == 5
        durations = [e["duration_seconds"] for e in timing["top_slowest"]]
        assert durations == sorted(durations, reverse=True)
        assert durations[0] == 9.0  # slowest first

    def test_timing_top_slowest_custom_n(self):
        """``_build_timing_field`` honours a custom top-N."""
        from rocq_mcp.compile import _build_timing_field

        entries = [
            {
                "line": i,
                "characters": [0, 0],
                "name": f"s{i}",
                "duration_seconds": float(i),
            }
            for i in range(4)
        ]
        timing = _build_timing_field(entries, top_n=2)
        assert len(timing["top_slowest"]) == 2

    def test_timing_last_completed_field(self):
        """``last_completed`` is the final emitted entry (preserving order)."""
        from rocq_mcp.compile import _build_timing_field

        entries = [
            {"line": 1, "characters": [0, 5], "name": "A", "duration_seconds": 9.0},
            {"line": 2, "characters": [6, 9], "name": "B", "duration_seconds": 1.0},
        ]
        timing = _build_timing_field(entries)
        assert timing["last_completed"]["name"] == "B"
        # Empty list → None
        assert _build_timing_field([])["last_completed"] is None

    def test_timing_line_number_conversion(self):
        """Char-offset → 1-based line number uses the actual source layout."""
        from rocq_mcp.compile import _char_offset_to_line

        # 3 lines of 10 chars each (incl. newline).
        source = "abcdefghi\njklmnopqr\nstuvwxyz0\n"
        assert _char_offset_to_line(source, 0) == 1
        assert _char_offset_to_line(source, 9) == 1  # at last char of line 1
        assert _char_offset_to_line(source, 10) == 2
        assert _char_offset_to_line(source, 25) == 3
        # Out-of-range offsets clamp to the last line rather than crash.
        assert _char_offset_to_line(source, 10_000) >= 3

    # ------------------------------------------------------------------ #
    # Timeout path                                                       #
    # ------------------------------------------------------------------ #

    def test_timing_last_completed_on_timeout(self, workspace, monkeypatch):
        """On timeout, partial stderr is still parsed and ``last_completed``
        is woven into the error string so the agent sees the offending
        sentence."""
        import rocq_mcp.compile as _compile

        path = workspace / "timing_to.v"
        # Make the source long enough that char 26 is on line 3 (matches
        # the third timing entry).
        path.write_text("Theorem t1 : True.\n" "Proof.\n" "exact I.\n" "Qed.\n")

        partial_output = (
            "Chars 0 - 18 [Theorem~t1~:~True.] 0.1 secs (0.u,0.s)\n"
            "Chars 19 - 25 [Proof.] 0.1 secs (0.u,0.s)\n"
            "Chars 26 - 34 [exact~I.] 15.3 secs (0.u,0.s)\n"
        )

        def fake_run(fp, ws, to, keep_vo=False, mode="full", *, timing=False):
            return {
                "returncode": -1,
                # coqc 9.x flushes per-sentence timing to stdout before
                # the SIGTERM kill on a timeout.
                "stdout": partial_output,
                "stderr": "",
                "timed_out": True,
            }

        monkeypatch.setattr(_compile, "_run_coqc_file", fake_run)

        result = run_compile_file(
            file="timing_to.v",
            workspace=str(workspace),
            timeout=10,
            timing=True,
        )
        assert result["success"] is False
        assert result["reason"] == "timeout"
        assert "timing" in result
        last = result["timing"]["last_completed"]
        assert last is not None
        assert last["name"] == "exact~I."
        # The error string is enriched with the last-completed phrase
        # so "timed out" becomes actionable.
        err = result["error"]
        assert "Last completed sentence" in err
        assert "exact~I." in err
        assert f"line {last['line']}" in err

    def test_timing_parser_returns_empty_on_malformed_durations(self):
        """A duration that can't be cast to float drops just that entry."""
        from rocq_mcp.compile import _parse_timing_lines

        stderr = (
            "Chars 0 - 18 [A] 0.013 secs (0.u,0.s)\n"
            "Chars 19 - 25 [B] NOTANUMBER secs (0.u,0.s)\n"
            "Chars 26 - 34 [C] 0.5 secs (0.u,0.s)\n"
        )
        entries = _parse_timing_lines(stderr, "X" * 40)
        # The malformed middle line fails the regex (NOTANUMBER doesn't
        # match ``[0-9.]+``) and is dropped, but the two valid entries
        # come through.
        assert len(entries) == 2
        assert entries[0]["name"] == "A"
        assert entries[1]["name"] == "C"

    # ------------------------------------------------------------------ #
    # Integration with real coqc                                         #
    # ------------------------------------------------------------------ #

    @pytest.mark.skipif(not COQC_AVAILABLE, reason="coqc not available")
    def test_timing_integration_returns_entries(self, workspace):
        """End-to-end: real coqc with ``timing=True`` yields non-empty
        timing data on a successful compile."""
        path = workspace / "timing_int.v"
        path.write_text(
            "Theorem t : True. Proof. exact I. Qed.\n"
            "Theorem t2 : 1 + 1 = 2. Proof. reflexivity. Qed.\n"
        )
        result = run_compile_file(
            file="timing_int.v",
            workspace=str(workspace),
            timeout=60,
            timing=True,
        )
        assert result["success"] is True, result
        assert "timing" in result
        timing = result["timing"]
        assert timing["total_sentences"] > 0
        assert isinstance(timing["top_slowest"], list)
        # ``last_completed`` is the final sentence's entry.
        assert timing["last_completed"] is not None
        assert "name" in timing["last_completed"]

    def test_timing_plumbed_through_wrapper(self, tmp_path, monkeypatch):
        """The ``timing`` kwarg reaches ``run_compile_file_with_state``."""
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        captured: dict = {}

        async def mock_rcfws(
            file,
            workspace,
            timeout,
            include_warnings,
            lifespan_state=None,
            keep_vo=False,
            mode="full",
            timing=False,
        ):
            captured["timing"] = timing
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        monkeypatch.setattr(_server, "run_compile_file_with_state", mock_rcfws)

        mock_ctx = _MockContext({"pet_client": None})
        result = asyncio.run(
            rocq_compile_file(
                file="proof.v",
                workspace=str(tmp_path),
                timeout=9,
                include_warnings=True,
                timing=True,
                ctx=mock_ctx,
            )
        )
        assert result["success"] is True
        assert captured["timing"] is True


# ---------------------------------------------------------------------------


class TestVosMode:
    """The ``mode`` option selects the coqc pass.

    Contract:

    * ``mode="full"`` (default): today's behaviour — full coqc, ``.vo``
      artifact.
    * ``mode="vos"``: passes ``-vos`` to coqc; statements / imports /
      notations are checked but proof bodies are skipped.  Produces a
      ``.vos`` artifact rather than ``.vo``.
    * Any other value is rejected as a validation error before coqc is
      invoked.
    """

    # Override the module-level coqc-skip for the mock-based tests; the
    # integration tests in this class re-impose the skip individually.
    pytestmark = []

    def test_default_mode_is_full(self, workspace, monkeypatch):
        """No ``mode`` arg => coqc command line does NOT include ``-vos``."""
        import rocq_mcp.compile as _compile

        captured: dict = {}

        def fake_process(file_path, ws, timeout, mode="full", *, timing=False):
            captured["mode"] = mode
            return {"returncode": 0, "stdout": "", "stderr": "", "timed_out": False}

        monkeypatch.setattr(_compile, "_run_coqc_process", fake_process)

        path = workspace / "vos_default.v"
        path.write_text(_TRIVIAL_PROOF)
        result = run_compile_file(
            file="vos_default.v", workspace=str(workspace), timeout=30
        )
        assert result["success"] is True
        assert captured["mode"] == "full"

    def test_mode_vos_passes_flag(self, workspace, monkeypatch):
        """``mode="vos"`` => underlying ``Popen`` call list contains ``-vos``."""
        import rocq_mcp.compile as _compile

        captured: dict = {}

        class _FakeProc:
            returncode = 0

            def communicate(self, timeout=None):
                return ("", "")

        def fake_popen(args, *a, **kw):
            captured["args"] = list(args)
            return _FakeProc()

        monkeypatch.setattr(_compile.subprocess, "Popen", fake_popen)

        path = workspace / "vos_flag.v"
        path.write_text(_TRIVIAL_PROOF)
        result = run_compile_file(
            file="vos_flag.v",
            workspace=str(workspace),
            timeout=30,
            mode="vos",
        )
        assert result["success"] is True
        assert (
            "-vos" in captured["args"]
        ), f"Expected '-vos' in coqc args; got {captured['args']!r}"

    def test_invalid_mode_rejected(self, workspace):
        """``mode="bogus"`` returns a validation failure without invoking coqc."""
        path = workspace / "vos_invalid.v"
        path.write_text(_TRIVIAL_PROOF)
        result = run_compile_file(
            file="vos_invalid.v",
            workspace=str(workspace),
            timeout=30,
            mode="bogus",
        )
        assert result["success"] is False
        assert result.get("reason") == "validation"
        assert "mode" in result["error"].lower()
        # No .vo / .vos artifacts produced.
        assert not (workspace / "vos_invalid.vo").exists()
        assert not (workspace / "vos_invalid.vos").exists()

    def test_invalid_mode_rejected_at_wrapper(self, tmp_path):
        """Wrapper layer rejects an invalid ``mode`` before coqc."""
        from rocq_mcp.server import rocq_compile_file

        mock_ctx = _MockContext(make_lifespan_state())
        result = asyncio.run(
            rocq_compile_file(
                file="anything.v",
                workspace=str(tmp_path),
                timeout=5,
                include_warnings=True,
                keep_vo=False,
                mode="bogus",
                ctx=mock_ctx,
            )
        )
        assert result["success"] is False
        assert result.get("reason") == "validation"
        assert "mode" in result["error"].lower()

    def test_mode_plumbed_through_wrapper(self, tmp_path, monkeypatch):
        """The ``mode`` kwarg must reach ``run_compile_file_with_state``."""
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        captured: dict = {}

        async def mock_run_compile_file_with_state(
            file,
            workspace,
            timeout,
            include_warnings,
            lifespan_state=None,
            keep_vo=False,
            mode="full",
            timing=False,
        ):
            captured.update(
                {
                    "file": file,
                    "workspace": workspace,
                    "timeout": timeout,
                    "include_warnings": include_warnings,
                    "lifespan_state": lifespan_state,
                    "keep_vo": keep_vo,
                    "mode": mode,
                }
            )
            return {"success": True, "output": "mock"}

        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)
        monkeypatch.setattr(
            _server,
            "run_compile_file_with_state",
            mock_run_compile_file_with_state,
        )

        mock_ctx = _MockContext({"pet_client": None})

        result = asyncio.run(
            rocq_compile_file(
                file="proof.v",
                workspace=str(tmp_path),
                timeout=9,
                include_warnings=True,
                mode="vos",
                ctx=mock_ctx,
            )
        )

        assert result["success"] is True
        assert captured["mode"] == "vos"


class TestVosModeIntegration:
    """End-to-end ``mode="vos"`` against a real coqc.

    Skipped automatically when ``coqc`` is not on PATH.  Verifies the
    actual semantics of ``coqc -vos``: catches statement-level problems,
    skips proof bodies, produces a ``.vos`` artifact.
    """

    def test_mode_vos_catches_statement_type_error(self, workspace):
        """vos mode fails on a statement that cannot type-check."""
        path = workspace / "vos_stmt_err.v"
        path.write_text("Theorem foo : bad_type.\nProof. exact I. Qed.\n")
        try:
            result = run_compile_file(
                file="vos_stmt_err.v",
                workspace=str(workspace),
                timeout=60,
                mode="vos",
            )
            assert result["success"] is False
            assert "error" in result
        finally:
            for ext in (".vo", ".vok", ".vos", ".glob"):
                (workspace / f"vos_stmt_err{ext}").unlink(missing_ok=True)

    def test_mode_vos_does_not_catch_tactic_error(self, workspace):
        """vos mode skips proof bodies, so a broken tactic still succeeds."""
        path = workspace / "vos_tactic_err.v"
        # Statement is valid; proof body is nonsense — vos must accept this.
        path.write_text(
            "Theorem foo : True.\n" "Proof. apply nonsense_lemma_does_not_exist. Qed.\n"
        )
        try:
            result = run_compile_file(
                file="vos_tactic_err.v",
                workspace=str(workspace),
                timeout=60,
                mode="vos",
            )
            assert result["success"] is True, result
        finally:
            for ext in (".vo", ".vok", ".vos", ".glob"):
                (workspace / f"vos_tactic_err{ext}").unlink(missing_ok=True)

    def test_mode_vos_with_keep_vo_true_preserves_vos(self, workspace):
        """vos + keep_vo=True preserves the .vos artifact (and no .vo is produced)."""
        path = workspace / "vos_keep.v"
        path.write_text(_TRIVIAL_PROOF)
        try:
            result = run_compile_file(
                file="vos_keep.v",
                workspace=str(workspace),
                timeout=60,
                keep_vo=True,
                mode="vos",
            )
            assert result["success"] is True, result
            assert (
                workspace / "vos_keep.vos"
            ).exists(), "keep_vo=True with mode='vos' must preserve the .vos file."
            # vos mode does not produce a .vo artifact.
            assert not (workspace / "vos_keep.vo").exists()
        finally:
            for ext in (".vo", ".vok", ".vos", ".glob"):
                (workspace / f"vos_keep{ext}").unlink(missing_ok=True)
