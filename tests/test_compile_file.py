"""Tests for the rocq_compile_file tool."""

from __future__ import annotations

import asyncio
import glob as glob_mod
import pytest

from tests.conftest import (
    COMPILER_AVAILABLE,
    _MockContext,
    _fake_compiler_result,
    make_lifespan_state,
)
from rocq_mcp.compile import run_compile_file

pytestmark = pytest.mark.skipif(not COMPILER_AVAILABLE, reason="rocq c not available")


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
    """Test timeout handling via monkeypatched _run_compiler_file."""

    # Override module-level skip — these tests use monkeypatch, not real rocq c
    pytestmark = []

    def test_timeout_returns_error(self, workspace, monkeypatch):
        """When _run_compiler_file reports timed_out=True, result shows timeout error."""
        path = workspace / "timeout_test.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        import rocq_mcp.compile as _compile

        monkeypatch.setattr(
            _compile,
            "_run_compiler_file",
            lambda fp, ws, to, keep_vo=False, mode="full", timing=False, output=None: {
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
            "_run_compiler_file",
            lambda *a, **kw: _fake_compiler_result(stderr),
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
            "_run_compiler_file",
            lambda *a, **kw: _fake_compiler_result(stderr),
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
              -> ``_run_compiler_file``           (subprocess + cleanup loop)
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
            # But auxiliary artifacts are still cleaned.  rocq c does not
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

        rocq c does not produce a .vo when compilation fails, so the
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

        # keep_vo=True — still no exception, still no .vo (rocq c never
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

        Rocq c may not emit ``.vok``/``.vos`` by default (they are produced
        by ``-vos`` / ``-vok`` modes), so the most robust check is
        structural: the implementation must reference a ``_VO_FAMILY``
        set (or equivalent) that contains all three extensions.  This
        keeps the test stable across rocq c versions and avoids mocking
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
    """End-to-end behaviour through the @mcp.tool wrapper with a real rocq c.

    Skipped automatically when ``rocq c`` is not on PATH via the module-level
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
    """The ``timing=True`` option surfaces rocq c ``-time`` diagnostics.

    Contract:

    * ``timing=False`` (default) — no ``-time`` flag, no ``timing`` field.
    * ``timing=True`` — rocq c is invoked with ``-time``; response gains a
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

        def fake_run(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen_timing["value"] = timing
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_compiler_file", fake_run)
        result = run_compile_file(
            file="timing_default.v", workspace=str(workspace), timeout=10
        )
        assert seen_timing["value"] is False
        assert "timing" not in result

    def test_timing_true_passes_flag(self, workspace, monkeypatch):
        """``timing=True`` propagates as a kwarg into ``_run_compiler_file``."""
        import rocq_mcp.compile as _compile

        path = workspace / "timing_flag.v"
        path.write_text("Theorem t : True. Proof. exact I. Qed.\n")

        seen_timing: dict = {"value": None}

        def fake_run(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen_timing["value"] = timing
            return {
                "returncode": 0,
                # rocq c 9.x emits ``-time`` to stdout
                "stdout": _SAMPLE_TIMING_OUTPUT,
                "stderr": "",
                "timed_out": False,
            }

        monkeypatch.setattr(_compile, "_run_compiler_file", fake_run)
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

    def test_timing_true_passes_time_to_compiler(self, workspace, monkeypatch):
        """``timing=True`` adds ``-time`` to the subprocess args.

        Asserts at the lowest layer (``_run_compiler_process``) that the
        flag actually reaches rocq c.
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
        _compile._run_compiler_process(str(path), workspace, 10, timing=True)
        assert "-time" in captured["args"]

        # And without timing, no flag.
        captured.clear()
        _compile._run_compiler_process(str(path), workspace, 10, timing=False)
        assert "-time" not in captured["args"]

    # ------------------------------------------------------------------ #
    # Parser                                                             #
    # ------------------------------------------------------------------ #

    def test_timing_parser_basic(self):
        """Parser extracts canonical fields from rocq c -time stderr."""
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

        def fake_run(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            return {
                "returncode": -1,
                # rocq c 9.x flushes per-sentence timing to stdout before
                # the SIGTERM kill on a timeout.
                "stdout": partial_output,
                "stderr": "",
                "timed_out": True,
            }

        monkeypatch.setattr(_compile, "_run_compiler_file", fake_run)

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
    # Integration with real rocq c                                         #
    # ------------------------------------------------------------------ #

    @pytest.mark.skipif(not COMPILER_AVAILABLE, reason="rocq c not available")
    def test_timing_integration_returns_entries(self, workspace):
        """End-to-end: real rocq c with ``timing=True`` yields non-empty
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
    """The ``mode`` option selects the rocq c pass.

    Contract:

    * ``mode="full"`` (default): today's behaviour — full rocq c, ``.vo``
      artifact.
    * ``mode="vos"``: passes ``-vos`` to rocq c; statements / imports /
      notations are checked but proof bodies are skipped.  Produces a
      ``.vos`` artifact rather than ``.vo``.
    * Any other value is rejected as a validation error before rocq c is
      invoked.
    """

    # Override the module-level compiler-skip for the mock-based tests; the
    # integration tests in this class re-impose the skip individually.
    pytestmark = []

    def test_default_mode_is_full(self, workspace, monkeypatch):
        """No ``mode`` arg => rocq c command line does NOT include ``-vos``."""
        import rocq_mcp.compile as _compile

        captured: dict = {}

        def fake_process(
            file_path, ws, timeout, mode="full", *, timing=False, output=None
        ):
            captured["mode"] = mode
            return {"returncode": 0, "stdout": "", "stderr": "", "timed_out": False}

        monkeypatch.setattr(_compile, "_run_compiler_process", fake_process)

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
        ), f"Expected '-vos' in rocq c args; got {captured['args']!r}"

    def test_invalid_mode_rejected(self, workspace):
        """``mode="bogus"`` returns a validation failure without invoking rocq c."""
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
        """Wrapper layer rejects an invalid ``mode`` before rocq c."""
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
    """End-to-end ``mode="vos"`` against a real rocq c.

    Skipped automatically when ``rocq c`` is not on PATH.  Verifies the
    actual semantics of ``rocq c -vos``: catches statement-level problems,
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


# ---------------------------------------------------------------------------
# dune-build integration
# ---------------------------------------------------------------------------


def _make_dune_project(root):
    """Create a minimal modern-stanza dune project under *root*.

    Returns the source ``theory/use.v`` path.  The stanza content only
    matters when ``dune build`` is actually run (these tests mock it).
    """
    (root / "dune-project").write_text("(lang dune 3.21)\n(using rocq 0.11)\n")
    theory = root / "theory"
    theory.mkdir()
    (theory / "dune").write_text("(rocq.theory (name mwe) (modules use))\n")
    (theory / "use.v").write_text("Lemma l : 0 = 0.\nProof. reflexivity. Qed.\n")
    return theory / "use.v"


def _dune_ok():
    return {
        "returncode": 0,
        "stdout": "",
        "stderr": "",
        "timed_out": False,
        "rule_missing": False,
    }


class TestCompileFileDuneBuild:
    """rocq_compile_file keeps .vo out of the source tree in dune projects.

    All subprocess layers are mocked, so no real rocq c/dune is needed.
    """

    pytestmark = []  # override module-level rocq c skip

    def test_path_helpers(self, tmp_path):
        from pathlib import Path
        import rocq_mcp.compile as _compile

        f = str(tmp_path / "theory" / "use.v")
        assert _compile._dune_target_relpath(tmp_path, f, ".vo") == "theory/use.vo"
        assert (
            _compile._dune_build_output(tmp_path, f, ".vo")
            == tmp_path.resolve() / "_build" / "default" / "theory" / "use.vo"
        )
        # A file outside the dune root is not a dune target.
        outside = str(tmp_path.parent / "elsewhere.v")
        assert _compile._dune_target_relpath(tmp_path, outside, ".vo") is None
        assert _compile._dune_build_output(tmp_path, outside, ".vo") is None

    def test_run_dune_build_flags_rule_missing(self, tmp_path, monkeypatch):
        import rocq_mcp.compile as _compile

        def fake_sub(args, cwd, timeout):
            assert args[:2] == ["dune", "build"]
            return {
                "returncode": 1,
                "stdout": "",
                "stderr": "Error: Don't know how to build x.vo\n",
                "timed_out": False,
            }

        monkeypatch.setattr(_compile, "_run_build_subprocess", fake_sub)
        assert _compile._run_dune_build(tmp_path, "x.vo", 30)["rule_missing"] is True

        monkeypatch.setattr(
            _compile,
            "_run_build_subprocess",
            lambda *a, **k: {
                "returncode": 0,
                "stdout": "",
                "stderr": "",
                "timed_out": False,
            },
        )
        assert _compile._run_dune_build(tmp_path, "x.vo", 30)["rule_missing"] is False

    def test_dune_build_success_skips_compiler(self, tmp_path, monkeypatch):
        import rocq_mcp.compile as _compile

        _make_dune_project(tmp_path)
        seen = {"target": None, "compiler": False}

        def fake_dune(dune_root, target, timeout):
            seen["target"] = target
            return _dune_ok()

        def fake_compiler(*a, **k):
            seen["compiler"] = True
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_dune_build", fake_dune)
        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)

        result = run_compile_file("theory/use.v", str(tmp_path), 60)
        assert result["success"] is True
        assert seen["target"] == "theory/use.vo"
        assert seen["compiler"] is False  # dune handled it; no direct compile
        assert "dune_build_warning" not in result

    def test_dune_compile_error_reported_without_recompile(self, tmp_path, monkeypatch):
        import rocq_mcp.compile as _compile

        _make_dune_project(tmp_path)
        dune_err = (
            'File "./theory/use.v", line 2, characters 13-28:\n'
            "Error: The variable nope was not found in the current environment.\n"
        )
        compiler = {"called": False}

        def fake_dune(dune_root, target, timeout):
            return {
                "returncode": 1,
                "stdout": "",
                "stderr": dune_err,
                "timed_out": False,
                "rule_missing": False,
            }

        def fake_compiler(*a, **k):
            compiler["called"] = True
            return _fake_compiler_result("")

        monkeypatch.setattr(_compile, "_run_dune_build", fake_dune)
        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)

        result = run_compile_file("theory/use.v", str(tmp_path), 60)
        assert result["success"] is False
        assert result["reason"] == "compile_error"
        # dune's stderr is compiler-format, so positions parse straight through.
        assert result.get("error_positions")
        assert compiler["called"] is False  # no redundant rocq c recompile
        assert "dune_build_warning" not in result

    def test_rule_missing_falls_back_to_compiler_into_build(
        self, tmp_path, monkeypatch
    ):
        import rocq_mcp.compile as _compile

        _make_dune_project(tmp_path)
        seen = {}

        def fake_dune(dune_root, target, timeout):
            return {
                "returncode": 1,
                "stdout": "",
                "stderr": "Error: Don't know how to build theory/use.vo\n",
                "timed_out": False,
                "rule_missing": True,
            }

        def fake_compiler(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen["ws"] = ws
            seen["output"] = output
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_dune_build", fake_dune)
        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)

        result = run_compile_file("theory/use.v", str(tmp_path), 60)
        assert result["success"] is True
        assert "dune_build_warning" in result
        # rocq c fallback compiles from the dune root, output redirected to _build.
        assert seen["ws"] == str(tmp_path.resolve())
        assert seen["output"] == str(
            tmp_path.resolve() / "_build" / "default" / "theory" / "use.vo"
        )
        assert (tmp_path / "_build" / "default" / "theory").is_dir()

    def test_vos_mode_skips_dune_uses_compiler_into_build(self, tmp_path, monkeypatch):
        import rocq_mcp.compile as _compile

        _make_dune_project(tmp_path)
        seen = {"dune": False}

        def fake_dune(*a, **k):
            seen["dune"] = True
            return _dune_ok()

        def fake_compiler(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen["mode"] = mode
            seen["output"] = output
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_dune_build", fake_dune)
        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)

        result = run_compile_file("theory/use.v", str(tmp_path), 60, mode="vos")
        assert result["success"] is True
        assert seen["dune"] is False  # dune has no .vos target
        assert seen["mode"] == "vos"
        assert seen["output"].endswith("/_build/default/theory/use.vos")
        assert "dune_build_warning" not in result

    def test_disabled_uses_source_tree_compiler(self, tmp_path, monkeypatch):
        import rocq_mcp.compile as _compile
        import rocq_mcp.server as _server

        _make_dune_project(tmp_path)
        monkeypatch.setattr(_server, "_DUNE_BUILD_ENABLED", False)
        seen = {}

        def fake_compiler(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen["ws"] = ws
            seen["output"] = output
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)
        monkeypatch.setattr(
            _compile,
            "_run_dune_build",
            lambda *a, **k: (_ for _ in ()).throw(
                AssertionError("dune must not run when disabled")
            ),
        )

        result = run_compile_file("theory/use.v", str(tmp_path), 60)
        assert result["success"] is True
        assert seen["output"] is None  # legacy source-tree placement
        assert seen["ws"] == str(tmp_path)

    def test_non_dune_workspace_unaffected(self, tmp_path, monkeypatch):
        import rocq_mcp.compile as _compile

        # No dune-project marker -> plain rocq c, output=None.
        (tmp_path / "solo.v").write_text("Lemma l : 0 = 0.\nProof. reflexivity. Qed.\n")
        seen = {}

        def fake_compiler(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen["output"] = output
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)
        result = run_compile_file("solo.v", str(tmp_path), 60)
        assert result["success"] is True
        assert seen["output"] is None

    def test_clear_output_artifacts_removes_readonly(self, tmp_path):
        """rocq c -o target artifacts (incl. read-only dune ones) are cleared.

        Full mode clears the whole family rocq c regenerates; vos mode clears
        only the .vos so dune's tracked .vo is not orphaned (digest-db desync).
        """
        import os
        import stat
        import rocq_mcp.compile as _compile

        family = ("use.vo", "use.vok", "use.vos", "use.glob", ".use.aux")

        def seed(d):
            d.mkdir(parents=True, exist_ok=True)
            for name in family:
                p = d / name
                p.write_text("x")
                os.chmod(p, stat.S_IRUSR)  # dune-style read-only

        # full: clears the whole family (all recreated by a full rocq c compile).
        d = tmp_path / "full" / "theory"
        seed(d)
        _compile._clear_output_artifacts(d / "use.vo", "full")
        for name in family:
            assert not (d / name).exists(), f"full: {name} should be cleared"
        _compile._clear_output_artifacts(d / "use.vo", "full")  # idempotent

        # vos: clears ONLY the .vos; dune's .vo/.vok/.glob/.aux stay put
        # (rocq c -vos won't recreate them — deleting would desync dune).
        d2 = tmp_path / "vos" / "theory"
        seed(d2)
        _compile._clear_output_artifacts(d2 / "use.vos", "vos")
        assert not (d2 / "use.vos").exists(), "vos: .vos should be cleared"
        for name in ("use.vo", "use.vok", "use.glob", ".use.aux"):
            assert (d2 / name).exists(), f"vos: {name} must be preserved"

    def test_dependency_error_surfaced_without_positions(self, tmp_path, monkeypatch):
        """A dune failure located in a *dependency* surfaces raw, no positions.

        dune build compiles the whole closure; an error in dep.v must not be
        rendered against the requested file's source (wrong caret / bogus
        error_positions that would send an agent to the wrong line).
        """
        import rocq_mcp.compile as _compile

        _make_dune_project(tmp_path)
        # Error names theory/dep.v, NOT the requested theory/use.v.
        dep_err = (
            'File "./theory/dep.v", line 5, characters 0-10:\n'
            "Error: The reference bogus was not found in the current environment.\n"
        )

        def fake_dune(dune_root, target, timeout):
            return {
                "returncode": 1,
                "stdout": "",
                "stderr": dep_err,
                "timed_out": False,
                "rule_missing": False,
            }

        def fake_compiler(*a, **k):  # must not run — dune owns the outcome
            raise AssertionError("rocq c must not be invoked for a dune dep error")

        monkeypatch.setattr(_compile, "_run_dune_build", fake_dune)
        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)

        result = run_compile_file("theory/use.v", str(tmp_path), 60)
        assert result["success"] is False
        assert result["reason"] == "compile_error"
        assert "dep.v" in result["error"]  # dune's raw output names the dep
        assert "error_positions" not in result  # not misattributed to use.v
        assert "dependency" in result.get("hint", "")

    def test_mkdir_failure_falls_back_to_source_tree(self, tmp_path, monkeypatch):
        """If staging _build fails, fall back to source-tree rocq c and drop the warning."""
        from pathlib import Path
        import rocq_mcp.compile as _compile

        _make_dune_project(tmp_path)

        def fake_dune(dune_root, target, timeout):
            # rule_missing sets a warning that the OSError arm must reset.
            return {
                "returncode": 1,
                "stdout": "",
                "stderr": "Error: Don't know how to build theory/use.vo\n",
                "timed_out": False,
                "rule_missing": True,
            }

        def boom(self, *a, **k):
            raise OSError("cannot create _build")

        seen = {}

        def fake_compiler(
            fp, ws, to, keep_vo=False, mode="full", *, timing=False, output=None
        ):
            seen["ws"] = ws
            seen["output"] = output
            return _fake_compiler_result("", returncode=0)

        monkeypatch.setattr(_compile, "_run_dune_build", fake_dune)
        monkeypatch.setattr(Path, "mkdir", boom)
        monkeypatch.setattr(_compile, "_run_compiler_file", fake_compiler)

        result = run_compile_file("theory/use.v", str(tmp_path), 60)
        assert result["success"] is True
        # Fell back to a plain source-tree compile (no _build redirect).
        assert seen["output"] is None
        assert seen["ws"] == str(tmp_path)
        # The rule-missing warning was reset — we did not redirect to _build.
        assert "dune_build_warning" not in result

    @pytest.mark.skipif(not COMPILER_AVAILABLE, reason="rocq c not available")
    def test_vos_fallback_preserves_dune_vo(self, tmp_path):
        """Real dune+rocq c: a vos-mode fallback must not orphan dune's .vo.

        Regression for the digest-db desync: clearing the .vo (which rocq c
        -vos never recreates) would leave dune believing it still exists and
        refusing to rebuild it. End-to-end: dune's .vo survives and a later
        dune build still succeeds.
        """
        import shutil
        import subprocess

        if not shutil.which("dune"):
            pytest.skip("dune not available")
        _make_dune_project(tmp_path)
        r = subprocess.run(
            ["dune", "build", "theory/use.vo"], cwd=tmp_path, capture_output=True
        )
        assert r.returncode == 0, r.stderr
        vo = tmp_path / "_build" / "default" / "theory" / "use.vo"
        assert vo.is_file()

        # vos has no dune target -> rocq c -o fallback into _build/default.
        result = run_compile_file("theory/use.v", str(tmp_path), 60, mode="vos")
        assert result["success"] is True, result
        assert vo.is_file(), "vos fallback must not delete dune's .vo"
        assert (tmp_path / "_build" / "default" / "theory" / "use.vos").is_file()
        # Source tree stays clean; a later dune build still works.
        assert not (tmp_path / "theory" / "use.vo").exists()
        r2 = subprocess.run(
            ["dune", "build", "theory/use.vo"], cwd=tmp_path, capture_output=True
        )
        assert r2.returncode == 0, r2.stderr
        assert vo.is_file()

    @pytest.mark.skipif(not COMPILER_AVAILABLE, reason="rocq c not available")
    def test_timing_fallback_over_readonly_build(self, tmp_path):
        """Real dune+rocq c: timing fallback overwrites read-only _build artifacts
        (via _clear_output_artifacts on the happy path) and leaves dune buildable."""
        import shutil
        import subprocess

        if not shutil.which("dune"):
            pytest.skip("dune not available")
        _make_dune_project(tmp_path)
        r = subprocess.run(
            ["dune", "build", "theory/use.vo"], cwd=tmp_path, capture_output=True
        )
        assert r.returncode == 0, r.stderr
        vo = tmp_path / "_build" / "default" / "theory" / "use.vo"

        # timing forces the rocq c -o fallback even for an in-stanza file whose
        # _build/.vo is present and read-only.
        result = run_compile_file("theory/use.v", str(tmp_path), 60, timing=True)
        assert result["success"] is True, result
        assert "timing" in result
        assert vo.is_file()
        assert not (tmp_path / "theory" / "use.vo").exists()  # source tree clean
        r2 = subprocess.run(
            ["dune", "build", "theory/use.vo"], cwd=tmp_path, capture_output=True
        )
        assert r2.returncode == 0, r2.stderr
