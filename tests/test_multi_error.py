"""Integration tests for the multi-error rocq_compile_file response.

The new ``errors`` field on a failed ``rocq_compile_file`` response
carries per-proof error entries produced by
``rocq_mcp.proof_walk.collect_file_errors`` and wired in by
``compile_enrichment.run_compile_file_with_state``.  Each entry has the
shape::

    {
        "proof_name": str | None,
        "kind": str,
        "start_line": int,
        "end_line": int,
        "code": int,
        "message": str,
    }

The feature is gated by:

* ``ROCQ_COMPILE_MULTI_ERROR_CAP`` (int, default 20; ``0`` disables).
* ``ROCQ_COMPILE_MULTI_ERROR_TIMEOUT`` (float, default 5.0).

The ``errors`` key is present only on ``reason == "compile_error"``
failures when a ``lifespan_state`` is supplied (pet available).

Most tests require a live coqc + pet on PATH and skip otherwise;
the file itself must import cleanly without rocq.
"""

from __future__ import annotations

from collections import deque

import pytest

from tests.conftest import (
    COQC_AVAILABLE,
    PET_AVAILABLE,
    _MockContext,
    make_lifespan_state,
)

pytestmark = pytest.mark.skipif(
    not (COQC_AVAILABLE and PET_AVAILABLE),
    reason="multi-error tests require coqc + pet on PATH",
)


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


_REQUIRED_KEYS = {
    "proof_name",
    "kind",
    "start_line",
    "end_line",
    "code",
    "message",
}

_VALID_CODES = {-32003, -32006}


def _fresh_lifespan_state():
    """Build a full lifespan state with a real recent_errors deque."""
    state = make_lifespan_state(pet_timeout=30.0)
    state["recent_errors"] = deque(maxlen=10)
    return state


def _invalidate(state):
    from rocq_mcp.server import _invalidate_pet

    _invalidate_pet(state)


# ---------------------------------------------------------------------------
# TestMultiErrorBasic
# ---------------------------------------------------------------------------


class TestMultiErrorBasic:
    """Smoke tests for the core single-file behaviour."""

    async def test_clean_file_no_errors_field(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "clean_no_errors.v"
        path.write_text("Theorem ok : True. Proof. exact I. Qed.\n")

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="clean_no_errors.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is True
        assert "errors" not in result

    async def test_single_proof_error_yields_one_entry(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "single_broken.v"
        path.write_text("Theorem broken : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="single_broken.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert result.get("reason") == "compile_error"
        assert "errors" in result
        assert isinstance(result["errors"], list)
        assert len(result["errors"]) == 1

        entry = result["errors"][0]
        assert entry["proof_name"] == "broken"
        assert entry["kind"] == "Theorem"
        assert isinstance(entry["start_line"], int)
        assert isinstance(entry["end_line"], int)
        assert entry["start_line"] <= entry["end_line"]
        # Proof body spans lines 0..3 in our 4-line file.
        assert 0 <= entry["start_line"] <= 3
        assert 0 <= entry["end_line"] <= 3

    async def test_cascade_within_one_proof_deduplicates(self, workspace):
        """A proof with several broken tactics must yield exactly one entry."""
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "cascade.v"
        path.write_text(
            "Theorem cascade_broken : True.\n"
            "Proof.\n"
            "  exact 0.\n"
            "  exact 1.\n"
            "  exact 2.\n"
            "  exact 3.\n"
            "  exact 4.\n"
            "Qed.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="cascade.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        # Per-proof deduplication: 5 broken tactics in one proof should
        # collapse to a single error entry for the enclosing proof.
        cascade_entries = [
            e for e in result["errors"] if e.get("proof_name") == "cascade_broken"
        ]
        assert len(cascade_entries) == 1


# ---------------------------------------------------------------------------
# TestMultiErrorAcrossProofs
# ---------------------------------------------------------------------------


class TestMultiErrorAcrossProofs:
    """Multiple independent error sites must each surface."""

    async def test_two_independent_broken_proofs(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "two_broken.v"
        path.write_text(
            "Theorem foo : True.\n"
            "Proof.\n"
            "  exact 0.\n"
            "Qed.\n"
            "\n"
            "Theorem bar : True.\n"
            "Proof.\n"
            "  exact 1.\n"
            "Qed.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="two_broken.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        names = {e.get("proof_name") for e in result["errors"]}
        assert "foo" in names
        assert "bar" in names
        # Per-proof entries — at least one for each broken theorem.
        assert len(result["errors"]) >= 2

    async def test_clean_proofs_interleaved_with_broken(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        # 5 theorems; 3rd (t3) and 5th (t5) broken.
        path = workspace / "interleaved.v"
        path.write_text(
            "Theorem t1 : True. Proof. exact I. Qed.\n"
            "Theorem t2 : True. Proof. exact I. Qed.\n"
            "Theorem t3 : True. Proof. exact 0. Qed.\n"
            "Theorem t4 : True. Proof. exact I. Qed.\n"
            "Theorem t5 : True. Proof. exact 0. Qed.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="interleaved.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        broken_names = {
            e.get("proof_name")
            for e in result["errors"]
            if e.get("proof_name") in {"t1", "t2", "t3", "t4", "t5"}
        }
        assert "t3" in broken_names
        assert "t5" in broken_names
        # Clean proofs must not appear in the error list.
        assert "t1" not in broken_names
        assert "t2" not in broken_names
        assert "t4" not in broken_names

    async def test_broken_require_after_first_proof(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "broken_require.v"
        path.write_text(
            "Theorem foo : True. Proof. exact I. Qed.\n"
            "Require Import nonexistent_module.\n"
            "Theorem bar : True. Proof. exact I. Qed.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="broken_require.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        # A top-level (inter-chunk) error must surface — proof_name=None.
        top_levels = [e for e in result["errors"] if e.get("proof_name") is None]
        assert len(top_levels) >= 1


# ---------------------------------------------------------------------------
# TestMultiErrorCoverage
# ---------------------------------------------------------------------------


class TestMultiErrorCoverage:
    """Per-kind coverage: Instance / Program Definition / Definition."""

    async def test_instance_record_syntax(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "instance_record.v"
        path.write_text(
            "Class Foo := { foo_field : nat }.\n"
            "Instance bad_inst : Foo := { foo_field := true }.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="instance_record.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        instance_entries = [
            e for e in result["errors"] if e.get("proof_name") == "bad_inst"
        ]
        assert len(instance_entries) >= 1
        assert instance_entries[0]["kind"] == "Instance"

    async def test_instance_tactic_syntax(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "instance_tactic.v"
        path.write_text(
            "Class Foo := { foo_field : nat }.\n"
            "Instance bad_inst_t : Foo.\n"
            "Proof.\n"
            "  exact 0.\n"
            "Defined.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="instance_tactic.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        instance_entries = [
            e for e in result["errors"] if e.get("proof_name") == "bad_inst_t"
        ]
        assert len(instance_entries) >= 1

    async def test_program_definition_next_obligation(self, workspace):
        """Program Definition + broken Next Obligation must be caught.

        This is the case the friend's coq-lsp fork addressed; rocq-mcp's
        proof_walk must surface it without needing a fork.
        """
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "program_def.v"
        path.write_text(
            "From Coq Require Import Program.\n"
            "Program Definition pdef : { n : nat | n > 0 } := 0.\n"
            "Next Obligation.\n"
            "  exact 0.\n"
            "Qed.\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="program_def.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        # The Program Definition or one of its Next Obligations must surface.
        pdef_entries = [
            e
            for e in result["errors"]
            if e.get("proof_name") == "pdef"
            or (e.get("proof_name") or "").startswith("pdef")
        ]
        assert len(pdef_entries) >= 1

    async def test_definition_term_form_type_error(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "definition_term.v"
        path.write_text("Definition foo : nat := true.\n")

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="definition_term.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        # The error may be attributed to "foo" (Definition kind) or to the
        # top-level chunk depending on the walker's toc handling — both
        # are valid as long as the error is surfaced.
        assert len(result["errors"]) >= 1


# ---------------------------------------------------------------------------
# TestMultiErrorCap
# ---------------------------------------------------------------------------


class TestMultiErrorCap:
    """``ROCQ_COMPILE_MULTI_ERROR_CAP`` truncates / disables the feature."""

    async def test_max_errors_cap_truncates(self, workspace, monkeypatch):
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        # Build 30 broken theorems; cap to 5.
        lines = [f"Theorem t{i} : True. Proof. exact {i}. Qed." for i in range(30)]
        path = workspace / "many_broken.v"
        path.write_text("\n".join(lines) + "\n")

        monkeypatch.setenv("ROCQ_COMPILE_MULTI_ERROR_CAP", "5")
        # Also bump the module attribute if the implementation read it at
        # import time.  Use ``raising=False`` so this test still runs
        # before the implementation worktree is merged.
        monkeypatch.setattr(
            _server,
            "_COMPILE_MULTI_ERROR_CAP",
            5,
            raising=False,
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="many_broken.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        assert len(result["errors"]) == 5

    async def test_cap_zero_disables_feature(self, workspace, monkeypatch):
        import rocq_mcp.server as _server
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "disabled.v"
        path.write_text("Theorem broken : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")

        monkeypatch.setenv("ROCQ_COMPILE_MULTI_ERROR_CAP", "0")
        monkeypatch.setattr(
            _server,
            "_COMPILE_MULTI_ERROR_CAP",
            0,
            raising=False,
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="disabled.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" not in result


# ---------------------------------------------------------------------------
# TestMultiErrorFallback
# ---------------------------------------------------------------------------


class TestMultiErrorFallback:
    """Pet-unavailable and unparseable-file fallbacks."""

    async def test_response_when_pet_unavailable(self, workspace):
        """No lifespan_state -> no enrichment, today's behaviour preserved.

        ``ctx=None`` makes ``rocq_compile_file`` route through with
        ``lifespan_state=None``; the wrapper must NOT attach an
        ``errors`` field in that case.
        """
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "no_pet.v"
        path.write_text("Theorem broken : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")

        result = await rocq_compile_file(
            file="no_pet.v",
            workspace=str(workspace),
            ctx=None,
        )

        assert result["success"] is False
        assert "errors" not in result

    async def test_empty_errors_when_walker_finds_nothing(self, workspace, monkeypatch):
        """``errors`` may be present and empty when the walker ran but pet
        did not reproduce the coqc failure.

        Construct this by stubbing ``collect_file_errors`` to return an empty
        list — exercises the contract edge that the README and docstring
        explicitly call out ("treat as 'no additional errors found' rather
        than 'no errors at all'").
        """
        from rocq_mcp import compile_enrichment as _ce
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "empty_walker.v"
        path.write_text("Theorem broken : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")

        monkeypatch.setattr(_ce, "collect_file_errors", lambda **kw: [])

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="empty_walker.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        assert result["errors"] == []

    async def test_toc_failure_fallback(self, workspace):
        """An unparseable file: either some errors surface (fallback to
        whole-file chunk) or no ``errors`` key is attached.  Both are
        contract-conforming."""
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "garbage.v"
        path.write_text(
            "this is not valid Coq source at all $$$ %%% &&&\n"
            "completely unparseable rubbish\n"
        )

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="garbage.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        # Either: walker fell back to a whole-file chunk and surfaced
        # something; or: walker returned None and no key is attached.
        if "errors" in result:
            assert isinstance(result["errors"], list)


# ---------------------------------------------------------------------------
# TestMultiErrorEnvelopeContract
# ---------------------------------------------------------------------------


class TestMultiErrorEnvelopeContract:
    """Envelope-level shape and interaction with existing fields."""

    async def test_errors_field_shape(self, workspace):
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "envelope.v"
        path.write_text("Theorem broken : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="envelope.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        assert "errors" in result
        assert isinstance(result["errors"], list)
        for entry in result["errors"]:
            assert isinstance(entry, dict)
            assert _REQUIRED_KEYS <= set(entry.keys())
            assert entry["proof_name"] is None or isinstance(entry["proof_name"], str)
            assert isinstance(entry["kind"], str)
            assert isinstance(entry["start_line"], int)
            assert isinstance(entry["end_line"], int)
            assert entry["start_line"] >= 0
            assert entry["end_line"] >= entry["start_line"]
            assert isinstance(entry["code"], int)
            assert entry["code"] in _VALID_CODES
            assert isinstance(entry["message"], str)

    async def test_errors_only_on_compile_error_reason(self, workspace):
        """Validation failures (e.g. forbidden command) must not carry an
        ``errors`` field — the feature is gated on
        ``reason == "compile_error"``."""
        from rocq_mcp.server import rocq_compile_file

        # Forbidden command (Drop) triggers a validation reason before
        # coqc ever runs.
        path = workspace / "forbidden.v"
        path.write_text("Drop.\n")

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="forbidden.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        # Forbidden / validation reasons must not get the errors[] field.
        if result.get("reason") != "compile_error":
            assert "errors" not in result

    async def test_existing_state_capture_unchanged(self, workspace):
        """``state_capture_status`` / ``state_id`` / ``goals`` / ``theorem``
        must still work alongside the new ``errors`` field."""
        from rocq_mcp.server import rocq_compile_file

        path = workspace / "coexist.v"
        path.write_text("Theorem broken : True.\n" "Proof.\n" "  exact 0.\n" "Qed.\n")

        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        try:
            result = await rocq_compile_file(
                file="coexist.v",
                workspace=str(workspace),
                ctx=ctx,
            )
        finally:
            _invalidate(ls)

        assert result["success"] is False
        # Existing fields preserved.
        assert "state_capture_status" in result
        assert "error_positions" in result
        # On a successful state capture, the existing fields populate
        # exactly as before.
        if result["state_capture_status"] == "ok":
            assert isinstance(result.get("state_id"), int)
            assert "goals" in result
            assert "theorem" in result
        # ... and the new errors field coexists with them.
        assert "errors" in result
