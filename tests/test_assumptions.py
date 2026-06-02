"""Tests for the rocq_assumptions tool (run_assumptions).

These tests mock run_query to avoid needing pet — they test result
formatting and the available_in_file enrichment.  rocq_assumptions
is pure introspection (no classification); the verdict / classification
fields live on rocq_verify.
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
    async def test_classical_axiom_returned_verbatim(self):
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
        assert len(result["assumptions"]) == 1
        assert "Coq.Logic.Classical_Prop.classic" in result["assumptions"][0]

    @pytest.mark.asyncio
    async def test_user_axiom_returned_verbatim(self):
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
        assert any("my_custom_axiom" in a for a in result["assumptions"])

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
    async def test_mixed_axioms_returned_verbatim(self):
        """All assumptions appear in the same flat list — no classification."""
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
        joined = "\n".join(result["assumptions"])
        assert "Coq.Logic.Classical_Prop.classic" in joined
        assert "my_custom_axiom" in joined
        # No classification fields anywhere on the response.
        for legacy_key in (
            "verdict",
            "admitted",
            "classical_axioms",
            "user_axioms",
            "standard_assumptions",
        ):
            assert legacy_key not in result

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
        """If the raw assumptions parser raises, return error with the
        unified envelope (success/error/reason) and round-trip the
        failure into recent_errors so rocq_diag surfaces it."""
        from collections import deque

        self._query_result = {
            "success": True,
            "output": "some unparseable garbage",
        }
        import rocq_mcp.verify as _verify

        def _bad_parse(*args, **kwargs):
            raise ValueError("parse failed")

        monkeypatch.setattr(_verify, "_parse_assumptions_raw", _bad_parse)

        ls = {"recent_errors": deque(maxlen=10)}
        result = await run_assumptions(
            name="thm",
            file="test.v",
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert result["reason"] == "crashed"
        assert "parse" in result["error"].lower()
        assert "raw_output" in result
        # The same reason must reach recent_errors.
        recorded = [
            e
            for e in ls["recent_errors"]
            if e.get("tool") == "rocq_assumptions" and e.get("reason") == "crashed"
        ]
        assert len(recorded) == 1

    @pytest.mark.asyncio
    async def test_no_classification_fields_on_success(self):
        """Confirm rocq_assumptions never emits classifier fields — this is
        introspection, not a trust decision (rocq_verify owns that)."""
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        r = await run_assumptions(
            name="thm", file="test.v", workspace="/tmp", lifespan_state={}
        )
        for legacy_key in (
            "verdict",
            "admitted",
            "classical_axioms",
            "user_axioms",
            "standard_assumptions",
        ):
            assert legacy_key not in r

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


from tests.conftest import make_lifespan_state as _make_lifespan_state  # noqa: E402


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
        assert result["assumptions"] == []

    @pytest.mark.asyncio
    async def test_module_child_qualified_in_available_in_file(
        self, workspace, lifespan_state
    ):
        """End-to-end: a typo'd theorem name in a file containing a Module
        must produce ``available_in_file`` with the Module-qualified form
        (``M.foo`` not bare ``foo``) so the agent can address it
        directly.  Notation entries must be filtered out — their syntax
        keys would only confuse the agent."""
        vfile = Path(workspace) / "qualified_avail.v"
        vfile.write_text(
            "Module Outer.\n"
            "  Definition shallow := 1.\n"
            "  Module Inner.\n"
            "    Theorem deep : True.\n"
            "    Proof. exact I. Qed.\n"
            "  End Inner.\n"
            "End Outer.\n"
            'Notation "x +! y" := (x + y) (at level 50).\n'
            "Definition top := 0.\n"
        )
        # Ask for a typo to trigger the available_in_file enrichment path.
        result = await run_assumptions(
            name="depe",  # typo for Outer.Inner.deep
            file="qualified_avail.v",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
        )
        assert result["success"] is False
        names = set(result.get("available_in_file", []))
        # Module children carry the full path; bare top-level definition
        # stays bare; the Notation entry is filtered out.
        assert "Outer.Inner.deep" in names
        assert "Outer.shallow" in names
        assert "top" in names
        assert "deep" not in names  # bare form must NOT appear
        assert "shallow" not in names
        assert "x +! y" not in names


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
        from tests.conftest import _MockContext

        mock_ctx = _MockContext({})
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
        from tests.conftest import _MockContext
        import rocq_mcp.server as _server

        captured = {}

        async def mock_run_assumptions(**kwargs):
            captured.update(kwargs)
            return {"success": True, "theorem": "my_thm", "assumptions": []}

        monkeypatch.setattr(_server, "run_assumptions", mock_run_assumptions)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        mock_ctx = _MockContext({"pet_client": None})

        await rocq_assumptions(
            name="my_thm",
            file="proof.v",
            workspace=str(tmp_path),
            ctx=mock_ctx,
        )

        assert captured["name"] == "my_thm"
        assert captured["file"] == "proof.v"
        assert captured["lifespan_state"] is mock_ctx.lifespan_context

    @pytest.mark.asyncio
    async def test_timeout_above_cap_clamped_with_signal(self, monkeypatch, tmp_path):
        """Wrapper clamps an over-cap timeout and echoes ``clamped_timeout``."""
        from rocq_mcp.server import rocq_assumptions
        from tests.conftest import _MockContext
        import rocq_mcp.server as _server

        captured: dict = {}

        async def mock_run_assumptions(**kwargs):
            captured.update(kwargs)
            return {"success": True, "theorem": "my_thm", "assumptions": []}

        monkeypatch.setattr(_server, "run_assumptions", mock_run_assumptions)
        monkeypatch.setattr(_server, "_validate_workspace", lambda ws: None)

        mock_ctx = _MockContext({"pet_client": None})

        result = await rocq_assumptions(
            name="my_thm",
            file="proof.v",
            workspace=str(tmp_path),
            timeout=5000,
            ctx=mock_ctx,
        )

        assert result["clamped_timeout"] == _server.ROCQ_QUERY_TIMEOUT_CAP
        assert captured["timeout"] == float(_server.ROCQ_QUERY_TIMEOUT_CAP)


# ---------------------------------------------------------------------------
# Tests for ``available_in_file`` enrichment on rocq_assumptions failures.
# ---------------------------------------------------------------------------


class TestAssumptionsAvailableInFile:
    """When run_query fails (e.g. theorem not found), run_assumptions should
    attach ``available_in_file`` populated by the cached pet.toc lookup.

    These tests mock both ``run_query`` and ``_fetch_available_in_file`` so
    they don't need a real pet.
    """

    @pytest.mark.asyncio
    async def test_failure_attaches_available_in_file(self, monkeypatch):
        """A failed run_query response must be augmented with the
        capped name list returned by ``_fetch_available_in_file``."""
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {"success": False, "error": "Reference foo not found."}

        async def mock_fetch_available(**kwargs):
            return _int._AvailableInFile(["alpha", "foo_bar", "zeta"], False, 3)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        result = await run_assumptions(
            name="foo",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )

        assert result["success"] is False
        assert result["available_in_file"] == ["alpha", "foo_bar", "zeta"]
        assert "available_in_file_truncated" not in result
        assert "available_in_file_total" not in result
        assert "available_in_file_limit" not in result

    @pytest.mark.asyncio
    async def test_failure_attaches_truncation_marker_when_over_limit(
        self, monkeypatch
    ):
        """When the helper signals truncation, marker fields propagate
        — including ``available_in_file_limit`` which surfaces the
        active cap so the agent never has to guess it.
        """
        import rocq_mcp.interactive as _int
        from rocq_mcp.interactive import _DEFAULT_TOC_LIMIT

        async def mock_run_query(**kwargs):
            return {"success": False, "error": "Reference foo not found."}

        async def mock_fetch_available(**kwargs):
            return _int._AvailableInFile(["a", "b", "c"], True, 1234)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        result = await run_assumptions(
            name="foo",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )

        assert result["success"] is False
        assert result["available_in_file"] == ["a", "b", "c"]
        assert result["available_in_file_truncated"] is True
        assert result["available_in_file_total"] == 1234
        assert result["available_in_file_limit"] == _DEFAULT_TOC_LIMIT
        # Sanity: the value matches the documented cap (500) so test
        # output catches accidental cap drift.
        assert result["available_in_file_limit"] == 500

    @pytest.mark.asyncio
    async def test_failure_skips_field_when_helper_returns_empty(self, monkeypatch):
        """No symbols → no field; the failure response is otherwise unchanged."""
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {"success": False, "error": "Reference foo not found."}

        async def mock_fetch_available(**kwargs):
            return _int._AvailableInFile([], False, 0)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        result = await run_assumptions(
            name="foo",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )

        assert result["success"] is False
        assert "available_in_file" not in result
        assert "available_in_file_truncated" not in result
        assert "available_in_file_total" not in result

    @pytest.mark.asyncio
    async def test_success_does_not_attach_field(self, monkeypatch):
        """Success path is untouched — ``available_in_file`` only on failures."""
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {"success": True, "output": "Closed under the global context"}

        called = {"count": 0}

        async def mock_fetch_available(**kwargs):
            called["count"] += 1
            return _int._AvailableInFile(["something"], False, 1)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        result = await run_assumptions(
            name="thm",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )

        assert result["success"] is True
        assert "available_in_file" not in result
        assert called["count"] == 0

    @pytest.mark.asyncio
    @pytest.mark.parametrize(
        "transport_reason",
        ["timeout", "memory_exhausted", "lock_contended", "unavailable"],
    )
    async def test_transport_failure_skips_enrichment(
        self, monkeypatch, transport_reason
    ):
        """Pet-transport failures must NOT trigger the extra ``pet.toc``
        call — the pet is already stressed/dead, so hammering it with a
        speculative enrichment wastes resources.
        """
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {
                "success": False,
                "error": "Pet timed out / lock contended / OOM.",
                "reason": transport_reason,
            }

        called = {"count": 0}

        async def mock_fetch_available(**kwargs):
            called["count"] += 1
            return _int._AvailableInFile(["should_not_appear"], False, 1)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        result = await run_assumptions(
            name="foo",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )

        assert result["success"] is False
        assert result["reason"] == transport_reason
        # Crucially: no enrichment fields, no extra pet call.
        assert "available_in_file" not in result
        assert called["count"] == 0

    @pytest.mark.asyncio
    async def test_pet_restarted_crashed_skips_enrichment(self, monkeypatch):
        """``reason="crashed"`` *with* ``pet_restarted: True`` means the
        pet process actually died — skip the extra ``pet.toc`` call.
        (A bare ``reason="crashed"`` without ``pet_restarted`` is a live
        Coq error — typo recovery — and DOES trigger enrichment; that
        path is covered by ``test_typo_failure_records_not_found_reason``.)
        """
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {
                "success": False,
                "error": "Pet process died.",
                "reason": "crashed",
                "pet_restarted": True,
            }

        called = {"count": 0}

        async def mock_fetch_available(**kwargs):
            called["count"] += 1
            return _int._AvailableInFile(["should_not_appear"], False, 1)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        result = await run_assumptions(
            name="foo",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )

        assert result["success"] is False
        assert result["reason"] == "crashed"
        assert result["pet_restarted"] is True
        assert "available_in_file" not in result
        assert called["count"] == 0

    @pytest.mark.asyncio
    async def test_typo_failure_records_not_found_reason(self, monkeypatch):
        """When ``run_query`` failed on a typo'd theorem name (the file
        IS valid, the name is not), ``run_assumptions`` must override
        the propagated reason to ``"not_found"`` AND record a
        ``rocq_diag``-visible entry under that reason.  Otherwise the
        diagnostic buffer mis-attributes the error to ``"crashed"``
        (the generic reason ``_run_with_pet`` sets on Coq errors).
        """
        from collections import deque
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {
                "success": False,
                "error": "Reference fool_bound not found.",
                "reason": "crashed",
            }

        async def mock_fetch_available(**kwargs):
            return _int._AvailableInFile(["alpha", "fuel_bound", "zeta"], False, 3)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        recent_errors: deque = deque(maxlen=10)
        lifespan_state = {"recent_errors": recent_errors}

        result = await run_assumptions(
            name="fool_bound",
            file="test.v",
            workspace="/tmp",
            lifespan_state=lifespan_state,
        )

        assert result["success"] is False
        # Reason was overridden from "crashed" to "not_found".
        assert result["reason"] == "not_found"
        assert result["available_in_file"] == ["alpha", "fuel_bound", "zeta"]

        # rocq_diag would see a not_found entry tagged ``rocq_assumptions``.
        not_found_entries = [
            e
            for e in recent_errors
            if e.get("tool") == "rocq_assumptions" and e.get("reason") == "not_found"
        ]
        assert len(not_found_entries) == 1
        assert "fool_bound" in not_found_entries[0]["message"]

    @pytest.mark.asyncio
    async def test_typo_failure_drops_prior_rocq_query_crashed_entry(self, monkeypatch):
        """When the not_found re-tag fires, the rocq_query/crashed entry
        that ``_run_with_pet`` recorded for the underlying live
        PetanqueError must be dropped — otherwise rocq_diag reports the
        same failure twice with conflicting attribution
        (``rocq_query/crashed`` AND ``rocq_assumptions/not_found``)."""
        from collections import deque
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            # Simulate the buffer state after _run_with_pet has recorded
            # the live PetanqueError as rocq_query/crashed (the real flow
            # is run_assumptions -> run_query -> _run_with_pet -> _record_error).
            kwargs["lifespan_state"]["recent_errors"].append(
                {
                    "tool": "rocq_query",
                    "message": "Reference fool_bound not found.",
                    "reason": "crashed",
                    "occurred_at": 0.0,
                }
            )
            return {
                "success": False,
                "error": "Reference fool_bound not found.",
                "reason": "crashed",
            }

        async def mock_fetch_available(**kwargs):
            return _int._AvailableInFile(["fuel_bound"], False, 1)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        recent_errors: deque = deque(maxlen=10)
        lifespan_state = {"recent_errors": recent_errors}

        await run_assumptions(
            name="fool_bound",
            file="test.v",
            workspace="/tmp",
            lifespan_state=lifespan_state,
        )

        # Buffer must contain exactly ONE entry — the re-tagged
        # rocq_assumptions/not_found.  The original rocq_query/crashed
        # was dropped.
        assert len(recent_errors) == 1
        only = recent_errors[0]
        assert only["tool"] == "rocq_assumptions"
        assert only["reason"] == "not_found"

    @pytest.mark.asyncio
    async def test_typo_failure_no_double_record_when_reason_already_not_found(
        self, monkeypatch
    ):
        """If a future caller already set ``reason="not_found"`` (e.g.
        run_query learned to do its own classification), we must NOT
        double-record into the recent_errors buffer.  Idempotency check.
        """
        from collections import deque
        import rocq_mcp.interactive as _int

        async def mock_run_query(**kwargs):
            return {
                "success": False,
                "error": "Reference foo not found.",
                "reason": "not_found",
            }

        async def mock_fetch_available(**kwargs):
            return _int._AvailableInFile(["alpha", "foo_bar"], False, 2)

        monkeypatch.setattr(_int, "run_query", mock_run_query)
        monkeypatch.setattr(_int, "_fetch_available_in_file", mock_fetch_available)

        recent_errors: deque = deque(maxlen=10)
        lifespan_state = {"recent_errors": recent_errors}

        result = await run_assumptions(
            name="foo",
            file="test.v",
            workspace="/tmp",
            lifespan_state=lifespan_state,
        )

        assert result["reason"] == "not_found"
        # No spurious extra record because reason was already "not_found".
        not_found_entries = [
            e
            for e in recent_errors
            if e.get("tool") == "rocq_assumptions" and e.get("reason") == "not_found"
        ]
        assert len(not_found_entries) == 0


# ---------------------------------------------------------------------------
# Tests for ``_collect_toc_names`` (pure helper, no pet).
# ---------------------------------------------------------------------------


class TestCollectTocNames:
    def test_empty_toc(self):
        from rocq_mcp.interactive import _collect_toc_names

        assert _collect_toc_names([]) == []
        assert _collect_toc_names(None) == []

    def test_flattens_nested_children(self):
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, children=None):
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Theorem",
                kind=0,
                range=None,
                children=children,
            )

        toc = [
            (
                "main",
                [
                    _e("a"),
                    _e("b", children=[_e("b_inner1"), _e("b_inner2")]),
                    _e("c"),
                ],
            )
        ]
        names = _collect_toc_names(toc)
        assert set(names) == {"a", "b", "b_inner1", "b_inner2", "c"}

    def test_skips_unnamed_but_recurses(self):
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        unnamed = SimpleNamespace(
            name=None,
            detail="Section",
            kind=0,
            range=None,
            children=[
                SimpleNamespace(
                    name=SimpleNamespace(v="inner"),
                    detail="Theorem",
                    kind=0,
                    range=None,
                    children=None,
                )
            ],
        )
        names = _collect_toc_names([("main", [unnamed])])
        assert names == ["inner"]

    def test_filters_notation_entries(self):
        """Notation/Infix entries have syntax keys (`x + y`) as names —
        useless as `name=` arguments, must be dropped."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, detail):
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail=detail,
                kind=0,
                range=None,
                children=None,
            )

        toc = [
            (
                "main",
                [
                    _e("real_def", "Definition"),
                    _e("x + y", "Notation"),
                    _e("x ?? y", "Infix"),
                    _e("real_thm", "Theorem"),
                ],
            )
        ]
        names = _collect_toc_names(toc)
        assert set(names) == {"real_def", "real_thm"}

    def test_qualifies_module_children_when_source_given(self):
        """When a Rocq source is provided, definitions inside Module M get
        qualified as ``M.foo`` so the agent can address them."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Definition",
                kind=0,
                range=r,
                children=None,
            )

        # Source layout (0-based lines):
        # 0: Module Outer.
        # 1:   Module Inner.
        # 2:     Definition deep := 99.
        # 3:   End Inner.
        # 4:   Definition shallow := 1.
        # 5: End Outer.
        # 6: Definition top := 0.
        source = (
            "Module Outer.\n"
            "  Module Inner.\n"
            "    Definition deep := 99.\n"
            "  End Inner.\n"
            "  Definition shallow := 1.\n"
            "End Outer.\n"
            "Definition top := 0.\n"
        )
        toc = [
            ("deep", [_e("deep", 2)]),
            ("shallow", [_e("shallow", 4)]),
            ("top", [_e("top", 6)]),
        ]
        names = _collect_toc_names(toc, source=source)
        assert set(names) == {"Outer.Inner.deep", "Outer.shallow", "top"}

    def test_section_children_not_qualified(self):
        """Coq sections do NOT introduce a namespace qualifier — Section
        members must be emitted as bare names."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Definition",
                kind=0,
                range=r,
                children=None,
            )

        # Section S. Definition x := 1. End S.
        source = "Section S.\n  Definition x := 1.\nEnd S.\n"
        toc = [("x", [_e("x", 1)])]
        names = _collect_toc_names(toc, source=source)
        assert names == ["x"]

    def test_module_type_also_qualifies(self):
        """Module Type members are addressable as MT.foo from outside,
        so they MUST be qualified."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line, detail="Parameter"):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail=detail,
                kind=0,
                range=r,
                children=None,
            )

        # Module Type MT. Parameter p : nat. End MT.
        source = "Module Type MT.\n  Parameter p : nat.\nEnd MT.\n"
        toc = [("p", [_e("p", 1)])]
        names = _collect_toc_names(toc, source=source)
        assert names == ["MT.p"]

    def test_qualification_skips_module_open_in_comment(self):
        """A 'Module X.' inside a comment must NOT open a region — the
        comment scrubber preserves line numbers so subsequent ranges
        still align correctly."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Definition",
                kind=0,
                range=r,
                children=None,
            )

        # Line 0: comment claiming Module M.   Line 1: real def.
        # Confirms the region scanner does not treat the comment as a
        # real Module opener — `top` stays bare.
        source = "(* Module M. *)\nDefinition top := 0.\n"
        toc = [("top", [_e("top", 1)])]
        names = _collect_toc_names(toc, source=source)
        assert names == ["top"]

    def test_declarative_one_liner_does_not_corrupt_parent_qualifier(self):
        """Audit-fix #2 reproducer.  ``Module M : MT.`` is a declarative
        one-liner: it has no body and no ``End M.``.  The opener regex
        cannot distinguish it from a real opener, so it gets pushed
        onto the stack.  When ``End Outer.`` later fires, we must scan
        down the stack for the matching name (rather than checking only
        the top), or ``Outer`` is silently dropped from regions and
        ``Sibling.x`` ends up qualified bare instead of as
        ``Outer.Sibling.x``."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Definition",
                kind=0,
                range=r,
                children=None,
            )

        # 0: Module Outer.
        # 1:   Module M : MT.            (one-liner, no End)
        # 2:   Module Sibling.
        # 3:     Definition x := 1.
        # 4:   End Sibling.
        # 5: End Outer.
        source = (
            "Module Outer.\n"
            "  Module M : MT.\n"
            "  Module Sibling.\n"
            "    Definition x := 1.\n"
            "  End Sibling.\n"
            "End Outer.\n"
        )
        toc = [("x", [_e("x", 3)])]
        names = _collect_toc_names(toc, source=source)
        assert names == ["Outer.Sibling.x"]

    def test_module_assignment_one_liner_no_corruption(self):
        """Same bug class via ``Module M := SomeMod.`` (functor application
        / module aliasing).  Also has no body and no ``End``."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Definition",
                kind=0,
                range=r,
                children=None,
            )

        # 0: Module Outer.
        # 1:   Module M := SomeMod.
        # 2:   Definition y := 0.
        # 3: End Outer.
        source = (
            "Module Outer.\n"
            "  Module M := SomeMod.\n"
            "  Definition y := 0.\n"
            "End Outer.\n"
        )
        toc = [("y", [_e("y", 2)])]
        names = _collect_toc_names(toc, source=source)
        assert names == ["Outer.y"]

    def test_top_level_one_liner_does_not_break_subsequent_regions(self):
        """A declarative one-liner at the top level leaks onto the open
        stack but should not corrupt any subsequent module's qualifier."""
        from rocq_mcp.interactive import _collect_toc_names
        from types import SimpleNamespace

        def _e(name, line):
            r = SimpleNamespace(
                start=SimpleNamespace(line=line, character=0),
                end=SimpleNamespace(line=line, character=0),
            )
            return SimpleNamespace(
                name=SimpleNamespace(v=name),
                detail="Definition",
                kind=0,
                range=r,
                children=None,
            )

        # 0: Module M := SomeMod.       (one-liner, top-level, no End)
        # 1: Module Real.
        # 2:   Definition x := 1.
        # 3: End Real.
        source = (
            "Module M := SomeMod.\n"
            "Module Real.\n"
            "  Definition x := 1.\n"
            "End Real.\n"
        )
        toc = [("x", [_e("x", 2)])]
        names = _collect_toc_names(toc, source=source)
        assert names == ["Real.x"]
