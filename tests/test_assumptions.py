"""Tests for the rocq_assumptions tool (run_assumptions).

These tests mock run_query to avoid needing pet — they test the
classification and result formatting logic only.
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
        assert result["verdict"] == "closed"
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
    async def test_standard_axioms(self):
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
        assert result["verdict"] == "standard_only"
        assert len(result["assumptions"]) == 1

    @pytest.mark.asyncio
    async def test_suspicious_axiom(self):
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
        assert result["verdict"] == "suspicious"
        assert len(result["assumptions"]) >= 1

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
    async def test_mixed_axioms(self):
        """Both standard and suspicious axioms should be classified correctly."""
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
        assert result["verdict"] == "suspicious"
        # Should have suspicious assumptions
        assert len(result["assumptions"]) >= 1
        # Should also report standard assumptions
        assert "standard_assumptions" in result

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
        """If parse_and_classify_assumptions raises, return error with raw_output."""
        self._query_result = {
            "success": True,
            "output": "some unparseable garbage",
        }
        import rocq_mcp.interactive as _int

        def _bad_parse(*args, **kwargs):
            raise ValueError("parse failed")

        # Patch the local import inside run_assumptions
        import rocq_mcp.verify as _verify

        monkeypatch.setattr(_verify, "parse_and_classify_assumptions", _bad_parse)

        result = await run_assumptions(
            name="thm",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is False
        assert "parse" in result["error"].lower()
        assert "raw_output" in result

    # --- §1.6: categorized name lists on the response (additive) ---

    @pytest.mark.asyncio
    async def test_categorized_lists_present_when_closed(self):
        """All three new lists must appear in the response, even when closed."""
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
        assert result["admitted"] == []
        assert result["classical_axioms"] == []
        assert result["user_axioms"] == []

    @pytest.mark.asyncio
    async def test_categorized_lists_classical_only(self):
        self._query_result = {
            "success": True,
            "output": (
                "Axioms:\n"
                "Coq.Logic.Classical_Prop.classic : forall P : Prop, P \\/ ~ P"
            ),
        }
        result = await run_assumptions(
            name="thm",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["admitted"] == []
        assert result["classical_axioms"] == ["Coq.Logic.Classical_Prop.classic"]
        assert result["user_axioms"] == []

    @pytest.mark.asyncio
    async def test_categorized_lists_user_axiom(self):
        """A non-whitelist axiom lands in user_axioms (admitted stays empty
        because Print Assumptions does not distinguish Admitted from Axiom)."""
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
        assert result["admitted"] == []
        assert result["classical_axioms"] == []
        assert result["user_axioms"] == ["my_custom_axiom"]

    @pytest.mark.asyncio
    async def test_categorized_lists_mixed(self):
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
        assert result["admitted"] == []
        assert result["classical_axioms"] == ["Coq.Logic.Classical_Prop.classic"]
        assert result["user_axioms"] == ["my_custom_axiom"]

    @pytest.mark.asyncio
    async def test_verdict_field_retained_for_back_compat(self):
        """Phase 1 is additive only — verdict must still be in the response."""
        # closed
        self._query_result = {
            "success": True,
            "output": "Closed under the global context",
        }
        r = await run_assumptions(
            name="thm", file="test.v", workspace="/tmp", lifespan_state={}
        )
        assert "verdict" in r and r["verdict"] == "closed"

        # standard_only
        self._query_result = {
            "success": True,
            "output": (
                "Axioms:\n"
                "Coq.Logic.Classical_Prop.classic"
                " : forall P : Prop, P \\/ ~ P"
            ),
        }
        r = await run_assumptions(
            name="thm", file="test.v", workspace="/tmp", lifespan_state={}
        )
        assert r["verdict"] == "standard_only"

        # suspicious
        self._query_result = {
            "success": True,
            "output": "Axioms:\nmy_custom_axiom : False",
        }
        r = await run_assumptions(
            name="thm", file="test.v", workspace="/tmp", lifespan_state={}
        )
        assert r["verdict"] == "suspicious"

    @pytest.mark.asyncio
    async def test_assumptions_field_retained_for_back_compat(self):
        """The legacy ``assumptions`` and ``standard_assumptions`` keys must
        still be populated alongside the new lists."""
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
            name="thm",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert "assumptions" in result
        assert any("my_custom_axiom" in a for a in result["assumptions"])
        assert "standard_assumptions" in result
        assert any(
            "Classical_Prop.classic" in a for a in result["standard_assumptions"]
        )

    @pytest.mark.asyncio
    async def test_run_assumptions_propagates_populated_admitted(self, monkeypatch):
        """Verify run_assumptions surfaces ``admitted`` from the parser, even
        when populated externally — proves the wiring works once admit
        detection lands in a future phase.

        Today no caller passes ``admitted_names``, so ``admitted`` is
        structurally ``[]`` in the production flow.  This test stubs the
        parser to return a populated list and asserts the tool layer
        forwards it unchanged into ``result["admitted"]``.
        """
        self._query_result = {
            "success": True,
            "output": "Axioms:\nfuel_bound_admit : nat -> Prop\nmy_axiom : True",
        }

        def fake_classify(stdout, admitted_names=None):
            return (
                "suspicious",
                {
                    "admitted": ["fuel_bound_admit"],
                    "classical_axioms": [],
                    "user_axioms": ["my_axiom"],
                    "standard": [],
                    "suspicious": [
                        "my_axiom : True",
                        "fuel_bound_admit : nat -> Prop",
                    ],
                    "suspicious_names": ["my_axiom", "fuel_bound_admit"],
                },
            )

        monkeypatch.setattr(
            "rocq_mcp.verify.parse_and_classify_assumptions", fake_classify
        )

        result = await run_assumptions(
            name="thm",
            file="test.v",
            workspace="/tmp",
            lifespan_state={},
        )
        assert result["success"] is True
        assert result["admitted"] == ["fuel_bound_admit"]
        assert result["user_axioms"] == ["my_axiom"]
        assert result["classical_axioms"] == []
        assert result["verdict"] == "suspicious"

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


def _make_lifespan_state(pet_timeout: float = 30.0) -> dict:
    return {
        "pet_client": None,
        "pet_timeout": pet_timeout,
        "current_workspace": None,
    }


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
        assert result["verdict"] == "closed"


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
            return {"success": True, "verdict": "closed", "assumptions": []}

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
