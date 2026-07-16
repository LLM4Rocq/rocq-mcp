"""The degraded-enrichment convention (rocq_mcp.envelope).

Contract:
- ``degraded`` appears on a response only when at least one best-effort
  enrichment step failed; it is then a non-empty ``list[str]`` of stable
  ``"<field>:<code>"`` strings.
- It never appears as an empty list.
- ``degraded_detail`` appears only under ``ROCQ_DEBUG_ENRICHMENT=1``.
- Failures also bump ``lifespan_state["enrichment_failures"]`` counters
  (surfaced by rocq_diag).
"""

from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

from rocq_mcp import envelope
from rocq_mcp.interactive import _try_get_goals_with_depth
from tests.conftest import _MockPetBase


class TestPrimitives:
    def test_note_is_a_noop_outside_a_scope(self):
        # Must never raise or leak when no run_* scope is active.
        envelope.note_degraded("goals:pet_call_failed", "detail")

    async def test_decorator_attaches_only_when_noted(self):
        @envelope.collects_degraded
        async def clean_run(*, lifespan_state=None):
            return {"success": True}

        @envelope.collects_degraded
        async def degraded_run(*, lifespan_state=None):
            envelope.note_degraded("goals:pet_call_failed", "boom")
            return {"success": True}

        clean = await clean_run(lifespan_state=None)
        assert "degraded" not in clean

        got = await degraded_run(lifespan_state=None)
        assert got["degraded"] == ["goals:pet_call_failed"]
        assert "degraded_detail" not in got  # debug env not set

    async def test_debug_env_adds_detail(self, monkeypatch):
        monkeypatch.setenv("ROCQ_DEBUG_ENRICHMENT", "1")

        @envelope.collects_degraded
        async def degraded_run(*, lifespan_state=None):
            envelope.note_degraded("goals:pet_call_failed", "RuntimeError('x')")
            return {"success": True}

        got = await degraded_run(lifespan_state=None)
        assert got["degraded_detail"] == {"goals:pet_call_failed": "RuntimeError('x')"}

    async def test_counters_bump_per_code(self):
        state = {"enrichment_failures": {}}

        @envelope.collects_degraded
        async def degraded_run(*, lifespan_state=None):
            envelope.note_degraded("goals:pet_call_failed")
            envelope.note_degraded("goals:pet_call_failed")  # deduped in notes
            envelope.note_degraded("available_in_file:toc_failed")
            return {"success": True}

        await degraded_run(lifespan_state=state)
        await degraded_run(lifespan_state=state)
        assert state["enrichment_failures"] == {
            "goals:pet_call_failed": 2,
            "available_in_file:toc_failed": 2,
        }

    async def test_failure_envelopes_can_carry_degraded_too(self):
        @envelope.collects_degraded
        async def failing_run(*, lifespan_state=None):
            envelope.note_degraded("goals:pet_call_failed")
            return {"success": False, "error": "x", "reason": "tactic_failed"}

        got = await failing_run(lifespan_state=None)
        # Required failure keys unchanged; degraded is additive.
        assert got["success"] is False
        assert got["reason"] == "tactic_failed"
        assert got["degraded"] == ["goals:pet_call_failed"]

    async def test_non_dict_results_pass_through(self):
        @envelope.collects_degraded
        async def weird_run(*, lifespan_state=None):
            envelope.note_degraded("goals:pet_call_failed")
            return None

        assert await weird_run(lifespan_state=None) is None


class TestSwallowSitesRecord:
    def test_try_get_goals_records_inside_a_scope(self):
        pet = MagicMock()
        pet.complete_goals.side_effect = RuntimeError("pet exploded")

        payload = {"codes": [], "details": {}}
        token = envelope._degraded.set(payload)
        try:
            text, depth = _try_get_goals_with_depth(pet, SimpleNamespace(st=1))
        finally:
            envelope._degraded.reset(token)

        assert text is None and depth is None
        assert payload["codes"] == ["goals:pet_call_failed"]


class TestEndToEnd(_MockPetBase):
    """Through the real run_check path with a mock pet whose goal fetch dies."""

    @pytest.mark.asyncio
    async def test_run_check_reports_degraded_goals(self):
        from rocq_mcp.interactive import run_check

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(st=99, proof_finished=False, feedback=[])

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)
        lifespan_state["enrichment_failures"] = {}
        mock_pet.complete_goals.side_effect = RuntimeError("goal fetch died")

        result = await run_check(
            body="intros.",
            timeout=5.0,
            lifespan_state=lifespan_state,
            from_state=sid,
        )
        assert result["success"] is True
        assert result["goals"] == "(goals unavailable)"
        assert "goals:pet_call_failed" in result["degraded"]
        assert lifespan_state["enrichment_failures"]["goals:pet_call_failed"] >= 1
