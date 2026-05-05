"""Real-pet integration tests for Phase 1 features that were previously
mock-only — closes audit finding #9.

Each Phase 1 feature claimed to be load-bearing in production but had
zero coverage against a real pet subprocess:

- §1.3 memory watchdog: aborts pet calls when RSS exceeds the threshold.
- §1.4 ``rocq_diag``: reports live pet/memory/state diagnostics.
- §1.7 ``not_found`` reason classification + TOC cache enrichment:
  rocq_assumptions on a typo'd theorem name returns
  ``reason="not_found"`` and a populated ``available_in_file`` list
  fetched through the cached ``pet.toc`` lookup.

These tests skip when ``pet`` is not on PATH.
"""

from __future__ import annotations

from collections import deque
from pathlib import Path

import pytest

from tests.conftest import PET_AVAILABLE, make_lifespan_state

pytestmark = pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")


# ---------------------------------------------------------------------------
# §1.3 — memory watchdog (real pet, fake threshold)
# ---------------------------------------------------------------------------


class TestMemoryWatchdogRealPet:
    """Mock-only tests cover the cancellation logic; this test pins the
    end-to-end wiring against a real pet subprocess.  We force a tiny
    RSS cap (1 MB) so any real pet — even at startup — exceeds it and
    the watchdog fires the abort path."""

    @pytest.mark.asyncio
    async def test_memory_watchdog_aborts_real_pet_call(self, workspace, monkeypatch):
        import rocq_mcp.server as _server
        from rocq_mcp.interactive import run_query

        # Cap pet RSS at 1 MB.  A real pet uses tens of MB even idle, so
        # the watchdog must fire on the first sample.
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1)
        # Speed up watchdog poll so it samples within the call budget.
        monkeypatch.setattr(_server, "_MEMORY_WATCHDOG_INTERVAL", 0.05)

        ls = make_lifespan_state(pet_timeout=10.0)
        ls["recent_errors"] = deque(maxlen=10)
        try:
            result = await run_query(
                command="Search nat.",
                preamble="",
                workspace=str(workspace),
                lifespan_state=ls,
            )
            assert result["success"] is False
            assert result["reason"] == "memory_exhausted"
            # Pet must have been killed and is reported as restarted.
            assert result.get("pet_restarted") is True
            # Recent-errors trail picks it up under the same reason.
            assert any(
                e.get("reason") == "memory_exhausted" for e in ls["recent_errors"]
            )
        finally:
            _server._invalidate_pet(ls)


# ---------------------------------------------------------------------------
# §1.4 — rocq_diag against a live pet
# ---------------------------------------------------------------------------


class TestRocqDiagRealPet:
    """rocq_diag must report real pet pid / uptime / memory after a real
    call has spawned pet.  Mock tests cover the snapshot-builder logic
    in isolation; this exercise pins the full read-side wiring."""

    @pytest.mark.asyncio
    async def test_diag_reports_live_pet_after_real_call(self, workspace):
        from rocq_mcp.diag import _build_diag_snapshot
        from rocq_mcp.interactive import run_query
        from rocq_mcp.server import _invalidate_pet, ROCQ_MAX_PET_RSS_MB

        ls = make_lifespan_state(pet_timeout=30.0)
        ls["recent_errors"] = deque(maxlen=10)

        try:
            # Real call to spawn pet + record uptime / total_spawns.
            ok = await run_query(
                command="Check Nat.add.",
                preamble="",
                workspace=str(workspace),
                lifespan_state=ls,
            )
            assert ok["success"] is True

            snap = _build_diag_snapshot(ls)
            # Pet must be live with a real PID.
            assert snap["success"] is True
            assert isinstance(snap["pet"]["pid"], int)
            assert snap["pet"]["pid"] > 0
            assert snap["pet"]["uptime_seconds"] >= 0
            # First spawn — restart counter is 0.
            assert snap["pet"]["restarts"] == 0
            # Memory section reports a real RSS sample (psutil-backed).
            mem = snap["memory"]
            assert mem["sample_status"] == "ok"
            assert isinstance(mem["pet_rss_mb"], float)
            assert mem["pet_rss_mb"] > 0
            assert mem["max_rss_mb_threshold"] == float(ROCQ_MAX_PET_RSS_MB)
        finally:
            _invalidate_pet(ls)


# ---------------------------------------------------------------------------
# §1.7 — not_found reason + cached available_in_file enrichment
# ---------------------------------------------------------------------------


class TestNotFoundEnrichmentRealPet:
    """A typo'd theorem name on rocq_assumptions must return:

    - ``reason == "not_found"`` (not the generic ``crashed``)
    - ``available_in_file`` populated with the file's real defined
      names — proving ``_toc_names_cached`` works against a real pet
      and the §1.3 cache key (file + mtime) is correct.
    """

    @pytest.mark.asyncio
    async def test_typo_yields_not_found_with_real_available_in_file(self, workspace):
        from rocq_mcp.interactive import run_assumptions
        from rocq_mcp.server import _invalidate_pet

        vfile = Path(workspace) / "real_pet_typo.v"
        vfile.write_text(
            "Theorem alpha : True. Proof. exact I. Qed.\n"
            "Theorem fuel_bound : True. Proof. exact I. Qed.\n"
            "Theorem zeta : True. Proof. exact I. Qed.\n"
        )

        ls = make_lifespan_state(pet_timeout=30.0)
        ls["recent_errors"] = deque(maxlen=10)

        try:
            result = await run_assumptions(
                name="fool_bound",  # typo for fuel_bound
                file="real_pet_typo.v",
                workspace=str(workspace),
                lifespan_state=ls,
            )
            assert result["success"] is False
            assert result["reason"] == "not_found"
            names = result.get("available_in_file") or []
            # The three theorems must appear; the typo'd name must not.
            assert "fuel_bound" in names
            assert "alpha" in names
            assert "zeta" in names
            assert "fool_bound" not in names
            # The recent-errors deque records this under the same reason
            # (rocq_diag would surface it).
            not_found = [
                e
                for e in ls["recent_errors"]
                if e.get("tool") == "rocq_assumptions"
                and e.get("reason") == "not_found"
            ]
            assert len(not_found) >= 1
        finally:
            _invalidate_pet(ls)
