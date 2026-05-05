"""Tests for the ``rocq_diag`` operational diagnostics tool.

The tool exposes pet uptime, restart count, memory headroom (composing with
the §1.3 memory watchdog), live state IDs, and a ring buffer of recent
errors.  These tests exercise both the response schema and the wiring of
each diagnostic counter at its source (``_ensure_pet`` for restarts,
``_invalidate_pet`` for generation, watchdog for peak RSS, every error
path in ``_run_with_pet`` for ``recent_errors``).
"""

from __future__ import annotations

import time
from unittest.mock import MagicMock

import pytest

import rocq_mcp.server as _server
from rocq_mcp.server import (
    _build_diag_snapshot,
    _record_error,
    _run_with_pet,
    rocq_diag,
)
from tests.conftest import (
    _MockContext,
    FakePsutilProcess as _FakePsutilProcess,
    add_mock_state,
    make_lifespan_state,
    mock_pet as _mock_pet,
    patch_psutil_rss as _patch_psutil_rss,
)


def _fresh_lifespan_state() -> dict:
    """Build a lifespan_state dict matching ``app_lifespan``'s schema."""
    return make_lifespan_state(full=True)


@pytest.fixture(autouse=True)
def _reset_pet_state(monkeypatch):
    """Reset pet semaphore + lock between tests."""
    _server._pet_semaphore = None
    import threading

    monkeypatch.setattr(_server, "_pet_lock", threading.Lock())
    yield
    _server._pet_semaphore = None


@pytest.fixture(autouse=True)
def _fast_watchdog(monkeypatch):
    monkeypatch.setattr(_server, "_MEMORY_WATCHDOG_INTERVAL", 0.01)


# ---------------------------------------------------------------------------
# Schema / smoke tests
# ---------------------------------------------------------------------------


class TestDiagSchema:
    @pytest.mark.asyncio
    async def test_diag_returns_expected_keys(self):
        ls = _fresh_lifespan_state()
        snap = _build_diag_snapshot(ls)
        assert set(snap.keys()) == {
            "success",
            "pet",
            "memory",
            "live_states",
            "live_states_total",
            "recent_errors",
        }
        assert snap["success"] is True
        assert set(snap["pet"].keys()) == {
            "pid",
            "uptime_seconds",
            "restarts",
            "generation",
        }
        assert set(snap["memory"].keys()) == {
            "pet_rss_mb",
            "peak_pet_rss_mb",
            "max_rss_mb_threshold",
            "sample_status",
        }
        assert isinstance(snap["live_states"], list)
        assert isinstance(snap["live_states_total"], int)
        assert isinstance(snap["recent_errors"], list)

    @pytest.mark.asyncio
    async def test_diag_when_pet_not_running(self):
        ls = _fresh_lifespan_state()
        snap = _build_diag_snapshot(ls)
        assert snap["success"] is True
        assert snap["pet"]["pid"] is None
        assert snap["pet"]["uptime_seconds"] == 0.0
        assert snap["pet"]["restarts"] == 0
        assert snap["pet"]["generation"] == 0
        assert snap["memory"]["pet_rss_mb"] is None
        assert snap["memory"]["peak_pet_rss_mb"] == 0.0
        assert snap["memory"]["sample_status"] == "no_pet"
        assert snap["live_states"] == []
        assert snap["live_states_total"] == 0
        assert snap["recent_errors"] == []

    @pytest.mark.asyncio
    async def test_max_rss_mb_threshold_reports_env_value(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 4242)
        ls = _fresh_lifespan_state()
        snap = _build_diag_snapshot(ls)
        assert snap["memory"]["max_rss_mb_threshold"] == 4242.0

    @pytest.mark.asyncio
    async def test_diag_tool_routes_to_snapshot(self):
        ls = _fresh_lifespan_state()
        ctx = _MockContext(ls)
        snap = await rocq_diag(ctx=ctx)
        assert snap["success"] is True
        assert snap["pet"]["pid"] is None
        assert "memory" in snap

    @pytest.mark.asyncio
    async def test_diag_tool_no_context(self):
        result = await rocq_diag(ctx=None)
        assert result["success"] is False
        assert "MCP context" in result["error"]


# ---------------------------------------------------------------------------
# Pet uptime / pid sampling
# ---------------------------------------------------------------------------


class TestDiagPetSampling:
    @pytest.mark.asyncio
    async def test_pet_uptime_reflects_started_at(self, monkeypatch):
        ls = _fresh_lifespan_state()
        ls["pet_client"] = _mock_pet(pid=999)
        ls["pet_started_at"] = time.time() - 5.0
        snap = _build_diag_snapshot(ls)
        assert snap["pet"]["pid"] == 999
        assert 4.0 <= snap["pet"]["uptime_seconds"] <= 7.0

    @pytest.mark.asyncio
    async def test_pet_rss_mb_live_sample(self, monkeypatch):
        _patch_psutil_rss(monkeypatch, 256)
        ls = _fresh_lifespan_state()
        ls["pet_client"] = _mock_pet()
        ls["pet_started_at"] = time.time()
        snap = _build_diag_snapshot(ls)
        # 256 MB sample (rss_bytes = 256 * 1024 * 1024 -> 256.0 MB exact)
        assert snap["memory"]["pet_rss_mb"] == pytest.approx(256.0, rel=1e-3)

    @pytest.mark.asyncio
    async def test_pet_rss_mb_handles_psutil_error(self, monkeypatch):
        import psutil

        def _raise(pid):
            raise psutil.NoSuchProcess(pid)

        monkeypatch.setattr(psutil, "Process", _raise)
        ls = _fresh_lifespan_state()
        ls["pet_client"] = _mock_pet()
        ls["pet_started_at"] = time.time()
        snap = _build_diag_snapshot(ls)
        assert snap["memory"]["pet_rss_mb"] is None
        assert snap["memory"]["sample_status"] == "psutil_error"


# ---------------------------------------------------------------------------
# Wiring: pet.restarts (derived from total_spawns) + pet_generation
# ---------------------------------------------------------------------------


class TestRestartCounters:
    """``_ensure_pet`` bumps ``total_spawns`` on every successful spawn;
    ``pet.restarts`` is derived as ``max(0, total_spawns - 1)``.
    ``_invalidate_pet`` bumps ``pet_generation`` every time."""

    def test_first_spawn_does_not_count_as_restart(self, monkeypatch):
        """Bypass real Pytanque: stub it out and verify counters update."""
        ls = _fresh_lifespan_state()

        spawned: list[MagicMock] = []

        class _StubPytanque:
            def __init__(self, *a, **kw):
                self._mock = _mock_pet(pid=42)
                self.process = self._mock.process
                self._own_pgrp = False
                spawned.append(self._mock)

            def connect(self):
                pass

        class _StubMode:
            STDIO = "stdio"

        import sys

        fake_mod = type(sys)("pytanque")
        fake_mod.Pytanque = _StubPytanque
        fake_mod.PytanqueMode = _StubMode
        fake_mod.PetanqueError = type("PetanqueError", (Exception,), {})
        monkeypatch.setitem(sys.modules, "pytanque", fake_mod)

        # First spawn: total_spawns goes 0 -> 1; restarts (derived) is 0.
        _server._ensure_pet(ls)
        assert ls["total_spawns"] == 1
        assert _server._build_diag_snapshot(ls)["pet"]["restarts"] == 0
        assert ls["pet_started_at"] is not None
        first_started = ls["pet_started_at"]

        # Force a respawn: kill the previous pet so _pet_alive returns False.
        ls["pet_client"].process.poll.return_value = 1
        time.sleep(0.01)  # ensure timestamp difference
        _server._ensure_pet(ls)
        assert ls["total_spawns"] == 2
        assert _server._build_diag_snapshot(ls)["pet"]["restarts"] == 1
        assert ls["pet_started_at"] > first_started

        # Third call replaces a dead pet again.
        ls["pet_client"].process.poll.return_value = 1
        _server._ensure_pet(ls)
        assert ls["total_spawns"] == 3
        assert _server._build_diag_snapshot(ls)["pet"]["restarts"] == 2

    def test_pet_generation_bumps_on_invalidate(self):
        ls = _fresh_lifespan_state()
        assert ls["pet_generation"] == 0
        _server._invalidate_pet(ls)
        assert ls["pet_generation"] == 1
        _server._invalidate_pet(ls)
        assert ls["pet_generation"] == 2

    def test_invalidate_with_active_pet_kills_and_bumps(self, monkeypatch):
        ls = _fresh_lifespan_state()
        mock_pet = _mock_pet()
        ls["pet_client"] = mock_pet

        # Stub _kill_pet to avoid touching real process state.
        killed: list[MagicMock] = []
        monkeypatch.setattr(_server, "_kill_pet", lambda p: killed.append(p))
        # Suppress the state-table invalidation hook (no-op for this test).
        monkeypatch.setattr(_server, "_pet_invalidation_hooks", [])

        _server._invalidate_pet(ls)
        assert killed == [mock_pet]
        assert ls["pet_client"] is None
        assert ls["pet_generation"] == 1


# ---------------------------------------------------------------------------
# Wiring: peak_pet_rss_mb
# ---------------------------------------------------------------------------


class TestPeakRss:
    @pytest.mark.asyncio
    async def test_peak_rss_updated_by_watchdog(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 100_000)
        _patch_psutil_rss(monkeypatch, 256)

        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)

        def fn(pet):
            time.sleep(0.05)
            return {"success": True}

        await _run_with_pet(fn, ls, "Op")
        # Peak should reflect at least one sample of 256 MB.
        assert ls["peak_pet_rss_mb"] >= 256.0

    @pytest.mark.asyncio
    async def test_peak_rss_monotonic(self, monkeypatch):
        ls = _fresh_lifespan_state()
        ls["peak_pet_rss_mb"] = 500.0
        # Subsequent diag snapshots reflect the stored peak even when pet
        # is gone.
        snap = _build_diag_snapshot(ls)
        assert snap["memory"]["peak_pet_rss_mb"] == 500.0

    def test_peak_rss_resets_on_respawn(self, monkeypatch):
        """Peak from a dead pet must not poison the new pet's headroom."""
        ls = _fresh_lifespan_state()

        class _StubPytanque:
            def __init__(self, *a, **kw):
                self._mock = _mock_pet(pid=42)
                self.process = self._mock.process
                self._own_pgrp = False

            def connect(self):
                pass

        class _StubMode:
            STDIO = "stdio"

        import sys

        fake_mod = type(sys)("pytanque")
        fake_mod.Pytanque = _StubPytanque
        fake_mod.PytanqueMode = _StubMode
        fake_mod.PetanqueError = type("PetanqueError", (Exception,), {})
        monkeypatch.setitem(sys.modules, "pytanque", fake_mod)

        # First spawn: peak is fresh (0.0); first spawn must NOT clobber it.
        _server._ensure_pet(ls)
        ls["peak_pet_rss_mb"] = 1234.0  # simulate a sample

        # Force a respawn and verify the stale peak is reset.
        ls["pet_client"].process.poll.return_value = 1
        _server._ensure_pet(ls)
        assert ls["peak_pet_rss_mb"] == 0.0


# ---------------------------------------------------------------------------
# Wiring: recent_errors ring buffer
# ---------------------------------------------------------------------------


class TestRecentErrors:
    @pytest.mark.asyncio
    async def test_recent_errors_records_timeout(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)

        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        ls["pet_timeout"] = 0.05  # very short
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)
        monkeypatch.setattr(
            _server,
            "_invalidate_pet",
            lambda lstate: lstate.update(pet_client=None),
        )

        def fn_slow(pet):
            time.sleep(1.0)
            return {"success": True}

        result = await _run_with_pet(fn_slow, ls, "SlowOp")
        assert result["reason"] == "timeout"
        # Recorded in the buffer:
        assert len(ls["recent_errors"]) == 1
        e = ls["recent_errors"][0]
        assert e["tool"] == "SlowOp"
        assert "timed out" in e["message"]
        assert e["reason"] == "timeout"
        assert "occurred_at" in e

    @pytest.mark.asyncio
    async def test_recent_errors_records_memory_abort(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 100)
        _patch_psutil_rss(monkeypatch, 500)  # > 100

        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)
        monkeypatch.setattr(
            _server,
            "_invalidate_pet",
            lambda lstate: lstate.update(pet_client=None),
        )

        def fn_long(pet):
            time.sleep(0.2)
            return {"success": True}

        result = await _run_with_pet(fn_long, ls, "MemOp")
        assert result["reason"] == "memory_exhausted"
        assert len(ls["recent_errors"]) == 1
        e = ls["recent_errors"][0]
        assert e["tool"] == "MemOp"
        assert "RSS exceeded" in e["message"]
        assert e["reason"] == "memory_exhausted"
        # Peak RSS observed during this run is reflected in lifespan state.
        assert ls["peak_pet_rss_mb"] >= 500.0

    @pytest.mark.asyncio
    async def test_recent_errors_records_lock_contention(self, monkeypatch):
        """A held lock surfaces ``lock_contended`` and is recorded."""
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)

        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        ls["pet_timeout"] = 0.1
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)

        # Hold the pet lock from another thread so the worker times out
        # acquiring it.
        import threading

        held = threading.Event()
        release = threading.Event()

        def _hog():
            with _server._pet_lock:
                held.set()
                release.wait(timeout=1.0)

        t = threading.Thread(target=_hog, daemon=True)
        t.start()
        held.wait(timeout=1.0)

        try:
            result = await _run_with_pet(lambda pet: None, ls, "LockedOp")
        finally:
            release.set()
            t.join(timeout=1.0)

        assert result["reason"] == "lock_contended"
        assert any(
            e["tool"] == "LockedOp"
            and "lock contention" in e["message"]
            and e["reason"] == "lock_contended"
            for e in ls["recent_errors"]
        )

    @pytest.mark.asyncio
    async def test_recent_errors_records_petanque_error(self, monkeypatch):
        try:
            from pytanque import PetanqueError
        except ImportError:
            pytest.skip("pytanque not installed")

        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)

        mock_pet = _mock_pet(alive=True)
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)

        def fn_raises(pet):
            raise PetanqueError(1, "Tactic failed")

        result = await _run_with_pet(fn_raises, ls, "PetOp")
        assert result["success"] is False
        assert any(
            e["tool"] == "PetOp"
            and "Tactic failed" in e["message"]
            and e["reason"] == "crashed"
            for e in ls["recent_errors"]
        )

    @pytest.mark.asyncio
    async def test_recent_errors_ring_buffer_caps_at_max(self):
        ls = _fresh_lifespan_state()
        cap = _server._RECENT_ERRORS_MAX
        # Push five more than the cap so we can verify oldest entries drop.
        n = cap + 5
        for i in range(n):
            _record_error(ls, f"Op{i}", f"err{i}", reason="validation")
        assert len(ls["recent_errors"]) == cap
        # Oldest (n - cap) dropped; newest entry is f"Op{n-1}"
        tools = [e["tool"] for e in ls["recent_errors"]]
        assert tools[0] == f"Op{n - cap}"
        assert tools[-1] == f"Op{n - 1}"

    @pytest.mark.asyncio
    async def test_recent_errors_message_truncated(self):
        """Multi-KB messages are truncated so 20-entry buffer stays bounded."""
        ls = _fresh_lifespan_state()
        big = "x" * 5000
        _record_error(ls, "BigOp", big, reason="validation")
        stored = ls["recent_errors"][0]["message"]
        # Truncation produces exactly _RECENT_ERROR_MESSAGE_LIMIT chars + "..."
        assert len(stored) == _server._RECENT_ERROR_MESSAGE_LIMIT + len("...")
        assert stored.endswith("...")
        # Short messages pass through untouched.
        _record_error(ls, "TinyOp", "boom", reason="validation")
        assert ls["recent_errors"][1]["message"] == "boom"

    @pytest.mark.asyncio
    async def test_recent_errors_exposed_via_diag(self):
        ls = _fresh_lifespan_state()
        _record_error(ls, "SomeOp", "boom", reason="validation")
        snap = _build_diag_snapshot(ls)
        assert len(snap["recent_errors"]) == 1
        e = snap["recent_errors"][0]
        assert e["tool"] == "SomeOp"
        assert e["message"] == "boom"
        assert e["reason"] == "validation"
        # Diag converts occurred_at -> ago_seconds
        assert "ago_seconds" in e
        assert "occurred_at" not in e
        assert e["ago_seconds"] >= 0.0


# ---------------------------------------------------------------------------
# Validation failures in interactive.py funnel into recent_errors
# ---------------------------------------------------------------------------


class TestValidationErrorsRecorded:
    """The validation paths in ``interactive.py`` (forbidden commands,
    missing files, invalid identifiers, ...) push to ``recent_errors``
    so the diag tool reports a complete failure history, not just the
    pet-level crashes."""

    @pytest.mark.asyncio
    async def test_run_query_forbidden_command_recorded(self):
        from rocq_mcp.interactive import run_query

        ls = _fresh_lifespan_state()
        result = await run_query(
            command="Drop.",  # forbidden
            preamble="",
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_query" for e in ls["recent_errors"])

    @pytest.mark.asyncio
    async def test_run_assumptions_missing_file_recorded(self):
        from rocq_mcp.interactive import run_assumptions

        ls = _fresh_lifespan_state()
        result = await run_assumptions(
            name="add_comm",
            file="",  # required
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_assumptions" for e in ls["recent_errors"])

    @pytest.mark.asyncio
    async def test_run_assumptions_invalid_identifier_recorded(self):
        from rocq_mcp.interactive import run_assumptions

        ls = _fresh_lifespan_state()
        result = await run_assumptions(
            name="not a valid id",
            file="some.v",
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_assumptions" for e in ls["recent_errors"])

    @pytest.mark.asyncio
    async def test_run_start_no_mode_recorded(self):
        from rocq_mcp.interactive import run_start

        ls = _fresh_lifespan_state()
        result = await run_start(
            file="",
            theorem="",
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_start" for e in ls["recent_errors"])

    @pytest.mark.asyncio
    async def test_run_check_forbidden_command_recorded(self):
        from rocq_mcp.interactive import run_check

        ls = _fresh_lifespan_state()
        result = await run_check(
            body="Drop.",  # forbidden
            timeout=1.0,
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_check" for e in ls["recent_errors"])

    @pytest.mark.asyncio
    async def test_run_step_multi_too_many_recorded(self):
        from rocq_mcp.interactive import run_step_multi

        ls = _fresh_lifespan_state()
        # _MAX_STEP_MULTI_TACTICS is 20; pass 25 to trigger the limit.
        result = await run_step_multi(
            tactics=["auto."] * 25,
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_step_multi" for e in ls["recent_errors"])

    @pytest.mark.asyncio
    async def test_run_notations_forbidden_recorded(self):
        from rocq_mcp.interactive import run_notations

        ls = _fresh_lifespan_state()
        result = await run_notations(
            statement="Drop.",  # forbidden
            preamble="",
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(e["tool"] == "rocq_notations" for e in ls["recent_errors"])


# ---------------------------------------------------------------------------
# live_states reporting
# ---------------------------------------------------------------------------


class TestLiveStates:
    @pytest.mark.asyncio
    async def test_diag_includes_live_states(self):
        ls = _fresh_lifespan_state()
        sid_a = add_mock_state(parent_id=None, tactic=None, step=0)
        sid_b = add_mock_state(parent_id=sid_a, tactic="intros.", step=1)
        snap = _build_diag_snapshot(ls)

        assert {s["state_id"] for s in snap["live_states"]} == {sid_a, sid_b}
        by_id = {s["state_id"]: s for s in snap["live_states"]}
        assert by_id[sid_a]["parent"] is None
        assert by_id[sid_b]["parent"] == sid_a
        assert by_id[sid_a]["file"] == "test.v"
        assert by_id[sid_a]["theorem"] == "t"
        for s in snap["live_states"]:
            assert s["age_seconds"] >= 0.0

    @pytest.mark.asyncio
    async def test_live_states_empty_when_table_empty(self):
        ls = _fresh_lifespan_state()
        snap = _build_diag_snapshot(ls)
        assert snap["live_states"] == []
        assert snap["live_states_total"] == 0

    @pytest.mark.asyncio
    async def test_live_states_capped_at_50(self):
        """``live_states`` is capped at 50; ``live_states_total`` is full count."""
        ls = _fresh_lifespan_state()
        n = _server._DIAG_LIVE_STATES_CAP + 7  # > 50
        for i in range(n):
            add_mock_state(parent_id=None, tactic=None, step=i)
        snap = _build_diag_snapshot(ls)
        assert len(snap["live_states"]) == _server._DIAG_LIVE_STATES_CAP
        assert snap["live_states_total"] == n


# ---------------------------------------------------------------------------
# Crash-path coverage: BrokenPipeError, FileNotFoundError, OSError, dead pet
# ---------------------------------------------------------------------------


class TestRecentErrorsCrashPaths:
    """Each pet-level failure path in ``_run_with_pet`` records into
    ``recent_errors`` with a canonical ``reason``."""

    @pytest.mark.asyncio
    async def test_recent_errors_records_broken_pipe(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)
        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)
        monkeypatch.setattr(
            _server,
            "_invalidate_pet",
            lambda lstate: lstate.update(pet_client=None),
        )

        def fn_pipe(pet):
            raise BrokenPipeError("pipe broken")

        result = await _run_with_pet(fn_pipe, ls, "BrokenPipeOp")
        assert result["success"] is False
        assert ls["recent_errors"][-1]["reason"] == "crashed"
        assert ls["recent_errors"][-1]["tool"] == "BrokenPipeOp"

    @pytest.mark.asyncio
    async def test_recent_errors_records_file_not_found(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)
        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)

        def fn_fnf(pet):
            raise FileNotFoundError("pet binary missing")

        result = await _run_with_pet(fn_fnf, ls, "FNFOp")
        assert result["success"] is False
        assert result["reason"] == "unavailable"
        assert ls["recent_errors"][-1]["reason"] == "unavailable"
        assert ls["recent_errors"][-1]["tool"] == "FNFOp"

    @pytest.mark.asyncio
    async def test_recent_errors_records_oserror(self, monkeypatch):
        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)
        mock_pet = _mock_pet()
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)

        def fn_oserr(pet):
            raise OSError("disk full")

        result = await _run_with_pet(fn_oserr, ls, "OSErrOp")
        assert result["success"] is False
        assert ls["recent_errors"][-1]["reason"] == "crashed"
        assert ls["recent_errors"][-1]["tool"] == "OSErrOp"

    @pytest.mark.asyncio
    async def test_recent_errors_records_dead_petanque_error(self, monkeypatch):
        """When pet has died (poll() != None) and PetanqueError fires,
        ``reason="crashed"`` is recorded and ``pet_restarted: True``."""
        try:
            from pytanque import PetanqueError
        except ImportError:
            pytest.skip("pytanque not installed")

        monkeypatch.setattr(_server, "ROCQ_MAX_PET_RSS_MB", 1_000_000)
        _patch_psutil_rss(monkeypatch, 1)
        mock_pet = _mock_pet(alive=False)  # poll() returns 1 -> dead
        ls = _fresh_lifespan_state()
        ls["pet_client"] = mock_pet
        monkeypatch.setattr(_server, "_ensure_pet", lambda lstate: mock_pet)
        monkeypatch.setattr(
            _server,
            "_invalidate_pet",
            lambda lstate: lstate.update(pet_client=None),
        )

        def fn_petanque(pet):
            raise PetanqueError(99, "pet died mid-call")

        result = await _run_with_pet(fn_petanque, ls, "DeadPetOp")
        assert result["success"] is False
        assert result["reason"] == "crashed"
        assert result.get("pet_restarted") is True
        e = ls["recent_errors"][-1]
        assert e["reason"] == "crashed"
        assert e["tool"] == "DeadPetOp"

    @pytest.mark.asyncio
    async def test_recent_errors_records_pytanque_unavailable(self, monkeypatch):
        """ImportError on pytanque -> ``reason="unavailable"`` recorded."""
        import sys

        # Force ``from pytanque import PetanqueError`` inside _run_with_pet
        # to raise ImportError.
        monkeypatch.setitem(sys.modules, "pytanque", None)

        ls = _fresh_lifespan_state()
        result = await _run_with_pet(lambda pet: None, ls, "ImportErrOp")
        assert result["success"] is False
        assert result["reason"] == "unavailable"
        assert ls["recent_errors"][-1]["reason"] == "unavailable"
        assert ls["recent_errors"][-1]["tool"] == "ImportErrOp"


# ---------------------------------------------------------------------------
# total_spawns / peak_pet_rss_mb invariants
# ---------------------------------------------------------------------------


class TestSpawnInvariants:
    def test_total_spawns_unchanged_on_init_failure(self, monkeypatch):
        """If Pytanque() raises, total_spawns must stay 0 and peak must
        not be zeroed (no successful spawn happened)."""
        ls = _fresh_lifespan_state()
        ls["peak_pet_rss_mb"] = 123.0  # baseline before any spawn

        class _ExplodingPytanque:
            def __init__(self, *a, **kw):
                raise RuntimeError("simulated init failure")

        class _StubMode:
            STDIO = "stdio"

        import sys

        fake_mod = type(sys)("pytanque")
        fake_mod.Pytanque = _ExplodingPytanque
        fake_mod.PytanqueMode = _StubMode
        fake_mod.PetanqueError = type("PetanqueError", (Exception,), {})
        monkeypatch.setitem(sys.modules, "pytanque", fake_mod)

        with pytest.raises(RuntimeError):
            _server._ensure_pet(ls)

        # No successful spawn: counter stays at 0, peak preserved.
        assert ls["total_spawns"] == 0
        assert ls["peak_pet_rss_mb"] == 123.0


# ---------------------------------------------------------------------------
# Validation paths (rocq_toc, reason field)
# ---------------------------------------------------------------------------


class TestExtraValidationRecording:
    @pytest.mark.asyncio
    async def test_validation_error_records_for_run_toc(self):
        """``run_toc`` validation failures land in ``recent_errors``
        under ``rocq_toc`` with ``reason="validation"``."""
        from rocq_mcp.interactive import run_toc

        ls = _fresh_lifespan_state()
        result = await run_toc(
            file="../../../etc/passwd",  # path traversal -> ValueError
            workspace="/tmp",
            lifespan_state=ls,
        )
        assert result["success"] is False
        assert any(
            e["tool"] == "rocq_toc" and e["reason"] == "validation"
            for e in ls["recent_errors"]
        )

    @pytest.mark.asyncio
    async def test_recent_errors_includes_reason(self):
        """Every documented reason round-trips through ``_record_error``
        and surfaces on the ``recent_errors[]`` entry.

        The expected list is enumerated explicitly (not iterated from
        the frozenset) so a regression that *removes* a reason from
        ``_RECENT_ERROR_REASONS`` without also removing the documented
        contract still fails this test — i.e. the test pins the public
        taxonomy, not just whatever the implementation happens to allow.
        """
        ls = _fresh_lifespan_state()
        expected = [
            # Pet-side (set by _run_with_pet)
            "timeout",
            "crashed",
            "memory_exhausted",
            "lock_contended",
            "unavailable",
            # Validation / lookup
            "validation",
            "not_found",
            # rocq_check mid-batch
            "tactic_failed",
            # rocq_verify-specific
            "compile_error",
            "axiom_dependency",
            "type_mismatch",
        ]
        for reason in expected:
            _record_error(ls, f"tool_{reason}", "msg", reason=reason)
        snap = _build_diag_snapshot(ls)
        reasons = [e["reason"] for e in snap["recent_errors"]]
        assert reasons == expected

    def test_record_error_rejects_unknown_reason(self):
        """A typo'd reason must trip the assertion at write time so it
        cannot silently appear in rocq_diag output and break agent
        dispatch logic.  Mirrors _VALID_STATE_CAPTURE_STATUSES."""
        ls = _fresh_lifespan_state()
        with pytest.raises(AssertionError, match="unknown error reason"):
            _record_error(ls, "tool_x", "msg", reason="totally_made_up")

    def test_documented_reason_set_matches_expected(self):
        """``_RECENT_ERROR_REASONS`` must equal the documented set —
        not a superset (silently broadens the contract) or a subset
        (silently narrows it).  Independent of any test that iterates
        the frozenset (which would tautologically cover whatever's in
        it)."""
        assert _server._RECENT_ERROR_REASONS == frozenset(
            {
                "timeout",
                "crashed",
                "memory_exhausted",
                "lock_contended",
                "unavailable",
                "validation",
                "not_found",
                "tactic_failed",
                "compile_error",
                "axiom_dependency",
                "type_mismatch",
            }
        )


# ---------------------------------------------------------------------------
# pet_rss sample_status branches (no_pet vs psutil_error)
# ---------------------------------------------------------------------------


class TestPetRssSampleStatus:
    @pytest.mark.asyncio
    async def test_pet_rss_sample_status_no_pet(self):
        ls = _fresh_lifespan_state()
        # No pet_client at all.
        rss, status = _server._sample_pet_rss_mb(ls)
        assert rss is None
        assert status == "no_pet"
        snap = _build_diag_snapshot(ls)
        assert snap["memory"]["pet_rss_mb"] is None
        assert snap["memory"]["sample_status"] == "no_pet"

    @pytest.mark.asyncio
    async def test_pet_rss_sample_status_psutil_error(self, monkeypatch):
        import psutil

        def _raise(pid):
            raise psutil.NoSuchProcess(pid)

        monkeypatch.setattr(psutil, "Process", _raise)
        ls = _fresh_lifespan_state()
        ls["pet_client"] = _mock_pet()
        rss, status = _server._sample_pet_rss_mb(ls)
        assert rss is None
        assert status == "psutil_error"
        snap = _build_diag_snapshot(ls)
        assert snap["memory"]["pet_rss_mb"] is None
        assert snap["memory"]["sample_status"] == "psutil_error"
