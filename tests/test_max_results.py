"""Unit tests for the max_results parameter in run_query.

These tests mock at the pet boundary — the real ``_run_with_pet`` executes
around the mock, exercising its lock / semaphore / timeout / exception
paths.  The tests are about feedback truncation and count logic only.
"""

from __future__ import annotations

import pytest

import rocq_mcp.server as _server
import rocq_mcp.interactive as _int
from tests.conftest import _MockPetBase, make_lifespan_state


@pytest.fixture(autouse=True)
def _patch_pet_boundary(monkeypatch):
    """Patch ``_ensure_pet`` to return a mock pet — the real
    ``_run_with_pet`` orchestrator runs around it."""
    from types import SimpleNamespace

    class MockState:
        def __init__(self, feedback):
            self.feedback = feedback
            self.proof_finished = False

    class MockPet:
        def __init__(self):
            # ``_pet_alive`` consults pet.process.poll() inside the
            # PetanqueError handler, so the mock must expose it.
            self.process = SimpleNamespace(poll=lambda: None)
            self._feedback = [(0, f"result_{i}") for i in range(20)]

        def run(self, state, cmd, timeout=None):
            return MockState(self._feedback)

        def get_state_at_pos(self, path, line, col):
            return MockState([])

        def set_workspace(self, debug=False, dir=""):
            pass

    mock_pet = MockPet()
    monkeypatch.setattr(_server, "_ensure_pet", lambda ls: mock_pet)
    # Bypass import caching — just return a mock state directly
    monkeypatch.setattr(
        _int,
        "_get_or_create_import_state",
        lambda pet, ws, cmds, ls: MockState([]),
    )
    # Reset the global pet semaphore between tests so the orchestrator
    # rebuilds its own lock fresh inside each test's event loop.
    _server._pet_semaphore = None
    yield
    _server._pet_semaphore = None


class TestMaxResultsEdgeCases(_MockPetBase):
    """Unit tests for max_results truncation logic."""

    @pytest.mark.asyncio
    async def test_max_results_truncates(self):
        """max_results=5 on 20 results should show 5 + truncation notice."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=5,
        )
        assert result["success"] is True
        assert "more results" in result["output"]
        assert "15 more results" in result["output"]
        assert "20 total" in result["output"]

    @pytest.mark.asyncio
    async def test_max_results_none_no_truncation(self):
        """max_results=None should show all 20 results without notice."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=None,
        )
        assert result["success"] is True
        assert "more results" not in result["output"]

    @pytest.mark.asyncio
    async def test_max_results_zero_no_truncation(self):
        """max_results=0 should behave like None (no limit)."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=0,
        )
        assert result["success"] is True
        assert "more results" not in result["output"]

    @pytest.mark.asyncio
    async def test_max_results_negative_no_truncation(self):
        """max_results=-1 should behave like None (no limit)."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=-1,
        )
        assert result["success"] is True
        assert "more results" not in result["output"]

    @pytest.mark.asyncio
    async def test_max_results_exceeds_total_no_truncation(self):
        """max_results=100 on 20 results should show all without notice."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=100,
        )
        assert result["success"] is True
        assert "more results" not in result["output"]

    @pytest.mark.asyncio
    async def test_max_results_equal_to_total_no_truncation(self):
        """max_results=20 on 20 results should show all without notice."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=20,
        )
        assert result["success"] is True
        assert "more results" not in result["output"]

    @pytest.mark.asyncio
    async def test_max_results_one(self):
        """max_results=1 should show 1 result + truncation notice."""
        result = await _int.run_query(
            command="Search nat.",
            preamble="",
            workspace="/tmp",
            lifespan_state=make_lifespan_state(),
            max_results=1,
        )
        assert result["success"] is True
        assert "more results" in result["output"]
        assert "19 more results" in result["output"]
