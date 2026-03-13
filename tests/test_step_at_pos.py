"""Tests for position-based session start and coqc error position parsing."""

from __future__ import annotations

import pytest

from rocq_mcp.server import _parse_coqc_error_positions

# ---------------------------------------------------------------------------
# _parse_coqc_error_positions
# ---------------------------------------------------------------------------


class TestParseCoqcErrorPositions:
    """Test coqc stderr error position parsing."""

    def test_single_error(self):
        stderr = (
            'File "/tmp/foo.v", line 15, characters 2-5:\n'
            "Error: Unable to unify something.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        p = positions[0]
        assert p["line"] == 14  # 0-based
        assert p["character"] == 2
        assert p["end_character"] == 5
        assert "Unable to unify" in p["message"]

    def test_multiple_errors(self):
        stderr = (
            'File "/tmp/foo.v", line 3, characters 0-10:\n'
            "Error: First error.\n"
            'File "/tmp/foo.v", line 7, characters 4-8:\n'
            "Error: Second error.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 2
        assert positions[0]["line"] == 2
        assert positions[1]["line"] == 6

    def test_no_position(self):
        stderr = "Some random error without position info\n"
        positions = _parse_coqc_error_positions(stderr)
        assert positions == []

    def test_empty_stderr(self):
        assert _parse_coqc_error_positions("") == []

    def test_warning_parsed(self):
        stderr = (
            'File "/tmp/foo.v", line 1, characters 0-20:\n'
            "Warning: Deprecated feature.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert "Deprecated" in positions[0]["message"]

    def test_multiline_error_message(self):
        stderr = (
            'File "/tmp/foo.v", line 5, characters 10-15:\n'
            "Error: In environment\n"
            "n : nat\n"
            "Unable to unify something with something else.\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert "In environment" in positions[0]["message"]

    def test_message_truncated(self):
        long_msg = "Error: " + "x" * 600
        stderr = 'File "/tmp/foo.v", line 1, characters 0-5:\n' f"{long_msg}\n"
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert len(positions[0]["message"]) <= 500

    def test_line_conversion_1based_to_0based(self):
        """Line 1 in coqc → line 0 for pytanque."""
        stderr = 'File "/tmp/foo.v", line 1, characters 0-3:\n' "Error: Syntax error.\n"
        positions = _parse_coqc_error_positions(stderr)
        assert positions[0]["line"] == 0

    def test_unicode_filepath(self):
        stderr = (
            'File "/tmp/café_test.v", line 3, characters 0-5:\nError: Test error.\n'
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert positions[0]["line"] == 2

    def test_large_character_range(self):
        stderr = 'File "/tmp/foo.v", line 1, characters 0-999999:\nError: Very wide.\n'
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert positions[0]["end_character"] == 999999

    def test_error_followed_by_trailing_text(self):
        stderr = (
            'File "/tmp/foo.v", line 5, characters 2-8:\n'
            "Error: Unable to unify.\n"
            "Some extra context.\n"
            "\n"
        )
        positions = _parse_coqc_error_positions(stderr)
        assert len(positions) == 1
        assert "Unable to unify" in positions[0]["message"]


# ---------------------------------------------------------------------------
# Position-based session integration tests
# ---------------------------------------------------------------------------

from tests.conftest import PET_AVAILABLE


@pytest.mark.skipif(not PET_AVAILABLE, reason="pet not available")
class TestPositionBasedSessionIntegration:
    """Integration tests for position-based session start (require pet)."""

    @pytest.fixture
    def lifespan_state(self):
        from rocq_mcp.server import _invalidate_pet

        state = {"pet_client": None, "pet_timeout": 30.0}
        yield state
        _invalidate_pet(state)

    @pytest.mark.asyncio
    async def test_start_at_proof_position(self, workspace, lifespan_state):
        """Start a session at a proof position and execute a tactic."""
        from rocq_mcp.server import run_step

        vfile = workspace / "pos_test.v"
        vfile.write_text(
            "Theorem pos_test : forall n : nat, n = n.\n"
            "Proof.\n"
            "  intros.\n"
            "  reflexivity.\n"
            "Qed.\n"
        )
        # Position (2, 2) is at "intros." — state before it has goal "forall n, n = n"
        result = await run_step(
            tactic="intros.",
            file=str(vfile),
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            line=2,
            character=2,
        )
        assert result["success"] is True

    @pytest.mark.asyncio
    async def test_bounds_validation(self, workspace, lifespan_state):
        """Reject out-of-bounds line/character values."""
        from rocq_mcp.server import run_step

        vfile = workspace / "bounds_test.v"
        vfile.write_text("Theorem t : True. Proof. exact I. Qed.\n")
        result = await run_step(
            tactic="exact I.",
            file=str(vfile),
            theorem="",
            workspace=str(workspace),
            lifespan_state=lifespan_state,
            line=200000,
            character=0,
        )
        assert result["success"] is False
        assert "range" in result["error"].lower()
