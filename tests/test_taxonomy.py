"""Wire-protocol pins for the failure-reason taxonomy.

The ``reason`` strings are agent-visible protocol: agents dispatch on
them, the README documents them, and ``recent_errors`` records them.
These tests make renaming a member a deliberate, test-breaking act.
"""

from __future__ import annotations

from typing import get_args

from rocq_mcp import taxonomy

# The exact wire strings.  Changing this set is a protocol change:
# update the CHANGELOG, the server instructions, and the guides.
EXPECTED_REASONS = {
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

EXPECTED_PET_SIDE = {
    "timeout",
    "crashed",
    "memory_exhausted",
    "lock_contended",
    "unavailable",
}


def test_reason_wire_strings_are_pinned():
    assert {str(r) for r in taxonomy.FailureReason} == EXPECTED_REASONS


def test_pet_side_subset():
    assert taxonomy.PET_SIDE_FAILURE_REASONS == EXPECTED_PET_SIDE
    assert taxonomy.PET_SIDE_FAILURE_REASONS <= taxonomy.RECENT_ERROR_REASONS


def test_members_are_plain_strings_on_the_wire():
    # StrEnum members must serialize and compare as their string values —
    # the whole envelope contract depends on it.
    assert taxonomy.FailureReason.TIMEOUT == "timeout"
    assert isinstance(taxonomy.FailureReason.TIMEOUT, str)
    assert "timeout" in taxonomy.PET_SIDE_FAILURE_REASONS


def test_state_capture_statuses_compose():
    assert taxonomy.STATE_CAPTURE_STATUSES == (
        EXPECTED_PET_SIDE | {"ok", "outside_proof", "no_position"}
    )


def test_enrichment_literal_matches_taxonomy():
    """compile_enrichment's typing Literal must equal the canonical set."""
    from rocq_mcp.compile_enrichment import _StateCaptureStatus

    assert frozenset(get_args(_StateCaptureStatus)) == taxonomy.STATE_CAPTURE_STATUSES


def test_server_alias_stays_bound():
    """Tests still read the recent-errors set via ``_server.<name>``."""
    import rocq_mcp.server as _server

    assert _server._RECENT_ERROR_REASONS is taxonomy.RECENT_ERROR_REASONS
