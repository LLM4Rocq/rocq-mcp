"""Single source of truth for the failure-reason taxonomy.

Every failure envelope in this codebase is ``{success: False, error: str,
reason: str}`` where ``reason`` is one of :class:`FailureReason`'s values.
Agents dispatch on these strings — they are **wire protocol**, pinned by
``tests/test_taxonomy.py``.  Renaming a member changes agent-visible
behavior and requires a changelog entry.

Before this module existed, three separate frozensets lived in
``server.py`` / ``compile_enrichment.py`` / ``interactive.py`` with
module-load asserts keeping them aligned.  The sets below are *derived*
from one enum, so the alignment holds by construction.

This module imports nothing from the package (leaf module) — safe to
import from anywhere without cycles.
"""

from __future__ import annotations

from enum import StrEnum


class FailureReason(StrEnum):
    """Allowed values of the ``reason`` field on failure envelopes."""

    # -- pet-side: produced by ``_run_with_pet``'s except arms ------------
    TIMEOUT = "timeout"
    CRASHED = "crashed"
    MEMORY_EXHAUSTED = "memory_exhausted"
    LOCK_CONTENDED = "lock_contended"
    UNAVAILABLE = "unavailable"

    # -- tool-side: produced before/around pet ----------------------------
    #: Input validation failed before any work happened.
    VALIDATION = "validation"
    #: Name resolution failed (rocq_start / rocq_assumptions typos).
    NOT_FOUND = "not_found"
    #: rocq_check mid-batch: Coq rejected a tactic (pet still healthy).
    TACTIC_FAILED = "tactic_failed"
    #: rocq_search: Coq rejected the Search pattern/filter syntax.
    QUERY_REJECTED = "query_rejected"
    #: coqc returned non-zero (rocq_compile / rocq_compile_file / rocq_verify).
    COMPILE_ERROR = "compile_error"
    #: rocq_verify: proof relies on Admitted/admit or a non-whitelisted axiom.
    AXIOM_DEPENDENCY = "axiom_dependency"
    #: rocq_verify phase 3: the proof's type differs from the problem's type.
    TYPE_MISMATCH = "type_mismatch"


#: Failure reasons emitted by ``_run_with_pet``'s except arms — the
#: subprocess/transport level failures, as opposed to tool-level ones.
PET_SIDE_FAILURE_REASONS: frozenset[str] = frozenset(
    {
        FailureReason.TIMEOUT,
        FailureReason.CRASHED,
        FailureReason.MEMORY_EXHAUSTED,
        FailureReason.LOCK_CONTENDED,
        FailureReason.UNAVAILABLE,
    }
)

#: Allowed values for the ``reason`` field on ``recent_errors`` entries
#: (the ring buffer surfaced by ``rocq_diag``) — i.e. every reason.
RECENT_ERROR_REASONS: frozenset[str] = frozenset(FailureReason)

#: ``state_capture_status`` values that do NOT indicate a pet-side
#: failure: enrichment either succeeded (``ok``), or was structurally
#: impossible (error outside any proof / no position to capture at).
NON_FAILURE_CAPTURE_STATUSES: frozenset[str] = frozenset(
    {"ok", "outside_proof", "no_position"}
)

#: Allowed values of the ``state_capture_status`` key on failed
#: ``rocq_compile`` / ``rocq_compile_file`` responses: the pet-side
#: failure modes plus the non-failure statuses above.
STATE_CAPTURE_STATUSES: frozenset[str] = (
    PET_SIDE_FAILURE_REASONS | NON_FAILURE_CAPTURE_STATUSES
)
