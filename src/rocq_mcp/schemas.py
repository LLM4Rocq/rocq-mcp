"""Output schemas for the pilot tools (structured-content declarations).

Design rules (permissiveness and the taxonomy-sourced ``reason`` enum
are pinned by tests/test_schemas.py):

- **Permissive**: only ``success`` is required and
  ``additionalProperties`` stays ``true`` — every tool returns a union
  of success shape, failure envelope, and optional enrichment keys, and
  the schema must accept all of them (FastMCP already emits the dict as
  structured content; the schema is a declaration for clients, not a
  runtime straitjacket).
- **Token-budgeted**: schemas ship in ``tools/list``; each stays under
  ~1,000 chars.  Field descriptions cover only what agents dispatch on;
  the deep reference lives in ``rocq://guide/responses``.
- **Taxonomy-sourced**: the ``reason`` enum derives from
  :mod:`rocq_mcp.taxonomy`, so a new reason value propagates here by
  construction.
"""

from __future__ import annotations

from typing import Any

from rocq_mcp.taxonomy import FailureReason

_REASON_ENUM = sorted(str(r) for r in FailureReason)


def _envelope(properties: dict[str, Any]) -> dict[str, Any]:
    """A permissive tool-output schema: success + failure union."""
    return {
        "type": "object",
        "properties": {
            "success": {"type": "boolean"},
            "error": {"type": "string"},
            "reason": {"type": "string", "enum": _REASON_ENUM},
            **properties,
        },
        "required": ["success"],
        "additionalProperties": True,
    }


CHECK_OUTPUT_SCHEMA = _envelope(
    {
        "state_id": {
            "type": "integer",
            "description": "Pass as from_state to continue.",
        },
        "goals": {"description": "Per goals_format (string or list)."},
        "goals_diff": {"type": "object"},
        "proof_finished": {"type": "boolean"},
        "proof_tactics": {"type": "array", "items": {"type": "string"}},
        "proof_script": {
            "type": "string",
            "description": "Ready-to-paste proof when the statement was recoverable.",
        },
        "last_valid_state_id": {
            "type": "integer",
            "description": "Recovery state after tactic_failed.",
        },
        "failed_command": {"type": "string"},
        "focus_depth": {"type": "integer"},
    }
)

STEP_MULTI_OUTPUT_SCHEMA = _envelope(
    {
        "results": {
            "type": "array",
            "description": (
                "Per-tactic outcomes in input order; repeats carry "
                "same_outcome_as instead of goals."
            ),
        },
        "distinct_outcomes": {"type": "integer"},
        "summary": {
            "type": "object",
            "description": "tried/succeeded/finished/best overview.",
        },
        "from_state_id": {"type": "integer"},
    }
)

COMPILE_FILE_OUTPUT_SCHEMA = _envelope(
    {
        "output": {"type": "string"},
        "error_positions": {"type": "array"},
        "hint": {"type": "string", "description": "Suggested next call."},
        "state_capture_status": {"type": "string"},
        "state_id": {
            "type": "integer",
            "description": "Captured proof state at the error (when status ok).",
        },
        "errors": {
            "type": "array",
            "description": "Per-declaration multi-error walk (may be empty).",
        },
        "timing": {"type": "object"},
    }
)

SEARCH_OUTPUT_SCHEMA = _envelope(
    {
        "hits": {
            "type": "array",
            "description": "Parsed Search hits: {name, type?} or {raw}.",
        },
        "total": {"type": "integer"},
        "offset": {"type": "integer"},
        "truncated": {"type": "boolean"},
        "query": {"description": "The executed Search command(s)."},
    }
)
