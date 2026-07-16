"""MCP surface contract — instructions, annotations, tool inventory.

These tests pin the protocol-visible surface of the server via a real
in-memory MCP session (full serialization path), so a regression in what
clients actually see fails here even when direct-call unit tests pass.
"""

from __future__ import annotations

import pytest

# The canonical tool inventory.  Additions/removals must update this set
# (and the annotations table below) deliberately.
EXPECTED_TOOLS = {
    "rocq_compile",
    "rocq_compile_file",
    "rocq_verify",
    "rocq_query",
    "rocq_assumptions",
    "rocq_toc",
    "rocq_notations",
    "rocq_start",
    "rocq_step_multi",
    "rocq_check",
    "rocq_diag",
    "rocq_health",
    "rocq_switch",
}

# (readOnlyHint, destructiveHint, idempotentHint) per tool.  A ``None``
# destructiveHint is fine for read-only tools (the hint is only
# meaningful when readOnlyHint is False).
EXPECTED_ANNOTATIONS = {
    "rocq_compile": (False, False, True),
    "rocq_compile_file": (False, False, True),
    "rocq_verify": (False, False, True),
    "rocq_query": (True, None, True),
    "rocq_assumptions": (True, None, True),
    "rocq_toc": (True, None, True),
    "rocq_notations": (True, None, True),
    "rocq_start": (False, True, False),
    "rocq_step_multi": (True, None, True),
    "rocq_check": (False, False, False),
    "rocq_diag": (True, None, True),
    "rocq_health": (True, None, True),
    "rocq_switch": (False, True, True),
}


@pytest.fixture(scope="module")
async def surface():
    """One in-memory session's view of the surface: (instructions, version, tools)."""
    from fastmcp import Client

    from rocq_mcp.server import mcp

    async with Client(mcp) as client:
        init = client.initialize_result
        tools = {t.name: t for t in await client.list_tools()}
        return init.instructions, init.serverInfo.version, tools


class TestInstructions:
    async def test_present_and_within_budget(self, surface):
        instructions, _, _ = surface
        assert instructions, "server must declare instructions"
        # Instructions are always-visible context; keep them lean.
        assert len(instructions) < 2_200, len(instructions)

    async def test_carry_the_load_bearing_contracts(self, surface):
        instructions, _, _ = surface
        # The core loop, the state rule, and the failure envelope must be
        # visible even when tool descriptions are deferred.
        for needle in (
            "rocq_start",
            "rocq_check",
            "from_state",
            "reason",
            "tactic_failed",
            "pet_restarted",
        ):
            assert needle in instructions, f"instructions lost {needle!r}"

    async def test_version_is_published(self, surface):
        _, version, _ = surface
        assert version and version != "0.0.0+unknown"


class TestToolInventory:
    async def test_exact_tool_set(self, surface):
        _, _, tools = surface
        assert set(tools) == EXPECTED_TOOLS

    async def test_every_tool_has_description_and_title(self, surface):
        _, _, tools = surface
        for name, tool in tools.items():
            assert tool.description, f"{name} has no description"
            assert tool.annotations is not None, f"{name} has no annotations"
            assert tool.annotations.title, f"{name} has no title"


class TestAnnotations:
    async def test_hints_match_the_table(self, surface):
        _, _, tools = surface
        for name, (read_only, destructive, idempotent) in EXPECTED_ANNOTATIONS.items():
            ann = tools[name].annotations
            assert ann.readOnlyHint is read_only, f"{name}.readOnlyHint"
            assert ann.destructiveHint is destructive, f"{name}.destructiveHint"
            assert ann.idempotentHint is idempotent, f"{name}.idempotentHint"

    async def test_nothing_claims_open_world(self, surface):
        _, _, tools = surface
        for name, tool in tools.items():
            assert tool.annotations.openWorldHint is False, name

    async def test_switch_requires_user_interaction(self, surface):
        _, _, tools = surface
        meta = tools["rocq_switch"].meta or {}
        assert meta.get("anthropic/requiresUserInteraction") is True
