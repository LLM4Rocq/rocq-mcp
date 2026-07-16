"""Output-schema declarations for the pilot tools + notification helpers."""

from __future__ import annotations

import json
from unittest.mock import MagicMock

import pytest

from rocq_mcp import schemas, taxonomy

PILOT_TOOLS = {
    "rocq_check": schemas.CHECK_OUTPUT_SCHEMA,
    "rocq_step_multi": schemas.STEP_MULTI_OUTPUT_SCHEMA,
    "rocq_compile_file": schemas.COMPILE_FILE_OUTPUT_SCHEMA,
    "rocq_search": schemas.SEARCH_OUTPUT_SCHEMA,
}


class TestSchemaShape:
    def test_permissive_union(self):
        """Only success is required; extra keys always allowed — the
        schema must accept success shapes, failure envelopes, and any
        optional enrichment key."""
        for name, schema in PILOT_TOOLS.items():
            assert schema["required"] == ["success"], name
            assert schema["additionalProperties"] is True, name
            assert "error" in schema["properties"], name
            assert "reason" in schema["properties"], name

    def test_reason_enum_matches_taxonomy(self):
        expected = sorted(str(r) for r in taxonomy.FailureReason)
        for name, schema in PILOT_TOOLS.items():
            assert schema["properties"]["reason"]["enum"] == expected, name

    def test_token_budget(self):
        for name, schema in PILOT_TOOLS.items():
            size = len(json.dumps(schema))
            assert size <= 1_000, f"{name} schema is {size} chars"


class TestSchemasOverTheWire:
    async def test_declared_and_failure_envelope_round_trips(self):
        from fastmcp import Client

        from rocq_mcp.server import mcp

        async with Client(mcp) as client:
            tools = {t.name: t for t in await client.list_tools()}
            for name in PILOT_TOOLS:
                declared = tools[name].outputSchema
                assert declared is not None, name
                assert declared["required"] == ["success"], name

            # A validation failure must serialize cleanly through the
            # declared schema (structured content is not rejected).
            result = await client.call_tool("rocq_search", {"pattern": ""})
            payload = (
                result.data
                if isinstance(result.data, dict)
                else json.loads(result.content[0].text)
            )
            assert payload["success"] is False
            assert payload["reason"] == "validation"


class TestNotifyHelpers:
    def test_notify_is_a_noop_outside_a_request(self):
        """No ambient MCP context (unit tests, direct calls): the
        helpers must silently do nothing."""
        from rocq_mcp import envelope as env

        env._progress({}, 1, 2, "msg")
        env._log_info({}, "hello")
        env._log_warning(None, "hello")

    def test_notify_never_raises_even_if_factory_explodes(self):
        from rocq_mcp import envelope as env

        def bomb(ctx):
            raise RuntimeError("factory bug")

        env._notify({}, bomb)  # must not raise

    def test_walker_progress_callback_is_fault_isolated(self):
        """A raising progress callback must not break the walk loop."""
        from rocq_mcp.proof_walk import collect_file_errors

        pet = MagicMock()
        pet.toc.return_value = []  # no named entries -> single fallback chunk
        pet.get_root_state.return_value = MagicMock()
        pet.run.return_value = MagicMock()

        calls: list[tuple[int, int]] = []

        def bad_progress(i, n):
            calls.append((i, n))
            raise RuntimeError("ui exploded")

        # The progress bomb must be swallowed by the walk loop.
        try:
            collect_file_errors(
                file="f.v",
                source="Theorem t : True. Proof. exact I. Qed.",
                pet=pet,
                per_call_timeout=1.0,
                max_errors=5,
                progress=bad_progress,
            )
        except RuntimeError as e:  # pragma: no cover - would be the bug
            pytest.fail(f"progress callback escaped the walk: {e}")
        assert calls, "progress callback was never invoked"
