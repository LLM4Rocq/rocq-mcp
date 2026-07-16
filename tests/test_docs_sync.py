"""Anti-drift invariants between code and documentation.

The README's tools table is generated (scripts/gen_docs.py --check in
CI); these tests cover the drift classes generation can't:
- every registered tool is mentioned in the README and the guides
- every ROCQ_* env var read in src/ is documented in the README (and
  vice versa)
- the failure reasons documented in README/guides equal the taxonomy
"""

from __future__ import annotations

import re
from pathlib import Path

from rocq_mcp import taxonomy

REPO = Path(__file__).resolve().parent.parent
README = (REPO / "README.md").read_text(encoding="utf-8")
GUIDES = {
    p.name: p.read_text(encoding="utf-8")
    for p in (REPO / "src/rocq_mcp/guides").glob("*.md")
}
ALL_GUIDE_TEXT = "\n".join(GUIDES.values())


def _tool_names() -> set[str]:
    import asyncio

    from fastmcp import Client

    from rocq_mcp.server import mcp

    async def _list() -> set[str]:

        async with Client(mcp) as client:
            return {t.name for t in await client.list_tools()}

    return asyncio.run(_list())


def test_every_tool_is_documented_in_readme_and_guides():
    tools = _tool_names()
    for name in tools:
        assert name in README, f"{name} missing from README"
        assert name in ALL_GUIDE_TEXT, f"{name} missing from all guides"


def test_env_vars_in_code_match_readme_table():
    code_vars: set[str] = set()
    for py in (REPO / "src/rocq_mcp").rglob("*.py"):
        code_vars |= set(
            re.findall(r"os\.environ\.get\(\s*[\"'](ROCQ_[A-Z_]+)[\"']", py.read_text())
        )
        code_vars |= set(
            re.findall(
                r"[\"'](ROCQ_[A-Z_]+)[\"']\s*(?:in|not in)\s*os\.environ",
                py.read_text(),
            )
        )
    documented = set(re.findall(r"^\|\s*`(ROCQ_[A-Z_]+)`", README, flags=re.MULTILINE))

    assert code_vars - documented == set(), (
        f"env vars read in code but missing from the README table: "
        f"{sorted(code_vars - documented)}"
    )
    assert documented - code_vars == set(), (
        f"env vars documented in README but not read anywhere in src/: "
        f"{sorted(documented - code_vars)}"
    )


def test_documented_reasons_equal_taxonomy():
    expected = {str(r) for r in taxonomy.FailureReason}
    # The README lists the full taxonomy in the Agent documentation section.
    for reason in expected:
        assert f"`{reason}`" in README, f"README does not document reason {reason!r}"
    # The failures guide has a table row per reason.
    failures = GUIDES["failures.md"]
    for reason in expected:
        assert (
            f"`{reason}`" in failures
        ), f"failures guide does not document reason {reason!r}"


def test_guides_exist_and_are_nonempty():
    assert set(GUIDES) == {
        "workflows.md",
        "failures.md",
        "concurrency.md",
        "responses.md",
    }
    for name, text in GUIDES.items():
        assert len(text) > 1_000, f"{name} suspiciously small"
