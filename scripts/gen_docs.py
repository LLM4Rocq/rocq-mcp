#!/usr/bin/env python3
"""Regenerate the README tools table from the live MCP registry.

Generation direction is code -> README, never hand-edit inside the
markers.  Run ``gen_docs.py --check`` (exit 1 on diff) — e.g. as a CI
step — to catch drift from the actual tool surface.
"""

from __future__ import annotations

import argparse
import asyncio
import re
import sys
from pathlib import Path

README = Path(__file__).resolve().parent.parent / "README.md"
BEGIN = "<!-- BEGIN GENERATED: tools (scripts/gen_docs.py) -->"
END = "<!-- END GENERATED: tools -->"


async def render_table() -> str:
    from fastmcp import Client

    from rocq_mcp.server import mcp

    async with Client(mcp) as client:
        tools = await client.list_tools()

    lines = ["| Tool | What it does |", "|------|--------------|"]
    for tool in tools:
        first_sentence = (tool.description or "").strip().splitlines()[0].strip()
        lines.append(f"| **`{tool.name}`** | {first_sentence} |")
    return "\n".join(lines)


def splice(readme_text: str, table: str) -> str:
    pattern = re.compile(re.escape(BEGIN) + r".*?" + re.escape(END), flags=re.DOTALL)
    if not pattern.search(readme_text):
        raise SystemExit(f"README is missing the generation markers {BEGIN!r}")
    return pattern.sub(f"{BEGIN}\n{table}\n{END}", readme_text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="exit 1 if the README table is out of date (no write)",
    )
    args = parser.parse_args()

    table = asyncio.run(render_table())
    current = README.read_text(encoding="utf-8")
    updated = splice(current, table)

    if args.check:
        if updated != current:
            print(
                "README tools table is out of date. "
                "Run: uv run python scripts/gen_docs.py",
                file=sys.stderr,
            )
            return 1
        print("README tools table is up to date.")
        return 0

    README.write_text(updated, encoding="utf-8")
    print("README tools table regenerated.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
