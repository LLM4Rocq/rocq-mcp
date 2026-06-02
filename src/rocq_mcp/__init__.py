"""rocq-mcp — Coq/Rocq verification tools exposed as an MCP server."""

from importlib.metadata import PackageNotFoundError, version

try:
    __version__ = version("rocq-mcp")
except PackageNotFoundError:
    __version__ = "0.0.0+unknown"
