"""Toolchain health & opam-switch detection — backing logic for the
``rocq_health`` and ``rocq_switch`` tools.

This module is deliberately *generic*: it does not assume any particular
opam layout.  It reports the toolchain the running server actually
resolves (the ``coqc`` / ``pet`` binaries on the server process's
``PATH``) and, when the install looks like opam, the active switch.  When
it does not look like opam (a system install, a Nix store path, a
hand-built ``coqc``), it degrades gracefully: the binary paths and
versions are still reported and ``switch_source`` is ``"unknown"``.

The MCP tool wrappers (``rocq_health`` / ``rocq_switch``) live in
:mod:`rocq_mcp.server`; this module provides the snapshot builder and the
switch-mutation helper they delegate to.

Why this matters: an MCP server is a long-lived subprocess.  It inherits
its ``PATH`` / opam environment from whatever launched it (e.g. an
``opam exec --switch=<name> -- ...`` wrapper in the MCP client config),
*not* from the operator's interactive shell.  So the switch the server
runs on can silently differ from the shell's current switch.  These tools
let an agent see — and, via ``rocq_switch``, change — that binding.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from typing import Any

import rocq_mcp as _rocq_mcp  # for __version__
import rocq_mcp.server as _server

# Short per-probe budget for the ``coqc --print-version`` / ``pet --version``
# subprocess.  These are fast (tens of ms); the cap is pure insurance against
# a wedged binary so a health check never hangs the event loop's worker thread.
_VERSION_TIMEOUT: float = 5.0

# Budget for ``opam env`` / ``opam switch list`` invocations in rocq_switch.
_OPAM_TIMEOUT: float = 15.0

# Parses one ``KEY='VALUE'; export KEY;`` line of ``opam env --shell=sh``
# output.  opam single-quotes every value and escapes embedded single
# quotes as the POSIX idiom ``'\''`` (close-quote, escaped-quote, reopen).
_OPAM_ENV_LINE = re.compile(r"^(\w+)='(.*)'; export \1;?\s*$")

# Environment keys opam may emit that we propagate into the live process so a
# respawned pet / next coqc invocation resolves the new switch.  Anything opam
# prints that is not in this set is ignored (defensive: we never blindly trust
# arbitrary KEY=VALUE pairs into our own environment).
#
# ``OPAM_LAST_ENV`` is the breadcrumb opam writes pointing at the env it last
# materialised.  It MUST be propagated: on a *subsequent* ``opam env --switch``
# call, opam reads it from our environment to know which switch's ``bin`` to
# *remove* from ``PATH``.  Drop it and repeated rocq_switch calls leave each
# prior switch's ``bin`` stranded on ``PATH``, so ``coqc`` can resolve to a
# stale switch — the exact wrong-toolchain failure this module exists to catch.
_SWITCH_ENV_KEYS: frozenset[str] = frozenset(
    {
        "PATH",
        "OPAMSWITCH",
        "OPAM_SWITCH_PREFIX",
        "OPAM_LAST_ENV",
        "CAML_LD_LIBRARY_PATH",
        "OCAML_TOPLEVEL_PATH",
        "OCAMLTOP_INCLUDE_PATH",
        "MANPATH",
        "PKG_CONFIG_PATH",
    }
)


# ---------------------------------------------------------------------------
# Binary + version resolution
# ---------------------------------------------------------------------------


def _resolve_binary(name: str) -> str | None:
    """Resolve *name* to the absolute path the server would actually run.

    ``shutil.which`` handles both bare names (searched on ``PATH``) and
    explicit paths (returned if executable), which is exactly the
    resolution ``coqc`` / ``pet`` undergo at call time.  Returns ``None``
    when nothing resolves.
    """
    return shutil.which(name)


def _binary_version(path: str | None, args: list[str]) -> str | None:
    """First line of ``<path> <args>``, or ``None`` if it fails/blocks.

    Best-effort: any OSError / non-zero exit / timeout yields ``None`` so a
    health probe never raises.  ``coqc --print-version`` and
    ``pet --version`` both return promptly; the timeout is insurance.
    """
    if not path:
        return None
    try:
        proc = subprocess.run(
            [path, *args],
            capture_output=True,
            text=True,
            timeout=_VERSION_TIMEOUT,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    out = (proc.stdout or proc.stderr or "").strip()
    if not out:
        return None
    return out.splitlines()[0].strip()


# ---------------------------------------------------------------------------
# Switch detection (generic — opam, local switch, or non-opam)
# ---------------------------------------------------------------------------


def _switch_from_prefix(
    prefix: str, *, source: str, name_hint: str | None
) -> dict[str, Any]:
    """Build a switch descriptor from an ``OPAM_SWITCH_PREFIX``-style path.

    A prefix ending in ``_opam`` is a *local* (project-local) switch; its
    human name is the containing project directory.  Otherwise it is a
    global switch and the prefix basename is the switch name.  *name_hint*
    (typically ``$OPAMSWITCH``) wins when present — for local switches opam
    sets it to the full project path, which is the canonical handle.
    """
    prefix = prefix.rstrip("/\\")
    base = os.path.basename(prefix)
    is_local = base == "_opam"
    if is_local:
        name = name_hint or os.path.basename(os.path.dirname(prefix)) or prefix
    else:
        name = name_hint or base
    return {
        "switch": name or None,
        "switch_prefix": prefix,
        "switch_is_local": is_local,
        "switch_source": source,
    }


def _switch_from_binary_path(coqc_path: str) -> dict[str, Any] | None:
    """Infer the switch from a resolved ``coqc`` path, or ``None``.

    Recognises the two opam layouts and *only* those, to avoid mislabelling
    a system install (e.g. ``/usr/bin/coqc`` must not report switch
    ``"usr"``):

    - local:  ``<dir>/_opam/bin/coqc``        → local switch ``<dir>``
    - global: ``<opamroot>/<name>/bin/coqc``  where ``<opamroot>`` is named
      ``.opam`` or equals ``$OPAMROOT`` → global switch ``<name>``

    Anything else returns ``None`` (caller reports ``switch_source:
    "unknown"``).
    """
    bindir = os.path.dirname(coqc_path)
    if os.path.basename(bindir) != "bin":
        return None
    prefix = os.path.dirname(bindir)
    if os.path.basename(prefix) == "_opam":
        return _switch_from_prefix(prefix, source="binary_path", name_hint=None)
    root = os.path.dirname(prefix)
    opamroot = os.environ.get("OPAMROOT")
    looks_like_opam = os.path.basename(root) == ".opam" or (
        opamroot is not None and os.path.realpath(root) == os.path.realpath(opamroot)
    )
    if looks_like_opam:
        return _switch_from_prefix(prefix, source="binary_path", name_hint=None)
    return None


def _detect_switch(coqc_path: str | None) -> dict[str, Any]:
    """Detect the active switch, preferring opam's own env over path-sniffing.

    ``$OPAM_SWITCH_PREFIX`` is authoritative when present — opam sets it via
    ``eval $(opam env)`` / ``opam exec``.  Otherwise we infer from the
    resolved ``coqc`` path.  Falls back to a ``"unknown"`` descriptor for
    non-opam installs, where the binary paths/versions still tell the agent
    everything actionable.
    """
    prefix = os.environ.get("OPAM_SWITCH_PREFIX")
    name_hint = os.environ.get("OPAMSWITCH")
    if prefix:
        return _switch_from_prefix(prefix, source="opam_env", name_hint=name_hint)
    if coqc_path:
        parsed = _switch_from_binary_path(coqc_path)
        if parsed is not None:
            return parsed
    return {
        "switch": None,
        "switch_prefix": None,
        "switch_is_local": False,
        "switch_source": "unknown",
    }


# ---------------------------------------------------------------------------
# Health snapshot
# ---------------------------------------------------------------------------


def build_health_snapshot(lifespan_state: dict[str, Any]) -> dict[str, Any]:
    """Build the response dict for the ``rocq_health`` tool.

    Read-only: never spawns pet (mirrors ``rocq_diag``).  Reports the
    toolchain the server actually resolves plus a coarse ``ok`` health
    verdict and human-readable ``warnings``.  See ``rocq_health`` for the
    output schema.
    """
    coqc_path = _resolve_binary(_server.ROCQ_COQC_BINARY)
    pet_path = _resolve_binary("pet")

    try:
        import pytanque  # noqa: F401

        pytanque_importable = True
    except ImportError:
        pytanque_importable = False

    client = lifespan_state.get("pet_client")
    pet_running = client is not None and getattr(client, "process", None) is not None
    pet_pid = client.process.pid if pet_running else None

    switch = _detect_switch(coqc_path)

    warnings: list[str] = []
    if coqc_path is None:
        warnings.append(
            f"coqc binary {_server.ROCQ_COQC_BINARY!r} not found on PATH — "
            "compilation tools will fail. Check the switch / ROCQ_COQC_BINARY."
        )
    if pet_path is None:
        warnings.append(
            "`pet` not found on PATH — interactive tools and proof-state "
            'enrichment will return reason="unavailable".'
        )
    if not pytanque_importable:
        warnings.append(
            "the pytanque Python binding is not importable — interactive "
            'tools will return reason="unavailable".'
        )
    if switch["switch_source"] == "unknown":
        warnings.append(
            "could not identify an opam switch (non-opam install or "
            "unrecognised layout); reporting resolved binary paths instead."
        )

    # "ok" = the server can do its core job: coqc resolves.  Interactive
    # capability (pet + pytanque) is reported separately so a coqc-only
    # deployment still reads as healthy.
    ok = coqc_path is not None

    return {
        "success": True,
        "ok": ok,
        "server_version": _rocq_mcp.__version__,
        "switch": switch["switch"],
        "switch_prefix": switch["switch_prefix"],
        "switch_is_local": switch["switch_is_local"],
        "switch_source": switch["switch_source"],
        "toolchain": {
            "coqc": {
                "path": coqc_path,
                "version": _binary_version(coqc_path, ["--print-version"]),
            },
            "pet": {
                "path": pet_path,
                "version": _binary_version(pet_path, ["--version"]),
                "pytanque_importable": pytanque_importable,
            },
        },
        "pet": {"running": pet_running, "pid": pet_pid},
        "warnings": warnings,
    }


# ---------------------------------------------------------------------------
# Switch mutation (rocq_switch)
# ---------------------------------------------------------------------------


def _parse_opam_env(sh_output: str) -> dict[str, str]:
    """Parse ``opam env --shell=sh`` export lines into a ``{KEY: VALUE}`` dict.

    Keeps only keys in :data:`_SWITCH_ENV_KEYS` and unescapes the POSIX
    ``'\\''`` single-quote idiom opam emits.  Lines that do not match the
    ``KEY='VALUE'; export KEY;`` shape are ignored.
    """
    env: dict[str, str] = {}
    for line in sh_output.splitlines():
        m = _OPAM_ENV_LINE.match(line.strip())
        if not m:
            continue
        key, value = m.group(1), m.group(2)
        if key not in _SWITCH_ENV_KEYS:
            continue
        env[key] = value.replace("'\\''", "'")
    return env


def compute_switch_env(name: str) -> tuple[dict[str, str] | None, str | None]:
    """Resolve the environment for opam switch *name* via ``opam env``.

    Returns ``(env, None)`` on success (``env`` is the ``{KEY: VALUE}`` set
    to apply to the process) or ``(None, error_message)`` on failure
    (opam missing, switch not installed, unparseable output).
    """
    try:
        proc = subprocess.run(
            ["opam", "env", "--switch", name, "--set-switch", "--shell=sh"],
            capture_output=True,
            text=True,
            timeout=_OPAM_TIMEOUT,
        )
    except FileNotFoundError:
        return None, (
            "`opam` not found on PATH; cannot change switch. rocq_switch "
            "requires an opam-managed toolchain."
        )
    except subprocess.SubprocessError as exc:
        return None, f"`opam env` failed: {exc}"

    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()
        return None, (
            f"opam could not select switch {name!r} "
            f"(exit {proc.returncode}): {detail}"
        )

    env = _parse_opam_env(proc.stdout or "")
    if "PATH" not in env or "OPAM_SWITCH_PREFIX" not in env:
        return None, (
            f"`opam env --switch {name}` returned no usable PATH / "
            "OPAM_SWITCH_PREFIX; cannot change switch."
        )
    return env, None


def list_switches() -> list[str] | None:
    """Return installed opam switch names, or ``None`` if opam is unavailable."""
    try:
        proc = subprocess.run(
            ["opam", "switch", "list", "--short"],
            capture_output=True,
            text=True,
            timeout=_OPAM_TIMEOUT,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    return [ln.strip() for ln in (proc.stdout or "").splitlines() if ln.strip()]
