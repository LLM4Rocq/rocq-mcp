"""Tests for the ``rocq_health`` and ``rocq_switch`` toolchain tools.

Two concerns are exercised here:

1. *Generic* switch detection in :mod:`rocq_mcp.health` — global opam
   switches, project-local ``_opam`` switches, and the non-opam fallback
   (which must NOT mislabel ``/usr/bin/coqc`` as switch ``"usr"``).
2. The MCP wrappers: ``rocq_health`` (read-only snapshot) and
   ``rocq_switch`` (env mutation + pet invalidation), with the real opam /
   subprocess boundary mocked.
"""

from __future__ import annotations

import os
import subprocess
import sys
import types

import pytest

import rocq_mcp.health as health
import rocq_mcp.server as _server
from rocq_mcp.health import (
    _detect_switch,
    _parse_opam_env,
    _switch_from_binary_path,
    _switch_from_prefix,
    build_health_snapshot,
)
from rocq_mcp.server import rocq_health, rocq_switch
from tests.conftest import (
    _MockContext,
    add_mock_state,
    make_lifespan_state,
    mock_pet,
)


@pytest.fixture(autouse=True)
def _reset_pet_state(monkeypatch):
    """Reset pet lock between tests (rocq_switch invalidates pet)."""
    import threading

    monkeypatch.setattr(_server, "_pet_lock", threading.Lock())
    yield


@pytest.fixture
def _restore_environ():
    """Snapshot and restore ``os.environ`` (rocq_switch mutates it)."""
    saved = dict(os.environ)
    yield
    os.environ.clear()
    os.environ.update(saved)


# ---------------------------------------------------------------------------
# Switch detection — pure, env-independent
# ---------------------------------------------------------------------------


def test_switch_from_prefix_global():
    d = _switch_from_prefix("/home/u/.opam/rocq9", source="opam_env", name_hint="rocq9")
    assert d == {
        "switch": "rocq9",
        "switch_prefix": "/home/u/.opam/rocq9",
        "switch_is_local": False,
        "switch_source": "opam_env",
    }


def test_switch_from_prefix_local_uses_project_dir():
    d = _switch_from_prefix("/work/proj/_opam", source="binary_path", name_hint=None)
    assert d["switch_is_local"] is True
    assert d["switch"] == "proj"
    assert d["switch_prefix"] == "/work/proj/_opam"


def test_switch_from_prefix_name_hint_wins():
    # opam sets OPAMSWITCH to the full project path for local switches.
    d = _switch_from_prefix(
        "/work/proj/_opam", source="opam_env", name_hint="/work/proj"
    )
    assert d["switch"] == "/work/proj"


def test_switch_from_binary_path_global(monkeypatch):
    monkeypatch.delenv("OPAMROOT", raising=False)
    d = _switch_from_binary_path("/home/u/.opam/rocq9/bin/coqc")
    assert d is not None
    assert d["switch"] == "rocq9"
    assert d["switch_source"] == "binary_path"
    assert d["switch_is_local"] is False


def test_switch_from_binary_path_local():
    d = _switch_from_binary_path("/work/proj/_opam/bin/coqc")
    assert d is not None
    assert d["switch_is_local"] is True
    assert d["switch"] == "proj"


def test_switch_from_binary_path_honours_opamroot(monkeypatch):
    # A non-default OPAMROOT location is still recognised as opam.
    monkeypatch.setenv("OPAMROOT", "/custom/opamroot")
    d = _switch_from_binary_path("/custom/opamroot/myswitch/bin/coqc")
    assert d is not None
    assert d["switch"] == "myswitch"


def test_switch_from_binary_path_non_opam_returns_none(monkeypatch):
    monkeypatch.delenv("OPAMROOT", raising=False)
    # /usr/bin/coqc must NOT be reported as switch "usr".
    assert _switch_from_binary_path("/usr/bin/coqc") is None
    # bindir not named "bin" — unknown layout.
    assert _switch_from_binary_path("/opt/coq/coqc") is None


def test_detect_switch_prefers_opam_env(monkeypatch):
    monkeypatch.setenv("OPAM_SWITCH_PREFIX", "/home/u/.opam/myswitch")
    monkeypatch.setenv("OPAMSWITCH", "myswitch")
    # Binary path disagrees; env must win.
    d = _detect_switch("/elsewhere/.opam/other/bin/coqc")
    assert d["switch"] == "myswitch"
    assert d["switch_source"] == "opam_env"


def test_detect_switch_falls_back_to_binary(monkeypatch):
    monkeypatch.delenv("OPAM_SWITCH_PREFIX", raising=False)
    monkeypatch.delenv("OPAMSWITCH", raising=False)
    monkeypatch.delenv("OPAMROOT", raising=False)
    d = _detect_switch("/home/u/.opam/rocq9/bin/coqc")
    assert d["switch"] == "rocq9"
    assert d["switch_source"] == "binary_path"


def test_detect_switch_unknown_for_non_opam(monkeypatch):
    monkeypatch.delenv("OPAM_SWITCH_PREFIX", raising=False)
    monkeypatch.delenv("OPAMSWITCH", raising=False)
    monkeypatch.delenv("OPAMROOT", raising=False)
    d = _detect_switch("/usr/bin/coqc")
    assert d["switch"] is None
    assert d["switch_source"] == "unknown"
    # No coqc resolved at all → still graceful.
    assert _detect_switch(None)["switch_source"] == "unknown"


# ---------------------------------------------------------------------------
# opam env parsing
# ---------------------------------------------------------------------------


def test_parse_opam_env_filters_to_known_keys():
    sh = (
        "OPAMSWITCH='rocq9'; export OPAMSWITCH;\n"
        "OPAM_SWITCH_PREFIX='/h/.opam/rocq9'; export OPAM_SWITCH_PREFIX;\n"
        "PATH='/h/.opam/rocq9/bin:/usr/bin'; export PATH;\n"
        "OPAM_LAST_ENV='/h/.opam/.last-env/x'; export OPAM_LAST_ENV;\n"
    )
    env = _parse_opam_env(sh)
    assert env["OPAMSWITCH"] == "rocq9"
    assert env["OPAM_SWITCH_PREFIX"] == "/h/.opam/rocq9"
    assert env["PATH"] == "/h/.opam/rocq9/bin:/usr/bin"
    # OPAM_LAST_ENV is the breadcrumb opam needs on the NEXT switch to strip
    # the prior switch's bin from PATH — it MUST be propagated, not dropped.
    assert env["OPAM_LAST_ENV"] == "/h/.opam/.last-env/x"


def test_opam_last_env_is_propagated_to_strip_stale_path():
    # Regression for the PATH-leak bug: repeated rocq_switch calls relied on
    # OPAM_LAST_ENV to let opam clean the previous switch's bin off PATH.
    assert "OPAM_LAST_ENV" in health._SWITCH_ENV_KEYS


def test_parse_opam_env_drops_unknown_keys():
    sh = "OPAMROOT='/h/.opam'; export OPAMROOT;\n"  # not in the curated set
    assert "OPAMROOT" not in _parse_opam_env(sh)


def test_parse_opam_env_unescapes_single_quote():
    # opam emits embedded single quotes as the POSIX '\'' idiom.
    sh = "MANPATH='/x'\\''y'; export MANPATH;"
    env = _parse_opam_env(sh)
    assert env["MANPATH"] == "/x'y"


# ---------------------------------------------------------------------------
# build_health_snapshot
# ---------------------------------------------------------------------------


def test_build_health_snapshot_schema(monkeypatch):
    monkeypatch.setattr(health, "_resolve_binary", lambda n: f"/sw/bin/{n}")
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "ver")
    monkeypatch.setenv("OPAM_SWITCH_PREFIX", "/h/.opam/myswitch")
    monkeypatch.setenv("OPAMSWITCH", "myswitch")
    # Make the pytanque import deterministic so `warnings == []` does not
    # depend on whether the binding happens to be installed in the runner.
    monkeypatch.setitem(sys.modules, "pytanque", types.ModuleType("pytanque"))

    snap = build_health_snapshot({"pet_client": None})

    assert snap["success"] is True
    assert snap["ok"] is True
    assert snap["switch"] == "myswitch"
    assert snap["switch_source"] == "opam_env"
    assert snap["switch_is_local"] is False
    assert snap["toolchain"]["coqc"]["path"] == "/sw/bin/coqc"
    assert snap["toolchain"]["coqc"]["version"] == "ver"
    assert snap["toolchain"]["pet"]["path"] == "/sw/bin/pet"
    assert snap["pet"] == {"running": False, "pid": None}
    # coqc + pet resolved and pytanque importable (it's a dependency).
    assert snap["warnings"] == []


def test_build_health_snapshot_coqc_missing_is_not_ok(monkeypatch):
    monkeypatch.setattr(health, "_resolve_binary", lambda n: None)
    monkeypatch.setattr(health, "_binary_version", lambda p, a: None)
    snap = build_health_snapshot({"pet_client": None})
    assert snap["ok"] is False
    assert any("coqc" in w for w in snap["warnings"])


def test_build_health_snapshot_reports_running_pet(monkeypatch):
    monkeypatch.setattr(health, "_resolve_binary", lambda n: f"/x/{n}")
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "v")
    snap = build_health_snapshot({"pet_client": mock_pet(pid=4242)})
    assert snap["pet"] == {"running": True, "pid": 4242}


def test_build_health_snapshot_unknown_switch_warns(monkeypatch):
    monkeypatch.setattr(health, "_resolve_binary", lambda n: "/usr/bin/coqc")
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "v")
    monkeypatch.delenv("OPAM_SWITCH_PREFIX", raising=False)
    monkeypatch.delenv("OPAMSWITCH", raising=False)
    monkeypatch.delenv("OPAMROOT", raising=False)
    snap = build_health_snapshot({"pet_client": None})
    assert snap["switch"] is None
    assert snap["switch_source"] == "unknown"
    assert any("opam switch" in w for w in snap["warnings"])


# ---------------------------------------------------------------------------
# rocq_health tool wrapper
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
async def test_rocq_health_no_context():
    r = await rocq_health(ctx=None)
    assert r["success"] is False


@pytest.mark.asyncio
async def test_rocq_health_returns_snapshot(monkeypatch):
    monkeypatch.setattr(health, "_resolve_binary", lambda n: f"/x/{n}")
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "v")
    ctx = _MockContext(make_lifespan_state(full=True))
    r = await rocq_health(ctx=ctx)
    assert r["success"] is True
    assert "switch" in r
    assert "toolchain" in r


# ---------------------------------------------------------------------------
# rocq_switch tool wrapper
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
async def test_rocq_switch_requires_name():
    ctx = _MockContext(make_lifespan_state(full=True))
    r = await rocq_switch(name="", ctx=ctx)
    assert r["success"] is False
    assert r["reason"] == "validation"


@pytest.mark.asyncio
async def test_rocq_switch_no_context():
    r = await rocq_switch(name="rocq9", ctx=None)
    assert r["success"] is False


@pytest.mark.asyncio
async def test_rocq_switch_unknown_switch_lists_available(monkeypatch):
    # rocq_switch resolves compute_switch_env / list_switches via the *server*
    # module binding (server.py does `from rocq_mcp.health import ...`), so the
    # patch must target _server — patching health.* would have no effect.
    monkeypatch.setattr(
        _server, "compute_switch_env", lambda n: (None, "not installed")
    )
    monkeypatch.setattr(_server, "list_switches", lambda: ["a", "b"])
    ctx = _MockContext(make_lifespan_state(full=True))
    r = await rocq_switch(name="nope", ctx=ctx)
    assert r["success"] is False
    # A typo'd / uninstalled name is a name-resolution failure, not a
    # validation (input-shape) error — matches rocq_start's convention.
    assert r["reason"] == "not_found"
    assert r["available_switches"] == ["a", "b"]


@pytest.mark.asyncio
async def test_rocq_switch_opam_unavailable_is_validation(monkeypatch):
    # opam not on PATH: list_switches() returns None, so the name cannot be
    # classified — no available_switches, and reason stays "validation".
    monkeypatch.setattr(
        _server, "compute_switch_env", lambda n: (None, "opam not found")
    )
    monkeypatch.setattr(_server, "list_switches", lambda: None)
    ctx = _MockContext(make_lifespan_state(full=True))
    r = await rocq_switch(name="rocq9", ctx=ctx)
    assert r["success"] is False
    assert r["reason"] == "validation"
    assert "available_switches" not in r


@pytest.mark.asyncio
async def test_rocq_switch_installed_name_that_fails_omits_available(monkeypatch):
    # Name IS in the installed list but resolution failed (transient): do not
    # attach a confusing "it's right there" available_switches list.
    monkeypatch.setattr(_server, "compute_switch_env", lambda n: (None, "transient"))
    monkeypatch.setattr(_server, "list_switches", lambda: ["rocq9", "target"])
    ctx = _MockContext(make_lifespan_state(full=True))
    r = await rocq_switch(name="rocq9", ctx=ctx)
    assert r["success"] is False
    assert r["reason"] == "validation"
    assert "available_switches" not in r


@pytest.mark.asyncio
async def test_rocq_switch_success_applies_env_and_kills_pet(
    monkeypatch, _restore_environ
):
    # Pre-switch state: a known prior switch, so previous_switch is verifiable.
    os.environ["OPAM_SWITCH_PREFIX"] = "/h/.opam/prev"
    os.environ.pop("OPAMSWITCH", None)

    new_env = {
        "PATH": "/h/.opam/target/bin:/usr/bin",
        "OPAMSWITCH": "target",
        "OPAM_SWITCH_PREFIX": "/h/.opam/target",
        "OPAM_LAST_ENV": "/h/.opam/.last-env/target",
    }
    monkeypatch.setattr(_server, "compute_switch_env", lambda n: (new_env, None))
    # Detection after the switch reads os.environ → should report "target".
    monkeypatch.setattr(health, "_resolve_binary", lambda n: f"/h/.opam/target/bin/{n}")
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "v")

    pet = mock_pet(pid=777)
    state = make_lifespan_state(full=True)
    state["pet_client"] = pet
    from rocq_mcp.interactive import _state_table

    add_mock_state(parent_id=None, tactic="intro.")
    assert len(_state_table) == 1

    ctx = _MockContext(state)
    r = await rocq_switch(name="target", ctx=ctx)

    assert r["success"] is True
    assert r["switched"] is True
    assert r["switch"] == "target"
    # previous_switch is captured BEFORE the env mutation.
    assert r["previous_switch"] == "prev"
    assert "note" in r
    # Environment was applied to the live process, including the OPAM_LAST_ENV
    # breadcrumb (the PATH-leak fix).
    assert os.environ["OPAMSWITCH"] == "target"
    assert os.environ["OPAM_SWITCH_PREFIX"] == "/h/.opam/target"
    assert os.environ["OPAM_LAST_ENV"] == "/h/.opam/.last-env/target"
    # pet was invalidated (killed + cleared) and state table flushed.
    assert state["pet_client"] is None
    assert len(_state_table) == 0


@pytest.mark.asyncio
async def test_rocq_switch_success_local_switch(monkeypatch, _restore_environ):
    # End-to-end local (_opam) switch: switch_is_local True, name is the
    # project handle opam reports via OPAMSWITCH.
    new_env = {
        "PATH": "/work/proj/_opam/bin:/usr/bin",
        "OPAMSWITCH": "/work/proj",
        "OPAM_SWITCH_PREFIX": "/work/proj/_opam",
    }
    monkeypatch.setattr(_server, "compute_switch_env", lambda n: (new_env, None))
    monkeypatch.setattr(
        health, "_resolve_binary", lambda n: f"/work/proj/_opam/bin/{n}"
    )
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "v")

    state = make_lifespan_state(full=True)
    state["pet_client"] = mock_pet(pid=999)
    ctx = _MockContext(state)
    r = await rocq_switch(name="/work/proj", ctx=ctx)

    assert r["success"] is True
    assert r["switched"] is True
    assert r["switch_is_local"] is True
    assert r["switch"] == "/work/proj"


# ---------------------------------------------------------------------------
# compute_switch_env (the opam-env resolver behind rocq_switch)
# ---------------------------------------------------------------------------


def _fake_run(returncode=0, stdout="", stderr=""):
    """Return a fake subprocess.run that yields a CompletedProcess-like object."""

    def run(*args, **kwargs):
        return types.SimpleNamespace(
            returncode=returncode, stdout=stdout, stderr=stderr
        )

    return run


def test_compute_switch_env_opam_missing(monkeypatch):
    def raise_fnf(*args, **kwargs):
        raise FileNotFoundError("opam")

    monkeypatch.setattr(health.subprocess, "run", raise_fnf)
    env, err = health.compute_switch_env("rocq9")
    assert env is None
    assert "opam" in err and "not found" in err


def test_compute_switch_env_switch_not_installed(monkeypatch):
    monkeypatch.setattr(
        health.subprocess,
        "run",
        _fake_run(
            returncode=2, stderr="[ERROR] The selected switch nope is not installed."
        ),
    )
    env, err = health.compute_switch_env("nope")
    assert env is None
    assert "exit 2" in err
    assert "not installed" in err  # detail from stderr is surfaced


def test_compute_switch_env_unparseable_output(monkeypatch):
    # returncode 0 but no PATH / OPAM_SWITCH_PREFIX → guarded rejection.
    monkeypatch.setattr(
        health.subprocess,
        "run",
        _fake_run(returncode=0, stdout="OPAMSWITCH='x'; export OPAMSWITCH;\n"),
    )
    env, err = health.compute_switch_env("x")
    assert env is None
    assert "PATH" in err


def test_compute_switch_env_success(monkeypatch):
    out = (
        "PATH='/h/.opam/x/bin:/usr/bin'; export PATH;\n"
        "OPAM_SWITCH_PREFIX='/h/.opam/x'; export OPAM_SWITCH_PREFIX;\n"
        "OPAMSWITCH='x'; export OPAMSWITCH;\n"
        "OPAM_LAST_ENV='/h/.opam/.last-env/x'; export OPAM_LAST_ENV;\n"
    )
    monkeypatch.setattr(health.subprocess, "run", _fake_run(returncode=0, stdout=out))
    env, err = health.compute_switch_env("x")
    assert err is None
    assert env["PATH"] == "/h/.opam/x/bin:/usr/bin"
    assert env["OPAM_SWITCH_PREFIX"] == "/h/.opam/x"
    assert env["OPAM_LAST_ENV"] == "/h/.opam/.last-env/x"


def test_list_switches_returns_none_on_error(monkeypatch):
    def raise_oserror(*args, **kwargs):
        raise OSError("opam missing")

    monkeypatch.setattr(health.subprocess, "run", raise_oserror)
    assert health.list_switches() is None


def test_list_switches_parses_short_output(monkeypatch):
    monkeypatch.setattr(
        health.subprocess, "run", _fake_run(returncode=0, stdout="rocq9\ntarget\n\n")
    )
    assert health.list_switches() == ["rocq9", "target"]


# ---------------------------------------------------------------------------
# _binary_version
# ---------------------------------------------------------------------------


def test_binary_version_first_line_only(monkeypatch):
    monkeypatch.setattr(
        health.subprocess,
        "run",
        _fake_run(returncode=0, stdout="8.20.0 5.2.0\nignored"),
    )
    assert health._binary_version("/x/coqc", ["--print-version"]) == "8.20.0 5.2.0"


def test_binary_version_falls_back_to_stderr(monkeypatch):
    # Some coqc/pet builds print version info to stderr.
    monkeypatch.setattr(
        health.subprocess,
        "run",
        _fake_run(returncode=0, stdout="", stderr="ver on stderr"),
    )
    assert health._binary_version("/x/pet", ["--version"]) == "ver on stderr"


def test_binary_version_ignores_nonzero_exit(monkeypatch):
    # Intentional: no returncode check — first output line is still returned.
    monkeypatch.setattr(
        health.subprocess, "run", _fake_run(returncode=3, stdout="L1\n")
    )
    assert health._binary_version("/x/coqc", ["--version"]) == "L1"


def test_binary_version_timeout_returns_none(monkeypatch):
    def raise_timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(cmd="coqc", timeout=5)

    monkeypatch.setattr(health.subprocess, "run", raise_timeout)
    assert health._binary_version("/x/coqc", ["--version"]) is None


def test_binary_version_none_path_skips_subprocess():
    assert health._binary_version(None, ["--version"]) is None


def test_build_health_snapshot_pytanque_missing_warns(monkeypatch):
    monkeypatch.setattr(health, "_resolve_binary", lambda n: f"/x/{n}")
    monkeypatch.setattr(health, "_binary_version", lambda p, a: "v")
    monkeypatch.setenv("OPAM_SWITCH_PREFIX", "/h/.opam/x")
    # sys.modules[name] = None makes `import name` raise ImportError.
    monkeypatch.setitem(sys.modules, "pytanque", None)
    snap = build_health_snapshot({"pet_client": None})
    assert snap["toolchain"]["pet"]["pytanque_importable"] is False
    assert any("pytanque" in w for w in snap["warnings"])
