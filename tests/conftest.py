"""Shared fixtures for rocq-mcp test suite."""

from __future__ import annotations

import shutil
from unittest.mock import MagicMock

import pytest

# Ensure the full module graph is loaded (resolves circular import between
# server.py and interactive.py) before any test imports individual symbols.
import rocq_mcp.server  # noqa: F401

# ---------------------------------------------------------------------------
# Availability flags
# ---------------------------------------------------------------------------

COQC_AVAILABLE: bool = shutil.which("coqc") is not None
PET_AVAILABLE: bool = shutil.which("pet") is not None


# ---------------------------------------------------------------------------
# Shared test helpers (used across compile / compile_file / integration suites)
# ---------------------------------------------------------------------------

# Canonical "Real failure" stderr fixture used by status-derivation tests.
_DEFAULT_STDERR = (
    'File "/tmp/tmp.v", line 2, characters 0-5:\n' "Error: Real failure.\n"
)


def _fake_coqc_result(stderr, returncode=1):
    """Build a fake ``_run_coqc`` / ``_run_coqc_file`` return dict."""
    return {
        "returncode": returncode,
        "stdout": "",
        "stderr": stderr,
        "timed_out": False,
    }


def _patch_compile_error(monkeypatch, stderr):
    """Force ``_run_coqc`` to produce a failing fake result with *stderr*."""
    from rocq_mcp import compile as _compile

    monkeypatch.setattr(
        _compile,
        "_run_coqc",
        lambda *a, **kw: _fake_coqc_result(stderr),
    )


def _patch_capture_position_state(monkeypatch, async_fn):
    """Replace the lazy-imported ``capture_position_state`` symbol."""
    from rocq_mcp import interactive as _interactive

    monkeypatch.setattr(_interactive, "capture_position_state", async_fn)


class _MockContext:
    """Minimal mock for FastMCP Context to inject lifespan_state."""

    def __init__(self, lifespan_state):
        self.lifespan_context = lifespan_state


@pytest.fixture(autouse=True)
def _clean_state_table():
    """Reset ``_state_table`` before/after every test for isolation.

    Cheap (just clears a module-level dict) and keeps unit tests that
    populate the state table from leaking entries into each other.
    """
    from rocq_mcp.interactive import _state_invalidate_all

    _state_invalidate_all()
    yield
    _state_invalidate_all()


def add_mock_state(parent_id, tactic, step=0):
    """Add a mock state entry to ``_state_table`` and return its id.

    Convenience helper for unit tests that exercise the state-table
    bookkeeping (chain reconstruction, eviction, body-size limits, ...).
    """
    from unittest.mock import MagicMock

    from rocq_mcp.interactive import _state_add

    state = MagicMock()
    state.proof_finished = False
    return _state_add(
        state=state,
        file="test.v",
        theorem="t",
        workspace="/tmp",
        parent_id=parent_id,
        tactic=tactic,
        step=step,
    )


# ---------------------------------------------------------------------------
# Workspace fixture
# ---------------------------------------------------------------------------


@pytest.fixture(scope="session")
def workspace(tmp_path_factory):
    """Create a temporary workspace directory for coqc tests."""
    ws = tmp_path_factory.mktemp("rocq_workspace")
    return ws


# ---------------------------------------------------------------------------
# Proof fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def simple_proof():
    """A known-good simple proof: n + 0 = n by induction."""
    return (
        "From Coq Require Import Arith.\n\n"
        "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
        "Proof.\n"
        "  intros n. induction n as [| n' IH].\n"
        "  - reflexivity.\n"
        "  - simpl. rewrite IH. reflexivity.\n"
        "Qed.\n"
    )


@pytest.fixture
def simple_problem_statement():
    """The original problem statement for add_0_r (with Admitted)."""
    return (
        "From Coq Require Import Arith.\n\n"
        "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
        "Admitted.\n"
    )


@pytest.fixture
def classical_proof():
    """A proof using classical logic (standard axiom: classic)."""
    return (
        "From Coq Require Import Classical.\n\n"
        "Theorem lem_example : forall P : Prop, P \\/ ~P.\n"
        "Proof.\n"
        "  intro P. apply classic.\n"
        "Qed.\n"
    )


@pytest.fixture
def classical_problem():
    """Problem statement for the classical logic proof."""
    return (
        "From Coq Require Import Classical.\n\n"
        "Theorem lem_example : forall P : Prop, P \\/ ~P.\n"
        "Admitted.\n"
    )


@pytest.fixture
def cheating_proof():
    """A proof that redefines nat as bool to cheat."""
    return (
        "From Coq Require Import Arith.\n\n"
        "Definition nat := bool.\n"
        "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
        "Proof.\n"
        "  intros n. destruct n; reflexivity.\n"
        "Qed.\n"
    )


@pytest.fixture
def axiom_spoofing_proof():
    """A proof that declares a custom axiom named 'classic' to spoof the whitelist.

    This declares ``Axiom classic : False.`` which is NOT the stdlib classic.
    It has the same short name as the standard axiom but different type.
    The axiom classification must REJECT this because inside Module M. it will
    be printed as ``M.classic : False`` (user-qualified, not Coq.Logic... qualified).
    """
    return (
        "Axiom classic : False.\n\n"
        "Theorem anything : 1 = 2.\n"
        "Proof.\n"
        "  destruct classic.\n"
        "Qed.\n"
    )


@pytest.fixture
def admitted_proof():
    """A proof with Admitted inside (helper lemma admitted, not fully proved)."""
    return (
        "From Coq Require Import Arith.\n\n"
        "Lemma helper : forall n : nat, n + 0 = n. Admitted.\n\n"
        "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
        "Proof.\n"
        "  intros n. apply helper.\n"
        "Qed.\n"
    )


@pytest.fixture
def timeout_proof():
    """A proof that loops forever, causing subprocess timeout.

    Uses a tactic that keeps growing the obligation without making
    progress.
    """
    return "Theorem loop_thm : True.\n" "Proof.\n" "  repeat eapply proj1.\n" "Qed.\n"


@pytest.fixture
def braces_proof():
    """A proof using Rocq braces { } for subgoal focusing."""
    return (
        "From Coq Require Import Arith.\n\n"
        "Theorem add_comm_example : forall n m : nat, n + m = m + n.\n"
        "Proof.\n"
        "  intros n m.\n"
        "  { apply Nat.add_comm. }\n"
        "Qed.\n"
    )


@pytest.fixture
def multiline_import_proof():
    """A proof with multi-line From ... Require Import statement."""
    return (
        "From Coq Require Import\n"
        "  Arith\n"
        "  Lia.\n\n"
        "Theorem test : forall n : nat, n + 0 = n.\n"
        "Proof. lia. Qed.\n"
    )


# ---------------------------------------------------------------------------
# Shared mock helpers (used across pet-touching test suites)
# ---------------------------------------------------------------------------


def make_lifespan_state(pet_timeout: float = 30.0, *, full: bool = False) -> dict:
    """Build a lifespan_state dict for tests.

    With *full=False* (default), returns the minimal subset that the
    core pet-touching helpers actually read — sufficient for unit tests
    that drive ``run_*`` directly.

    With *full=True*, returns the complete schema produced by
    ``app_lifespan`` in production: pet bookkeeping fields,
    ``recent_errors`` ring buffer, peak/generation counters.  Use this
    for tests that exercise ``rocq_diag`` or the memory watchdog.
    """
    state: dict = {
        "pet_client": None,
        "pet_timeout": pet_timeout,
        "current_workspace": None,
    }
    if full:
        import collections

        import rocq_mcp.server as _server

        state.update(
            {
                "workspace": "/tmp",
                "pet_started_at": None,
                "total_spawns": 0,
                "peak_pet_rss_mb": 0.0,
                "pet_generation": 0,
                "recent_errors": collections.deque(maxlen=_server._RECENT_ERRORS_MAX),
            }
        )
    return state


def mock_pet(pid: int = 12345, alive: bool = True) -> MagicMock:
    """Minimal mock pet client whose ``.process`` has a pid and a poll() —
    just enough surface for ``_pet_alive`` and ``_sample_pet_rss_mb`` to
    exercise their happy paths.  Test files used to define this verbatim
    (test_diag.py / test_memory_watchdog.py)."""
    m = MagicMock()
    m.process = MagicMock()
    m.process.pid = pid
    m.process.poll.return_value = None if alive else 1
    m.process.stdin = None
    m.process.stdout = None
    m.process.stderr = None
    m._own_pgrp = False
    return m


class _FakeMemoryInfo:
    def __init__(self, rss: int) -> None:
        self.rss = rss


class FakePsutilProcess:
    """Stand-in for ``psutil.Process`` returning a fixed RSS in bytes."""

    def __init__(self, rss_bytes: int) -> None:
        self._rss = rss_bytes

    def memory_info(self) -> _FakeMemoryInfo:
        return _FakeMemoryInfo(self._rss)


def patch_psutil_rss(monkeypatch, rss_mb: int) -> None:
    """Make ``psutil.Process(pid)`` return a fake process with the given RSS."""
    import psutil

    rss_bytes = rss_mb * 1024 * 1024

    def _factory(pid: int) -> FakePsutilProcess:
        return FakePsutilProcess(rss_bytes)

    monkeypatch.setattr(psutil, "Process", _factory)


# ---------------------------------------------------------------------------
# _MockPetBase — shared mock-pet plumbing for MCP-path tests
# ---------------------------------------------------------------------------


class _MockPetBase:
    """Base class for mock-pet MCP-path tests.

    Mock at the ``pet`` boundary (the pytanque client) — the real
    ``_run_with_pet`` executes around it, so lock / semaphore / timeout /
    exception-handler paths are still exercised by tests that inherit from
    this class.  Mocking ``_run_with_pet`` directly skips that entire
    orchestration layer.

    Provides:
      * ``_reset_state_and_semaphore`` (autouse) — clears the state table
        and the global pet semaphore before/after each test.
      * ``_mock_pytanque`` (autouse) — installs a minimal ``pytanque``
        module in ``sys.modules`` if the real package is not importable.
      * ``_setup_state_and_pet(fake_run)`` — convenience helper that
        seeds a root state, builds a MagicMock pet whose ``run``
        delegates to *fake_run*, and returns
        ``(state_id, mock_pet, lifespan_state)``.
    """

    pytestmark = []

    @pytest.fixture(autouse=True)
    def _reset_state_and_semaphore(self):
        import rocq_mcp.server as srv
        from rocq_mcp.interactive import _state_invalidate_all

        _state_invalidate_all()
        srv._pet_semaphore = None
        yield
        _state_invalidate_all()
        srv._pet_semaphore = None

    @pytest.fixture(autouse=True)
    def _mock_pytanque(self):
        import sys
        from types import SimpleNamespace

        if "pytanque" in sys.modules:
            yield
            return

        mock_module = SimpleNamespace(
            PetanqueError=type("PetanqueError", (Exception,), {"message": ""}),
            Pytanque=MagicMock,
            PytanqueMode=SimpleNamespace(STDIO="stdio"),
        )
        sys.modules["pytanque"] = mock_module
        yield
        sys.modules.pop("pytanque", None)

    def _setup_state_and_pet(self, fake_run):
        from types import SimpleNamespace

        import rocq_mcp.interactive as _interactive

        _interactive._state_table.clear()
        _interactive._state_next_id = 1

        mock_state = SimpleNamespace(st=42, proof_finished=False, feedback=[])
        sid = _interactive._state_add(
            state=mock_state,
            file="test.v",
            theorem="test",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet.run = fake_run

        mock_goals = SimpleNamespace(goals=[], stack=[], shelf=[], given_up=[])
        mock_pet.complete_goals.return_value = mock_goals

        lifespan_state = make_lifespan_state()
        lifespan_state["pet_client"] = mock_pet
        lifespan_state["current_workspace"] = "/tmp"
        return sid, mock_pet, lifespan_state
