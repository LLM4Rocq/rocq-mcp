"""Unit tests for :mod:`rocq_mcp.proof_walk`.

All tests run against a mocked pet client built from :class:`_MockPet`
below; they do not require an active rocq opam switch.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from types import SimpleNamespace
from typing import Any, Callable

import pytest

from rocq_mcp.proof_walk import ProofError, collect_file_errors

# ---------------------------------------------------------------------------
# Test helpers
# ---------------------------------------------------------------------------


def _make_toc_element(
    name: str | None,
    detail: str,
    start_line: int,
    end_line: int | None = None,
    end_char: int = 0,
    children: list[Any] | None = None,
) -> SimpleNamespace:
    """Mimic a pytanque ``TocElement`` enough for the walker to inspect it."""
    end_line = end_line if end_line is not None else start_line
    name_obj = SimpleNamespace(v=name) if name is not None else None
    return SimpleNamespace(
        name=name_obj,
        detail=detail,
        range=SimpleNamespace(
            start=SimpleNamespace(line=start_line, character=0),
            end=SimpleNamespace(line=end_line, character=end_char),
        ),
        children=children or [],
    )


def _toc(elements: list[SimpleNamespace]) -> list[tuple[str | None, list[Any]]]:
    """Wrap a flat list of elements in pet.toc's outer ``(section, [...])``."""
    return [(None, elements)]


class _FakePetanqueError(Exception):
    """Stand-in for ``pytanque.PetanqueError`` (only ``.code`` + ``.message``)."""

    def __init__(self, message: str, code: int = -32003) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


@pytest.fixture(autouse=True)
def _patch_petanque_error(monkeypatch: pytest.MonkeyPatch) -> None:
    """Make ``from pytanque import PetanqueError`` yield our fake class.

    The walker imports ``PetanqueError`` lazily inside its functions, so
    we install a stub ``pytanque`` module in ``sys.modules`` and route
    the symbol through it.  This keeps test invariants stable whether or
    not the real pytanque is installed.
    """
    import sys

    fake_module = SimpleNamespace(PetanqueError=_FakePetanqueError)
    monkeypatch.setitem(sys.modules, "pytanque", fake_module)


@dataclass
class _MockPet:
    """Minimal stand-in for a pytanque client.

    ``run_handler`` is invoked with ``(state, body, timeout)`` and returns
    either a new opaque state or raises ``_FakePetanqueError`` to mimic
    coq-lsp reporting an error in *body*.
    """

    toc_result: Any = None
    toc_raises: BaseException | None = None
    root_state: Any = "root"
    run_handler: Callable[[Any, str, int | float], Any] | None = None
    resume_handler: Callable[[str, int, int], Any] | None = None
    calls: list[tuple[str, str]] = field(default_factory=list)
    resume_calls: list[tuple[str, int]] = field(default_factory=list)

    def toc(self, file: str) -> Any:
        if self.toc_raises is not None:
            raise self.toc_raises
        return self.toc_result

    def get_root_state(self, file: str) -> Any:
        if isinstance(self.root_state, BaseException):
            raise self.root_state
        return self.root_state

    def run(self, state: Any, body: str, *, timeout: int | float) -> Any:
        self.calls.append((state, body))
        assert self.run_handler is not None, "run_handler not configured"
        return self.run_handler(state, body, timeout)

    def get_state_at_pos(self, file: str, line: int, char: int) -> Any:
        self.resume_calls.append((file, line))
        if self.resume_handler is None:
            return ("resumed", line)
        return self.resume_handler(file, line, char)


# ---------------------------------------------------------------------------
# Tests: fallback paths
# ---------------------------------------------------------------------------


class TestFallbackPaths:
    def test_empty_source_returns_empty(self) -> None:
        """Empty source: walker has nothing to do, returns ``[]``."""
        pet = _MockPet(toc_result=[], run_handler=lambda s, b, t: s)
        assert collect_file_errors("f.v", "", pet) == []
        assert pet.calls == []  # no chunks submitted (all whitespace)

    def test_toc_petanque_error_falls_back_to_single_chunk(self) -> None:
        """When ``pet.toc`` raises, the walker still runs the whole file."""
        source = "Definition x := 1.\n"
        pet = _MockPet(
            toc_raises=_FakePetanqueError("parse error"),
            run_handler=lambda s, b, t: "after",
        )
        errs = collect_file_errors("f.v", source, pet)
        assert errs == []
        assert len(pet.calls) == 1
        assert pet.calls[0][1] == "Definition x := 1."

    def test_toc_type_error_falls_back_to_single_chunk(self) -> None:
        """``pet.toc`` raising :class:`TypeError` should not bubble up."""
        source = "Definition x := 1.\n"
        pet = _MockPet(
            toc_raises=TypeError("cannot unpack"),
            run_handler=lambda s, b, t: "after",
        )
        errs = collect_file_errors("f.v", source, pet)
        assert errs == []
        assert len(pet.calls) == 1

    def test_root_state_failure_returns_none(self) -> None:
        """If even the root state cannot be obtained, return ``None``."""
        pet = _MockPet(
            toc_result=[],
            root_state=_FakePetanqueError("init failed"),
            run_handler=lambda s, b, t: s,
        )
        assert collect_file_errors("f.v", "Definition x := 1.", pet) is None


# ---------------------------------------------------------------------------
# Tests: per-proof attribution
# ---------------------------------------------------------------------------


class TestAttribution:
    def test_single_broken_theorem(self) -> None:
        """One broken theorem out of three: one ``ProofError`` attributed
        to it; other chunks run cleanly."""
        source = (
            "Theorem t1 : True.\n"  # 0
            "Proof. trivial. Qed.\n"  # 1
            "Theorem t2 : False.\n"  # 2
            "Proof. trivial. Qed.\n"  # 3 (broken)
            "Theorem t3 : True.\n"  # 4
            "Proof. trivial. Qed.\n"  # 5
        )
        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t2", "Theorem", 2),
            _make_toc_element("t3", "Theorem", 4),
        ]

        def handler(state: Any, body: str, t: Any) -> Any:
            if "t2" in body:
                raise _FakePetanqueError("Cannot solve goal False")
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs is not None and len(errs) == 1
        err = errs[0]
        assert err.proof_name == "t2"
        assert err.kind == "Theorem"
        assert err.start_line == 2
        assert err.end_line == 3
        assert err.code == -32003
        assert "False" in err.message

    def test_cascade_within_proof_dedup(self) -> None:
        """A proof with 5 sentences where 3 would fail still yields exactly
        one ``ProofError`` — pet.run raises on the first failing sentence."""
        body_lines = ["Theorem t : True."] + ["Proof. bad1. bad2. bad3. Qed."]
        # The 5-sentence count is conceptual; the cascade collapses because
        # pet.run on the whole chunk raises on the first error.
        source = "\n".join(body_lines) + "\n"
        elements = [_make_toc_element("t", "Theorem", 0)]

        def handler(state: Any, body: str, t: Any) -> Any:
            raise _FakePetanqueError("bad1 not a tactic")

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs is not None and len(errs) == 1
        assert errs[0].proof_name == "t"


# ---------------------------------------------------------------------------
# Tests: bounding
# ---------------------------------------------------------------------------


class TestBounds:
    def test_max_errors_cap(self) -> None:
        """A file with 50 broken theorems should produce exactly 5 errors
        when ``max_errors=5``."""
        elements: list[SimpleNamespace] = []
        source_lines: list[str] = []
        for i in range(50):
            stmt_line = 2 * i
            elements.append(_make_toc_element(f"t{i}", "Theorem", stmt_line))
            source_lines.append(f"Theorem t{i} : False.")
            source_lines.append("Proof. trivial. Qed.")
        source = "\n".join(source_lines) + "\n"

        def handler(state: Any, body: str, t: Any) -> Any:
            raise _FakePetanqueError("False not provable")

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet, max_errors=5)
        assert errs is not None and len(errs) == 5
        assert [e.proof_name for e in errs] == [f"t{i}" for i in range(5)]

    def test_per_call_timeout_is_passed(self) -> None:
        """The configured timeout must reach every ``pet.run`` call."""
        observed: list[Any] = []

        def handler(state: Any, body: str, t: Any) -> Any:
            observed.append(t)
            return "ok"

        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t2", "Theorem", 2),
        ]
        source = "Theorem t1 : True.\nProof. trivial. Qed.\nTheorem t2 : True.\nProof. trivial. Qed.\n"
        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet, per_call_timeout=7.0)
        assert errs == []
        assert observed == [7, 7]

    def test_timeout_shaped_error_recorded_and_walk_continues(self) -> None:
        """A timeout-shaped PetanqueError on chunk 1 should produce one
        ProofError, then the walker must continue with chunk 2."""
        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t2", "Theorem", 2),
        ]
        source = "Theorem t1 : True.\nProof. trivial. Qed.\nTheorem t2 : True.\nProof. trivial. Qed.\n"

        def handler(state: Any, body: str, t: Any) -> Any:
            if "t1" in body:
                raise _FakePetanqueError("Tactic timeout", code=-32003)
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs is not None and len(errs) == 1
        assert errs[0].proof_name == "t1"
        # The walker resumed at chunk 2's start and ran it without error.
        assert pet.resume_calls and pet.resume_calls[0][1] == 2


# ---------------------------------------------------------------------------
# Tests: resume behaviour
# ---------------------------------------------------------------------------


class TestResume:
    def test_resume_after_error_continues(self) -> None:
        """Successful ``get_state_at_pos`` lets the walker proceed past an
        error and surface a second error in a later chunk."""
        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t2", "Theorem", 2),
            _make_toc_element("t3", "Theorem", 4),
        ]
        source = (
            "Theorem t1 : True.\nProof. trivial. Qed.\n"
            "Theorem t2 : True.\nProof. trivial. Qed.\n"
            "Theorem t3 : True.\nProof. trivial. Qed.\n"
        )

        def handler(state: Any, body: str, t: Any) -> Any:
            if "t1" in body or "t3" in body:
                raise _FakePetanqueError(f"err in {'t1' if 't1' in body else 't3'}")
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs is not None and len(errs) == 2
        assert errs[0].proof_name == "t1"
        assert errs[1].proof_name == "t3"

    def test_resume_failure_stops_walk(self) -> None:
        """If ``get_state_at_pos`` raises, the walker stops cleanly with the
        errors collected so far."""
        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t2", "Theorem", 2),
        ]
        source = "Theorem t1 : True.\nProof. trivial. Qed.\nTheorem t2 : True.\nProof. trivial. Qed.\n"

        def handler(state: Any, body: str, t: Any) -> Any:
            raise _FakePetanqueError(f"err in {body.splitlines()[0]}")

        def resume_handler(file: str, line: int, char: int) -> Any:
            raise _FakePetanqueError("resume failed")

        pet = _MockPet(
            toc_result=_toc(elements),
            run_handler=handler,
            resume_handler=resume_handler,
        )
        errs = collect_file_errors("f.v", source, pet)
        assert errs is not None and len(errs) == 1
        assert errs[0].proof_name == "t1"


# ---------------------------------------------------------------------------
# Tests: chunk-builder edge cases
# ---------------------------------------------------------------------------


class TestChunkBuilder:
    def test_consecutive_toc_entries_no_gap(self) -> None:
        """Two entries on adjacent lines should not produce an empty
        inter-chunk between them."""
        # t1's body ends on line 1; t2 starts on line 2 → no gap chunk.
        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t2", "Theorem", 2),
        ]
        source = "Theorem t1 : True.\nProof. trivial. Qed.\nTheorem t2 : True.\nProof. trivial. Qed.\n"

        seen_bodies: list[str] = []

        def handler(state: Any, body: str, t: Any) -> Any:
            seen_bodies.append(body)
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs == []
        # We should see exactly two chunks (one per theorem) — no empty
        # top-level chunk between them.
        assert len(seen_bodies) == 2
        assert seen_bodies[0].startswith("Theorem t1")
        assert seen_bodies[1].startswith("Theorem t2")

    def test_file_with_no_toc_entries_single_chunk(self) -> None:
        """No walkable entries → single ``<file>`` chunk over whole source."""
        source = "Require Import Arith.\n"

        def handler(state: Any, body: str, t: Any) -> Any:
            raise _FakePetanqueError("Cannot find Arith")

        pet = _MockPet(toc_result=[], run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs is not None and len(errs) == 1
        assert errs[0].proof_name is None
        assert errs[0].kind == "<file>"

    def test_no_closer_in_window_falls_back_to_stmt_end(self) -> None:
        """No ``Qed.``/``Defined.`` in next lines → body_end ==
        ``range.end.line``.  The chunk should still be submitted and any
        error attributed to the named entry."""
        # 11-line source; theorem range stops at line 0, no closer anywhere.
        source = "\n".join([f"line {i}" for i in range(11)]) + "\n"
        elements = [_make_toc_element("t", "Theorem", 0, end_line=0)]

        seen_bodies: list[str] = []

        def handler(state: Any, body: str, t: Any) -> Any:
            seen_bodies.append(body)
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        errs = collect_file_errors("f.v", source, pet)
        assert errs == []
        # The first chunk is just line 0 because no closer is present.
        assert seen_bodies[0] == "line 0"


# ---------------------------------------------------------------------------
# Tests: deduplication
# ---------------------------------------------------------------------------


class TestDedup:
    def test_duplicate_toc_entries_collapsed(self) -> None:
        """``pet.toc`` sometimes emits duplicate entries (mutual
        inductives, constructors) — they should be collapsed to one
        chunk."""
        # Two entries with same (name, start_line, detail) — should dedupe.
        elements = [
            _make_toc_element("t1", "Theorem", 0),
            _make_toc_element("t1", "Theorem", 0),
        ]
        source = "Theorem t1 : True.\nProof. trivial. Qed.\n"

        bodies: list[str] = []

        def handler(state: Any, body: str, t: Any) -> Any:
            bodies.append(body)
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        collect_file_errors("f.v", source, pet)
        assert len(bodies) == 1

    def test_unnamed_or_non_walkable_entries_skipped(self) -> None:
        """Entries with no name or with details outside
        :data:`_WALKABLE_DETAILS` must be ignored."""
        elements = [
            _make_toc_element(None, "Theorem", 0),  # unnamed
            _make_toc_element("Foo", "Inductive", 2),  # not walkable
            _make_toc_element("real_t", "Theorem", 4),  # kept
        ]
        # Pad source so line 4 is reachable.
        source = "\n".join(["line %d" % i for i in range(6)]) + "\n"

        seen_chunks: list[tuple[int, str]] = []

        def handler(state: Any, body: str, t: Any) -> Any:
            # Capture the chunk's first line to verify which entry it came from.
            seen_chunks.append((len(seen_chunks), body))
            return "ok"

        pet = _MockPet(toc_result=_toc(elements), run_handler=handler)
        collect_file_errors("f.v", source, pet)
        # We expect: an inter-chunk for lines 0..3, then the real_t chunk.
        assert any("line 4" in body for _, body in seen_chunks)
