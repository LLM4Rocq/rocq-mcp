"""Chunked pet.run multi-error walker.

Given a Rocq source file and an open pet (pytanque) client, walks the file
incrementally using ``pet.get_root_state`` + chunked ``pet.run``, attributing
each error to its surrounding proof when possible.  The walk is fail-fast at
the top level: it stops at the first inter-chunk / whole-file error (see
:func:`collect_file_errors`) rather than reporting the cascade that follows a
broken ``Require`` / ``Import`` / ``Notation``.

The module is intentionally self-contained: it imports nothing from the
rest of ``rocq_mcp``. ``pytanque`` is also optional — the ``PetanqueError``
type is imported lazily inside :func:`collect_file_errors` so this module
loads cleanly in environments without pytanque.

Public surface:
    - :class:`ProofError`
    - :func:`collect_file_errors`
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

__all__ = ["ProofError", "collect_file_errors"]


_WALKABLE_DETAILS = frozenset(
    {
        "Theorem",
        "Lemma",
        "Proposition",
        "Corollary",
        "Fact",
        "Remark",
        "Property",
        "Instance",
        "Definition",
        "Fixpoint",
    }
)

_CLOSERS = ("Qed.", "Defined.", "Admitted.", "Abort.", "Save.")

# Chunk kinds that are NOT a single named declaration: inter-chunk vernaculars
# (a broken ``Require`` / ``Import`` / ``Notation`` …) and the whole-file
# fallback.  An error in one of these poisons the environment for every chunk
# after it, so the walk stops there rather than emitting a "not found" cascade.
# Note: named declarations (``Definition``/``Fixpoint``/``Instance``/proofs)
# are their own walkable chunks and are NOT in this set — a failure there does
# not stop the walk.
_TOP_LEVEL_KINDS = frozenset({"<top-level>", "<file>"})


@dataclass(frozen=True)
class ProofError:
    """One error found by the proof walker.

    ``proof_name`` is ``None`` for top-level / inter-chunk errors (e.g. a
    broken ``Require Import``) and for the synthetic single-chunk fallback
    used when ``pet.toc`` is unavailable.

    ``kind`` mirrors the coq-lsp ``detail`` string for named entries
    (``"Theorem"`` / ``"Instance"`` / ...) and is the sentinel
    ``"<top-level>"`` for inter-chunk vernaculars or ``"<file>"`` for the
    whole-file fallback chunk.

    Line numbers are 0-based and inclusive on both ends, matching the
    ranges produced by ``pet.toc``.
    """

    proof_name: str | None
    kind: str
    start_line: int
    end_line: int
    code: int
    message: str


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _split_into_lines(source: str) -> list[str]:
    """Split ``source`` into lines preserving 0-based line indexing.

    ``str.splitlines`` drops the trailing newline; this helper does too,
    but it also guarantees ``[""]`` for an empty file so callers can take
    ``len(lines) - 1`` as ``last_line`` safely.
    """
    if not source:
        return [""]
    return source.splitlines()


def _safe_toc(pet: Any, file: str) -> list[Any] | None:
    """Run ``pet.toc(file)``, returning ``None`` on any expected failure.

    The two failure modes observed in practice are :class:`PetanqueError`
    (parse failures inside coq-lsp) and :class:`TypeError` (raised by
    pytanque itself when the response cannot be unpacked into the typed
    structure).
    """
    try:
        from pytanque import PetanqueError  # type: ignore[import-not-found]
    except ImportError:  # pragma: no cover - exercised only without pytanque
        PetanqueError = ()  # type: ignore[assignment]

    try:
        return pet.toc(file)
    except PetanqueError:
        return None
    except TypeError:
        return None


def _dedupe_and_sort_entries(toc_result: list[Any]) -> list[Any]:
    """Flatten, filter and dedupe walkable entries from ``pet.toc`` output.

    ``pet.toc`` returns ``list[(section_name, list[TocElement])]``.  We
    flatten one level and recurse into ``children`` to surface entries
    that live inside ``Section``/``Module`` blocks.  Entries are kept
    only when:

    * ``detail`` is in :data:`_WALKABLE_DETAILS`,
    * a non-empty ``name`` is present.

    Duplicates are collapsed by the key ``(name, start_line, detail)`` —
    pet emits duplicate rows for constructors/fields and for mutual
    inductives sharing a range; we want a single chunk per proof.
    """
    flat: list[Any] = []

    def _walk(elements: list[Any]) -> None:
        for elem in elements:
            if elem is None:
                continue
            flat.append(elem)
            children = getattr(elem, "children", None)
            if children:
                _walk(children)

    for entry in toc_result:
        try:
            _section_name, elements = entry
        except (TypeError, ValueError):
            continue
        if elements:
            _walk(elements)

    seen: set[tuple[str, int, str]] = set()
    kept: list[Any] = []
    for elem in flat:
        detail = getattr(elem, "detail", "") or ""
        if detail not in _WALKABLE_DETAILS:
            continue
        name_obj = getattr(elem, "name", None)
        name = getattr(name_obj, "v", None) if name_obj is not None else None
        if not name:
            continue
        rng = getattr(elem, "range", None)
        if rng is None:
            continue
        start_line = rng.start.line
        key = (name, start_line, detail)
        if key in seen:
            continue
        seen.add(key)
        kept.append(elem)

    kept.sort(key=lambda e: e.range.start.line)
    return kept


@dataclass(frozen=True)
class _Chunk:
    """A contiguous slice of the file submitted as one ``pet.run`` call."""

    start_line: int
    end_line: int  # inclusive
    proof_name: str | None
    kind: str


def _find_body_end(lines: list[str], stmt_end_line: int, next_start: int | None) -> int:
    """Find the inclusive end line of the proof body following a statement.

    Scans forward from ``stmt_end_line + 1`` for the first line containing
    one of :data:`_CLOSERS`, stopping before ``next_start`` (the start of
    the next named entry, or the end of file).  Falls back to
    ``stmt_end_line`` when no closer is found within the search window.
    """
    last_line = len(lines) - 1
    limit = next_start - 1 if next_start is not None else last_line
    if limit < stmt_end_line + 1:
        return stmt_end_line
    for i in range(stmt_end_line + 1, min(limit, last_line) + 1):
        line = lines[i]
        if any(closer in line for closer in _CLOSERS):
            return i
    return stmt_end_line


def _build_chunks(source: str, entries: list[Any]) -> list[_Chunk]:
    """Split ``source`` into ordered chunks driven by walkable entries.

    Named chunks span ``range.start.line`` through the body's closer (see
    :func:`_find_body_end`).  Gaps between consecutive named chunks become
    unnamed ``"<top-level>"`` chunks so broken ``Require``/``Notation``
    sentences are still caught.  When no walkable entries are present at
    all, a single ``"<file>"`` chunk covers the whole source.
    """
    lines = _split_into_lines(source)
    last_line = len(lines) - 1
    if not entries:
        return [_Chunk(0, last_line, None, "<file>")]

    chunks: list[_Chunk] = []
    cursor = 0
    for idx, elem in enumerate(entries):
        start = elem.range.start.line
        stmt_end = elem.range.end.line
        next_start = (
            entries[idx + 1].range.start.line if idx + 1 < len(entries) else None
        )
        body_end = _find_body_end(lines, stmt_end, next_start)
        if body_end < start:
            body_end = start

        if start > cursor:
            chunks.append(_Chunk(cursor, start - 1, None, "<top-level>"))

        name = elem.name.v
        kind = elem.detail
        chunks.append(_Chunk(start, body_end, name, kind))
        cursor = body_end + 1

    if cursor <= last_line:
        chunks.append(_Chunk(cursor, last_line, None, "<top-level>"))

    return chunks


def _chunk_text(lines: list[str], chunk: _Chunk) -> str:
    """Return the verbatim text of ``chunk`` joined with ``\\n``."""
    end = min(chunk.end_line, len(lines) - 1)
    if chunk.start_line > end:
        return ""
    return "\n".join(lines[chunk.start_line : end + 1])


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------


def collect_file_errors(
    file: str,
    source: str,
    pet: Any,
    *,
    per_call_timeout: float = 5.0,
    max_errors: int = 20,
) -> list[ProofError] | None:
    """Walk *file* via incremental ``pet.run`` chunked by toc.

    Returns:
        * ``None`` if the initial state cannot be obtained — the caller
          should fall back to a compiler-only first-error report.
        * ``[]`` if the walker found no errors.
        * ``list[ProofError]`` when errors were found.

    ``per_call_timeout`` is the timeout passed to every ``pet.run`` call —
    mandatory because pathological tactics such as ``vm_compute`` can
    wedge the RPC indefinitely otherwise.

    ``max_errors`` caps the result list to avoid runaway on adversarial
    files.

    The walk **stops at the first top-level / inter-chunk error** (a broken
    ``Require`` / ``Import`` / ``Notation``): such a failure poisons the
    environment for every later chunk, which would otherwise report a
    cascade of "reference/library not found" errors that bury the real one.
    Errors inside independent named declarations still accumulate up to
    ``max_errors`` (a failed named ``Definition``/``Fixpoint``/proof is its
    own chunk and does not stop the walk).
    """
    try:
        from pytanque import PetanqueError  # type: ignore[import-not-found]
    except ImportError:  # pragma: no cover

        class PetanqueError(Exception):  # type: ignore[no-redef]
            code: int = -32003
            message: str = ""

    toc_result = _safe_toc(pet, file)
    if toc_result is None:
        entries: list[Any] = []
    else:
        entries = _dedupe_and_sort_entries(toc_result)

    chunks = _build_chunks(source, entries)
    lines = _split_into_lines(source)

    try:
        state = pet.get_root_state(file)
    except Exception:
        return None

    errors: list[ProofError] = []
    # pytanque expects ``int`` seconds for the timeout kwarg; coerce when the
    # caller's float is >= 1 to avoid the binding's TypeError, otherwise pass
    # the sub-second float verbatim (the binding tolerates floats < 1).
    timeout_arg = int(per_call_timeout) if per_call_timeout >= 1 else per_call_timeout

    for idx, chunk in enumerate(chunks):
        body = _chunk_text(lines, chunk)
        if not body.strip():
            continue
        try:
            state = pet.run(state, body, timeout=timeout_arg)
        except PetanqueError as e:
            code = getattr(e, "code", -32003)
            message = getattr(e, "message", "") or str(e)
            errors.append(
                ProofError(
                    proof_name=chunk.proof_name,
                    kind=chunk.kind,
                    start_line=chunk.start_line,
                    end_line=chunk.end_line,
                    code=code,
                    message=message,
                )
            )
            if len(errors) >= max_errors:
                break
            # A failure in a top-level / inter-chunk region (a broken
            # ``Require``, ``Import``, ``Notation`` …) changes the
            # environment for everything after it, so subsequent chunks fail
            # with cascade "reference/library not found" errors that bury the
            # real cause.  Stop here — rocq c's own first-error report
            # (``error_positions``) already carries it, and matching rocq c's
            # fail-fast keeps ``errors`` to the genuine problem.
            if chunk.kind in _TOP_LEVEL_KINDS:
                break
            if idx + 1 >= len(chunks):
                break
            resume_line = chunks[idx + 1].start_line
            try:
                state = pet.get_state_at_pos(file, resume_line, 0)
            except Exception:
                break

    return errors
