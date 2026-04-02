"""Tests for proof reconstruction of Admitted / Section-local theorems."""

from __future__ import annotations

import re
import tempfile
import textwrap
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

from rocq_mcp.interactive import _reconstruct_proof_state


def _make_state(proof_finished: bool = False) -> SimpleNamespace:
    return SimpleNamespace(proof_finished=proof_finished)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _write_v_file(content: str) -> str:
    """Write *content* to a temp .v file and return its path."""
    f = tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False)
    f.write(textwrap.dedent(content))
    f.close()
    return f.name


# ---------------------------------------------------------------------------
# Strategy 1: pet.start(thm_name) succeeds
# ---------------------------------------------------------------------------


class TestReconstructionStrategy1:
    """pet.start() works for top-level theorems."""

    def test_basic_reconstruction(self):
        # Lines: 0=From, 1=Lemma, 2=Proof., 3=intros, 4=Admitted.
        path = _write_v_file("""\
From Stdlib Require Import Arith.
Lemma add_0_r : forall n, n + 0 = n.
Proof.
  intros n.
Admitted.
""")
        pet = MagicMock()
        open_state = _make_state(proof_finished=False)
        # pet.start returns an open proof state
        pet.start.return_value = open_state
        # pet.run replays tactics and returns a new state
        pet.run.return_value = _make_state(proof_finished=False)

        # cursor at line 4 (Admitted line) — replay should include "intros n."
        state, msg = _reconstruct_proof_state(pet, path, cursor_line=4, cursor_char=0)

        assert state is not None
        assert not state.proof_finished
        pet.start.assert_called_once_with(path, "add_0_r")
        # run() called once to replay "intros n."
        assert pet.run.call_count == 1

    def test_cursor_at_proof_start(self):
        """Cursor right after Proof. — no tactics to replay."""
        # Lines: 0=Theorem, 1=Proof., 2=Admitted.
        path = _write_v_file("""\
Theorem foo : True.
Proof.
Admitted.
""")
        pet = MagicMock()
        pet.start.return_value = _make_state(proof_finished=False)

        # cursor at line 2 (Admitted) — replay_start=2, cursor=2, so no tactics
        state, msg = _reconstruct_proof_state(pet, path, cursor_line=2, cursor_char=0)

        assert state is not None
        # No run() call needed since no tactics between Proof. and cursor
        pet.run.assert_not_called()

    def test_start_returns_finished_falls_to_strategy2(self):
        """pet.start returns proof_finished → fall to strategy 2."""
        # Lines: 0=From, 1=Lemma, 2=Proof., 3=Admitted.
        path = _write_v_file("""\
From Stdlib Require Import Arith.
Lemma bar : True.
Proof.
Admitted.
""")
        pet = MagicMock()
        # Strategy 1 returns finished
        pet.start.return_value = _make_state(proof_finished=True)
        # Strategy 2 calls
        replay_state = _make_state(proof_finished=False)
        pet.get_state_at_pos.return_value = _make_state(proof_finished=False)
        pet.run.return_value = replay_state

        state, msg = _reconstruct_proof_state(pet, path, cursor_line=3, cursor_char=0)

        assert state is not None
        pet.get_state_at_pos.assert_called_once()


# ---------------------------------------------------------------------------
# Strategy 2: Section-local theorem (pet.start fails)
# ---------------------------------------------------------------------------


class TestReconstructionStrategy2:
    """Fallback: replay from file start."""

    def test_section_local(self):
        # Lines: 0=From, 1=Section, 2=Variable, 3=Lemma, 4=Proof., 5=reflexivity, 6=Admitted.
        path = _write_v_file("""\
From Stdlib Require Import Arith.
Section Foo.
Variable x : nat.
Lemma bar : x = x.
Proof.
  reflexivity.
Admitted.
""")
        pet = MagicMock()
        pet.start.side_effect = Exception("Section-local, cannot start")
        base_state = _make_state(proof_finished=False)
        pet.get_state_at_pos.return_value = base_state
        after_replay = _make_state(proof_finished=False)
        # First run: replay preamble; second run: replay tactics
        pet.run.side_effect = [after_replay, _make_state(proof_finished=False)]

        # cursor at line 6 (Admitted) — replay includes "reflexivity."
        state, msg = _reconstruct_proof_state(pet, path, cursor_line=6, cursor_char=0)

        assert state is not None
        # get_state_at_pos called for base state
        pet.get_state_at_pos.assert_called_once()
        # run called: once for preamble, once for tactic replay
        assert pet.run.call_count == 2


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------


class TestReconstructionEdgeCases:
    def test_no_lemma_found(self):
        path = _write_v_file("""\
(* just a comment *)
""")
        pet = MagicMock()
        state, msg = _reconstruct_proof_state(pet, path, cursor_line=0, cursor_char=0)
        assert state is None
        assert "Could not locate" in msg

    def test_file_not_found(self):
        pet = MagicMock()
        state, msg = _reconstruct_proof_state(pet, "/nonexistent.v", 0, 0)
        assert state is None
        assert "Cannot read file" in msg

    def test_local_lemma_keyword(self):
        """Local Lemma is recognized."""
        # Lines: 0=Section, 1=Local Lemma, 2=Proof., 3=Admitted.
        path = _write_v_file("""\
Section S.
Local Lemma foo : True.
Proof.
Admitted.
""")
        pet = MagicMock()
        pet.start.return_value = _make_state(proof_finished=False)

        state, msg = _reconstruct_proof_state(pet, path, cursor_line=3, cursor_char=0)

        assert state is not None
        pet.start.assert_called_once_with(path, "foo")

    def test_both_strategies_fail(self):
        # Lines: 0=Lemma, 1=Proof., 2=Admitted.
        path = _write_v_file("""\
Lemma bad : True.
Proof.
Admitted.
""")
        pet = MagicMock()
        pet.start.side_effect = Exception("fail")
        pet.get_state_at_pos.return_value = _make_state(proof_finished=False)
        pet.run.side_effect = Exception("replay fail")

        state, msg = _reconstruct_proof_state(pet, path, cursor_line=2, cursor_char=0)

        assert state is None
        assert "failed" in msg.lower()

    def test_sentence_by_sentence_fallback(self):
        """When block replay fails, falls back to sentence-by-sentence."""
        # Lines: 0=Lemma, 1=Proof., 2=idtac. exact I., 3=Admitted.
        path = _write_v_file("""\
Lemma baz : True.
Proof.
  idtac. exact I.
Admitted.
""")
        pet = MagicMock()
        open_state = _make_state(proof_finished=False)
        pet.start.return_value = open_state
        # Block replay fails, sentence-by-sentence succeeds
        mid_state = _make_state(proof_finished=False)
        final_state = _make_state(proof_finished=False)
        pet.run.side_effect = [
            Exception("block fail"),  # block replay
            mid_state,                # "idtac."
            final_state,              # "exact I."
        ]

        # cursor at line 3 (Admitted) — should replay "idtac. exact I."
        state, msg = _reconstruct_proof_state(pet, path, cursor_line=3, cursor_char=0)

        assert state is not None
        # run called: 1 (block fail) + 2 (sentences)
        assert pet.run.call_count == 3

    def test_comments_and_terminators_stripped(self):
        """Comments and Admitted/Qed are removed before replay."""
        path = _write_v_file("""\
Theorem foo : True.
Proof.
  (* a comment *) exact I.
Admitted.
""")
        pet = MagicMock()
        pet.start.return_value = _make_state(proof_finished=False)
        pet.run.return_value = _make_state(proof_finished=False)

        state, msg = _reconstruct_proof_state(pet, path, cursor_line=3, cursor_char=0)

        assert state is not None
        # The replay text should NOT contain the comment or Admitted
        replay_call = pet.run.call_args_list[0]
        tactic_text = replay_call[0][1]
        assert "(*" not in tactic_text
        assert "Admitted" not in tactic_text

    def test_program_definition_keyword(self):
        """Program Definition is recognized."""
        path = _write_v_file("""\
Program Definition my_prog : nat.
Proof.
  exact 0.
Admitted.
""")
        pet = MagicMock()
        pet.start.return_value = _make_state(proof_finished=False)

        state, msg = _reconstruct_proof_state(pet, path, cursor_line=3, cursor_char=0)
        assert state is not None
        pet.start.assert_called_once_with(path, "my_prog")

    def test_global_instance_keyword(self):
        """Global Instance is recognized."""
        path = _write_v_file("""\
Global Instance my_inst : True.
Proof.
  exact I.
Admitted.
""")
        pet = MagicMock()
        pet.start.return_value = _make_state(proof_finished=False)

        state, msg = _reconstruct_proof_state(pet, path, cursor_line=3, cursor_char=0)
        assert state is not None
        pet.start.assert_called_once_with(path, "my_inst")


# ---------------------------------------------------------------------------
# Integration tests: run_start position mode triggers reconstruction
# ---------------------------------------------------------------------------


class _MockPetBase:
    """Shared setup for mock-based tests (no real pet)."""

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
        """Ensure pytanque is importable even if not installed."""
        import sys

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


class TestRunStartReconstruction(_MockPetBase):
    """Integration: run_start in position mode calls reconstruction when needed."""

    @pytest.mark.asyncio
    async def test_proof_finished_triggers_reconstruction(self):
        """When get_state_at_pos returns proof_finished=True, reconstruction runs."""
        import os
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False

        # get_state_at_pos returns proof_finished=True (the trigger)
        finished = SimpleNamespace(st=50, proof_finished=True, feedback=[])
        mock_pet.get_state_at_pos.return_value = finished

        # pet.start returns an open proof state (reconstruction succeeds)
        open_state = SimpleNamespace(st=100, proof_finished=False, feedback=[])
        mock_pet.start.return_value = open_state

        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        lifespan = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with tempfile.TemporaryDirectory() as ws:
            vfile = os.path.join(ws, "test.v")
            with open(vfile, "w") as f:
                f.write(
                    "Theorem my_thm : forall n : nat, n = n.\n"
                    "Proof.\n"
                    "  intros.\n"
                    "Admitted.\n"
                )

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="",
                    workspace=ws,
                    lifespan_state=lifespan,
                    line=2,
                    character=0,
                )

        assert result["success"] is True
        assert result["proof_finished"] is False
        # pet.start called by reconstruction
        mock_pet.start.assert_called_once_with(os.path.join(ws, "test.v"), "my_thm")

    @pytest.mark.asyncio
    async def test_proof_not_finished_skips_reconstruction(self):
        """When proof_finished=False, reconstruction does NOT run."""
        import os
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False

        normal = SimpleNamespace(st=50, proof_finished=False, feedback=[])
        mock_pet.get_state_at_pos.return_value = normal
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        lifespan = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with tempfile.TemporaryDirectory() as ws:
            vfile = os.path.join(ws, "test.v")
            with open(vfile, "w") as f:
                f.write("Theorem t : True.\nProof. exact I. Qed.\n")

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="",
                    workspace=ws,
                    lifespan_state=lifespan,
                    line=1,
                    character=0,
                )

        assert result["success"] is True
        assert result["proof_finished"] is False
        # reconstruction should NOT have been triggered
        mock_pet.start.assert_not_called()

    @pytest.mark.asyncio
    async def test_reconstruction_failure_keeps_original_state(self):
        """When reconstruction fails, original (finished) state is kept."""
        import os
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        mock_pet = MagicMock()
        mock_pet.process = MagicMock()
        mock_pet.process.poll.return_value = None
        mock_pet._own_pgrp = False

        finished = SimpleNamespace(st=50, proof_finished=True, feedback=[])
        mock_pet.get_state_at_pos.side_effect = [
            finished,                       # run_start call
            Exception("approach 2 fail"),   # reconstruction approach 2
        ]
        mock_pet.start.side_effect = Exception("approach 1 fail")
        mock_pet.complete_goals.return_value = SimpleNamespace(
            goals=[], stack=[], shelf=[], given_up=[]
        )

        lifespan = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        with tempfile.TemporaryDirectory() as ws:
            vfile = os.path.join(ws, "test.v")
            with open(vfile, "w") as f:
                f.write(
                    "Require Import Arith.\n"
                    "Lemma foo : True.\nProof.\nAdmitted.\n"
                )

            with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
                result = await _interactive.run_start(
                    file="test.v",
                    theorem="",
                    workspace=ws,
                    lifespan_state=lifespan,
                    line=3,
                    character=0,
                )

        assert result["success"] is True
        # Original state preserved
        assert result["proof_finished"] is True
