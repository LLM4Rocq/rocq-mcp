"""rocq_search, rocq_goal, step_multi upgrades, and proof_script assembly."""

from __future__ import annotations

import asyncio
from types import SimpleNamespace
from unittest.mock import patch

from tests.conftest import _MockPetBase


def _hyp(names, ty, def_=None):
    return SimpleNamespace(names=list(names), ty=ty, def_=def_)


def _goal(hyps, ty):
    return SimpleNamespace(hyps=hyps, ty=ty)


def _complete(goals, stack=(), shelf=(), given_up=()):
    return SimpleNamespace(
        goals=list(goals), stack=list(stack), shelf=list(shelf), given_up=list(given_up)
    )


def _feedback_state(messages, st=50):
    return SimpleNamespace(
        st=st, proof_finished=False, feedback=[(3, m) for m in messages]
    )


class TestBuildSearchCommand:
    def test_composition(self):
        from rocq_mcp.interactive import _build_search_command

        assert (
            _build_search_command("(_ + _)", "Lemma", ["Nat"], ["Coq.Init"])
            == "Search is:Lemma (_ + _) inside Nat outside Coq.Init."
        )

    def test_trailing_dot_stripped_then_added(self):
        from rocq_mcp.interactive import _build_search_command

        assert _build_search_command("(_ + _).", "", [], []) == "Search (_ + _)."


class TestRunSearch(_MockPetBase):
    def _search(self, mock_pet, lifespan_state, **kwargs):
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as srv

        with patch.object(srv, "_ensure_pet", return_value=mock_pet):
            return asyncio.run(
                _interactive.run_search(
                    workspace="/tmp", lifespan_state=lifespan_state, **kwargs
                )
            )

    def _pet_with_hits(self, hits_per_command):
        """hits_per_command: list of lists of feedback messages."""
        from unittest.mock import MagicMock

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(lambda *a, **k: None)
        replies = [_feedback_state(msgs) for msgs in hits_per_command]
        mock_pet.run = MagicMock(side_effect=replies)
        return sid, mock_pet, lifespan_state

    def test_parses_hits(self):
        sid, pet, ls = self._pet_with_hits(
            [["Nat.add_comm: forall n m : nat,\n n + m = m + n", "weird output"]]
        )
        result = self._search(pet, ls, pattern="(_ + _ = _ + _)", from_state=sid)
        assert result["success"] is True, result
        assert result["total"] == 2
        assert result["hits"][0] == {
            "name": "Nat.add_comm",
            "type": "forall n m : nat,\n n + m = m + n",
        }
        assert result["hits"][1] == {"raw": "weird output"}
        assert result["truncated"] is False
        assert result["query"] == "Search (_ + _ = _ + _)."

    def test_fanout_merges_and_tracks_patterns(self):
        sid, pet, ls = self._pet_with_hits(
            [
                ["add_comm: t1", "add_assoc: t2"],
                ["add_comm: t1", "mul_comm: t3"],
            ]
        )
        result = self._search(
            pet, ls, pattern="(_ + _)", patterns=["(_ * _)"], from_state=sid
        )
        assert result["total"] == 3
        by_name = {h["name"]: h for h in result["hits"]}
        assert by_name["add_comm"]["matched_patterns"] == ["(_ + _)", "(_ * _)"]
        assert by_name["mul_comm"]["matched_patterns"] == ["(_ * _)"]

    def test_pagination(self):
        sid, pet, ls = self._pet_with_hits([[f"lemma{i}: T{i}" for i in range(10)]])
        result = self._search(
            pet, ls, pattern="(_)", from_state=sid, max_results=3, offset=3
        )
        assert [h["name"] for h in result["hits"]] == ["lemma3", "lemma4", "lemma5"]
        assert result["total"] == 10
        assert result["truncated"] is True

    def test_include_types_false(self):
        sid, pet, ls = self._pet_with_hits([["a: t"]])
        result = self._search(
            pet, ls, pattern="(_)", from_state=sid, include_types=False
        )
        assert result["hits"] == [{"name": "a"}]

    def test_query_rejected_reason(self):
        from unittest.mock import MagicMock

        from pytanque import PetanqueError  # real package or _MockPetBase mock

        sid, pet, ls = self._pet_with_hits([[]])
        # Signature differs between the real class and the test mock —
        # bypass __init__ and set what run_search reads.
        exc = PetanqueError.__new__(PetanqueError)
        exc.message = "Syntax error in Search"
        pet.run = MagicMock(side_effect=exc)
        result = self._search(pet, ls, pattern="((broken", from_state=sid)
        assert result["success"] is False
        assert result["reason"] == "query_rejected"
        assert "Search" in result["error"]

    def test_validation_failures(self):
        result = asyncio.run(
            __import__("rocq_mcp.interactive", fromlist=["run_search"]).run_search(
                pattern="",
                workspace="/tmp",
                lifespan_state={"pet_timeout": 5.0},
            )
        )
        assert result["success"] is False and result["reason"] == "validation"


class TestRunGoal(_MockPetBase):
    def test_from_state_mode_registers_nothing(self):
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as srv

        sid, pet, ls = self._setup_state_and_pet(lambda *a, **k: None)
        pet.complete_goals.return_value = _complete([_goal([_hyp(["n"], "nat")], "G")])
        table_size = len(_interactive._state_table)

        with patch.object(srv, "_ensure_pet", return_value=pet):
            result = asyncio.run(
                _interactive.run_goal(lifespan_state=ls, from_state=sid)
            )
        assert result["success"] is True
        assert result["stateless"] is True
        assert result["goals_count"] == 1
        assert "n : nat" in result["goals"]
        assert len(_interactive._state_table) == table_size  # nothing added

    def test_diff_from(self):
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as srv

        sid, pet, ls = self._setup_state_and_pet(lambda *a, **k: None)
        other = _interactive._state_add(
            state=SimpleNamespace(st=77, proof_finished=False, feedback=[]),
            file="test.v",
            theorem="t",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )
        g1 = _goal([], "A")
        g2 = _goal([], "B")
        pet.complete_goals.side_effect = [_complete([g1, g2]), _complete([g1])]

        with patch.object(srv, "_ensure_pet", return_value=pet):
            result = asyncio.run(
                _interactive.run_goal(
                    lifespan_state=ls, from_state=sid, diff_from=other
                )
            )
        assert result["success"] is True
        assert result["goals_diff"]["after_count"] == 2
        assert "goals" not in result

    def test_mode_validation(self):
        import rocq_mcp.interactive as _interactive

        result = asyncio.run(_interactive.run_goal(lifespan_state={"pet_timeout": 5.0}))
        assert result["success"] is False and result["reason"] == "validation"

        result = asyncio.run(
            _interactive.run_goal(
                lifespan_state={"pet_timeout": 5.0},
                file="a.v",
                line=1,
                character=0,
                diff_from=3,
            )
        )
        assert result["success"] is False
        assert "diff_from requires from_state" in result["error"]


class TestStepMultiUpgrades(_MockPetBase):
    def _run(self, lifespan_state, mock_pet, **kwargs):
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as srv

        with patch.object(srv, "_ensure_pet", return_value=mock_pet):
            return asyncio.run(
                _interactive.run_step_multi(lifespan_state=lifespan_state, **kwargs)
            )

    def test_time_ms_and_summary(self):
        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(
                st=hash(cmd), proof_finished=cmd == "lia.", feedback=[]
            )

        sid, pet, ls = self._setup_state_and_pet(fake_run)
        completes = {
            "auto.": _complete([_goal([], "G1"), _goal([], "G2")]),
            "lia.": _complete([]),
        }
        calls = iter(["auto.", "lia."])
        pet.complete_goals.side_effect = lambda s: completes[next(calls)]

        result = self._run(ls, pet, tactics=["auto.", "lia."], from_state=sid)
        assert all("time_ms" in e for e in result["results"])
        summary = result["summary"]
        assert summary["tried"] == 2
        assert summary["succeeded"] == 2
        assert summary["finished"] == ["lia."]
        assert summary["best"] == {"tactic": "lia.", "goals_count": 0}

    def test_preset_auto_appends_battery(self):
        from rocq_mcp.interactive import _AUTO_SOLVE_TACTICS

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(st=1, proof_finished=False, feedback=[])

        sid, pet, ls = self._setup_state_and_pet(fake_run)
        pet.complete_goals.return_value = _complete([_goal([], "G")])

        result = self._run(ls, pet, tactics=["custom."], from_state=sid, preset="auto")
        tried = [e["tactic"] for e in result["results"]]
        assert tried[0] == "custom."
        assert tried[1] == _AUTO_SOLVE_TACTICS[0]
        assert len(tried) <= 20
        # 1 user + 16 battery = 17 <= 20: nothing cut
        assert "preset_truncated" not in result

    def test_preset_truncation_flag(self):
        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(st=1, proof_finished=False, feedback=[])

        sid, pet, ls = self._setup_state_and_pet(fake_run)
        pet.complete_goals.return_value = _complete([])

        user = [f"t{i}." for i in range(10)]
        result = self._run(ls, pet, tactics=user, from_state=sid, preset="auto")
        assert result["preset_truncated"] is True
        assert len(result["results"]) == 20

    def test_per_tactic_timeouts_forwarded(self):
        recorded = []

        def fake_run(state, cmd, timeout=None):
            recorded.append((cmd, timeout))
            return SimpleNamespace(st=1, proof_finished=False, feedback=[])

        sid, pet, ls = self._setup_state_and_pet(fake_run)
        pet.complete_goals.return_value = _complete([])

        result = self._run(
            ls,
            pet,
            tactics=["auto.", "lia."],
            from_state=sid,
            timeouts=[3.0, 7.0],
        )
        assert result["success"] is True
        assert recorded == [("auto.", 3), ("lia.", 7)]

    def test_timeouts_length_mismatch(self):
        sid, pet, ls = self._setup_state_and_pet(lambda *a, **k: None)
        result = self._run(
            ls, pet, tactics=["auto."], from_state=sid, timeouts=[1.0, 2.0]
        )
        assert result["success"] is False and result["reason"] == "validation"


class TestProofScript:
    def test_file_mode_statement_recovery(self, tmp_path):
        from rocq_mcp.interactive import _assemble_proof_script, _state_add, _state_get

        source = (
            "From Coq Require Import Arith.\n\n"
            "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
            "Admitted.\n"
        )
        vfile = tmp_path / "A.v"
        vfile.write_text(source)

        sid = _state_add(
            state=SimpleNamespace(proof_finished=True),
            file="A.v",
            theorem="add_0_r",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            resolved_file=str(vfile),
        )
        entry = _state_get(sid)
        fields = _assemble_proof_script(
            entry, ["intros n.", "induction n.", "reflexivity."]
        )
        assert fields["statement_source"] == "file"
        assert fields["statement"].startswith("Theorem add_0_r")
        script = fields["proof_script"]
        assert "Proof.\n  intros n.\n  induction n.\n  reflexivity.\nQed." in script

    def test_session_commands_mode(self):
        from rocq_mcp.interactive import _assemble_proof_script, _state_add, _state_get

        sid = _state_add(
            state=SimpleNamespace(proof_finished=True),
            file="<preamble>",
            theorem="<preamble>",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )
        entry = _state_get(sid)
        fields = _assemble_proof_script(
            entry,
            [
                "Require Import Lia.",
                "Lemma l : forall n m : nat, n + m = m + n.",
                "Proof.",
                "lia.",
            ],
        )
        assert fields["statement_source"] == "session_commands"
        script = fields["proof_script"]
        assert script.startswith("Require Import Lia.\n\nLemma l")
        assert script.rstrip().endswith("Proof.\n  lia.\nQed.")

    def test_unrecoverable(self):
        from rocq_mcp.interactive import _assemble_proof_script, _state_add, _state_get

        sid = _state_add(
            state=SimpleNamespace(proof_finished=True),
            file="A.v",
            theorem="@pos(3,0)",
            workspace="/tmp",
            parent_id=None,
            tactic=None,
            step=0,
        )
        entry = _state_get(sid)
        fields = _assemble_proof_script(entry, ["intros.", "auto."])
        assert fields == {"statement_source": "unrecoverable"}

    def test_run_check_returns_proof_script_end_to_end(self, tmp_path):
        """Through run_check with a mock pet: proof_finished responses now
        carry the assembled script."""
        import rocq_mcp.interactive as _interactive
        import rocq_mcp.server as srv

        source = "Theorem t_ok : True.\nAdmitted.\n"
        vfile = tmp_path / "T.v"
        vfile.write_text(source)

        _interactive._state_table.clear()
        _interactive._state_next_id = 1
        sid = _interactive._state_add(
            state=SimpleNamespace(st=1, proof_finished=False, feedback=[]),
            file="T.v",
            theorem="t_ok",
            workspace=str(tmp_path),
            parent_id=None,
            tactic=None,
            step=0,
            resolved_file=str(vfile),
        )

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(st=2, proof_finished=True, feedback=[])

        import sys
        from types import SimpleNamespace as NS
        from unittest.mock import MagicMock

        if "pytanque" not in sys.modules:
            sys.modules["pytanque"] = NS(
                PetanqueError=type("PetanqueError", (Exception,), {"message": ""}),
                Pytanque=MagicMock,
                PytanqueMode=NS(STDIO="stdio"),
            )
        pet = MagicMock()
        pet.process = MagicMock()
        pet.process.poll.return_value = None
        pet.run = fake_run
        pet.complete_goals.return_value = _complete([])

        ls = {"pet_client": pet, "pet_timeout": 5.0, "current_workspace": str(tmp_path)}
        srv_sem = srv._pet_semaphore
        srv._pet_semaphore = None
        try:
            with patch.object(srv, "_ensure_pet", return_value=pet):
                result = asyncio.run(
                    _interactive.run_check(
                        body="exact I.", lifespan_state=ls, from_state=sid
                    )
                )
        finally:
            srv._pet_semaphore = srv_sem

        assert result["proof_finished"] is True
        assert result["proof_tactics"] == ["exact I."]
        assert result["statement_source"] == "file"
        assert result["proof_script"] == (
            "Theorem t_ok : True.\nProof.\n  exact I.\nQed.\n"
        )
        assert "proof_script" in result["proof_hint"]


class TestMultiErrorStartArgs:
    def test_entries_carry_start_args(self, monkeypatch, tmp_path):
        """The errors list entries gain a ready-made position payload."""
        import rocq_mcp.compile_enrichment as ce
        from rocq_mcp.proof_walk import ProofError

        # The file must resolve inside the workspace, or the orchestrator
        # early-returns with state_capture_status="no_position" before the
        # multi-error walk runs.
        (tmp_path / "Broken.v").write_text("Theorem broken_thm : True.\nbad.\n")

        async def fake_walk(resolved_file, lifespan_state):
            return [
                ProofError(
                    proof_name="broken_thm",
                    kind="Theorem",
                    start_line=4,
                    end_line=7,
                    code=1,
                    message="boom",
                )
            ]

        def fake_compile(*args, **kwargs):
            # run_compile_file is synchronous.
            return {
                "success": False,
                "reason": "compile_error",
                "error": "x",
            }

        monkeypatch.setattr(ce, "_multi_error_walk", fake_walk)
        monkeypatch.setattr(ce, "run_compile_file", fake_compile)
        monkeypatch.setattr(
            ce, "_enrich_compile_failure", _passthrough_enrich, raising=True
        )

        # _enrich_compile_failure is patched to a passthrough, so no pet
        # is needed; the walk itself is the patched fake.
        result = asyncio.run(
            ce.run_compile_file_with_state(
                file="Broken.v",
                workspace=str(tmp_path),
                timeout=5,
                include_warnings=True,
                lifespan_state={},
            )
        )
        entry = result["errors"][0]
        assert entry["start_args"] == {"file": "Broken.v", "line": 4, "character": 0}


async def _passthrough_enrich(result, *args, **kwargs):
    return result
