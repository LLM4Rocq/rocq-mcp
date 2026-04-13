"""Tests for per-step feedback collection and _truncate_result utility."""

from __future__ import annotations

import pytest

# ---------------------------------------------------------------------------
# Unit tests for _truncate_result
# ---------------------------------------------------------------------------


class TestTruncateResult:
    """Pure unit tests for the _truncate_result helper."""

    def test_short_text_unchanged(self):
        from rocq_mcp.interactive import _truncate_result

        assert _truncate_result("hello", 100) == "hello"

    def test_exact_length_unchanged(self):
        from rocq_mcp.interactive import _truncate_result

        text = "a" * 50
        assert _truncate_result(text, 50) == text

    def test_over_limit_truncated(self):
        from rocq_mcp.interactive import _truncate_result

        text = "x" * 200
        result = _truncate_result(text, 100)
        assert result.startswith("x" * 100)
        assert "truncated" in result
        assert "200 total chars" in result

    def test_empty_string(self):
        from rocq_mcp.interactive import _truncate_result

        assert _truncate_result("", 100) == ""

    def test_large_output(self):
        """Simulate the 6.5M char vm_compute scenario."""
        from rocq_mcp.interactive import _truncate_result

        big = "Z" * 6_500_000
        result = _truncate_result(big, 50_000)
        assert len(result) < 60_000  # truncated + suffix
        assert result.startswith("Z" * 50_000)
        assert "6500000 total chars" in result


# ---------------------------------------------------------------------------
# Mock-based tests for feedback collection in run_check
# ---------------------------------------------------------------------------


class TestFeedbackCollection:
    """Test per-step feedback collection in run_check.

    Mock-based — does not require pet.
    """

    # Override module-level skip — this class uses mocks, not real pet
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
        """Ensure pytanque is importable even if not installed."""
        import sys
        from types import SimpleNamespace
        from unittest.mock import MagicMock

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
        """Helper: create initial state, mock pet, and lifespan_state."""
        from types import SimpleNamespace
        from unittest.mock import MagicMock

        import rocq_mcp.interactive as _interactive

        _interactive._state_table.clear()
        _interactive._state_next_id = 1
        _interactive._state_current_id = None

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

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        return sid, mock_pet, lifespan_state

    @pytest.mark.asyncio
    async def test_feedback_collected_on_success(self):
        """Feedback from steps with output appears in success result."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        call_count = 0

        def fake_run(state, cmd, timeout=None):
            nonlocal call_count
            call_count += 1
            return SimpleNamespace(
                st=100 + call_count,
                proof_finished=False,
                feedback=[(3, f"output from {cmd}")],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="Print nat. Check True.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert "feedback" in result
        fb = result["feedback"]
        assert len(fb) == 2
        assert fb[0][0] == "Print nat."
        assert "output from Print nat." in fb[0][1]
        assert fb[1][0] == "Check True."
        assert "output from Check True." in fb[1][1]

    @pytest.mark.asyncio
    async def test_feedback_absent_when_empty(self):
        """No feedback key when all steps produce empty feedback."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(st=200, proof_finished=False, feedback=[])

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="intros.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert "feedback" not in result

    @pytest.mark.asyncio
    async def test_feedback_on_error(self):
        """Feedback from successful steps is preserved when a later step fails."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import sys

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        PetanqueError = sys.modules["pytanque"].PetanqueError

        call_count = 0

        def fake_run(state, cmd, timeout=None):
            nonlocal call_count
            call_count += 1
            if call_count == 2:
                try:
                    err = PetanqueError(0, "tactic failed")
                except TypeError:
                    err = PetanqueError()
                err.message = "tactic failed"
                raise err
            return SimpleNamespace(
                st=300 + call_count,
                proof_finished=False,
                feedback=[(1, "step1 output")],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="intros. bad_tactic.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is False
        assert "feedback" in result
        fb = result["feedback"]
        assert len(fb) == 1
        assert fb[0][0] == "intros."
        assert "step1 output" in fb[0][1]

    @pytest.mark.asyncio
    async def test_feedback_truncated_per_step(self):
        """Each step's feedback is truncated independently."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        big_output = "X" * 100_000

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(
                st=400,
                proof_finished=False,
                feedback=[(1, big_output)],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="Print nat. Check True.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert "feedback" in result
        fb = result["feedback"]
        assert len(fb) == 2
        for tactic, text in fb:
            assert len(text) < 60_000  # well under 100k
            assert "truncated" in text
            assert "100000 total chars" in text

    @pytest.mark.asyncio
    async def test_feedback_skips_empty_steps(self):
        """Only steps with non-empty feedback appear in the list."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        call_count = 0

        def fake_run(state, cmd, timeout=None):
            nonlocal call_count
            call_count += 1
            if call_count == 2:
                # Step 2 has no feedback
                return SimpleNamespace(
                    st=500 + call_count, proof_finished=False, feedback=[]
                )
            return SimpleNamespace(
                st=500 + call_count,
                proof_finished=False,
                feedback=[(1, f"output{call_count}")],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="cmd1. cmd2. cmd3.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert "feedback" in result
        fb = result["feedback"]
        assert len(fb) == 2  # only steps 1 and 3
        assert fb[0][0] == "cmd1."
        assert "output1" in fb[0][1]
        assert fb[1][0] == "cmd3."
        assert "output3" in fb[1][1]

    @pytest.mark.asyncio
    async def test_multiple_feedback_messages_per_step(self):
        """Multiple feedback items in one step are joined with newlines."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(
                st=600,
                proof_finished=False,
                feedback=[(1, "first line"), (3, "second line"), (1, "third")],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="Print nat.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        fb = result["feedback"]
        assert len(fb) == 1
        assert "first line\nsecond line\nthird" in fb[0][1]

    @pytest.mark.asyncio
    async def test_empty_string_messages_filtered(self):
        """Empty-string feedback messages are filtered out."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(
                st=700,
                proof_finished=False,
                feedback=[(3, ""), (1, "real output"), (3, "")],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="cmd.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        fb = result["feedback"]
        assert len(fb) == 1
        assert fb[0][1] == "real output"

    @pytest.mark.asyncio
    async def test_all_empty_string_messages(self):
        """When every feedback message is empty, no feedback key appears."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(
                st=900,
                proof_finished=False,
                feedback=[(3, ""), (1, ""), (3, "")],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body="cmd.",
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        assert "feedback" not in result

    @pytest.mark.asyncio
    async def test_total_feedback_cap_precise(self):
        """Total cap stops collection at exactly 4 steps of 50K each."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        call_count = 0

        def fake_run(state, cmd, timeout=None):
            nonlocal call_count
            call_count += 1
            # Each step produces exactly 50K chars (at the per-step limit)
            return SimpleNamespace(
                st=1000 + call_count,
                proof_finished=False,
                feedback=[(1, "X" * 50_000)],
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        body = " ".join(f"cmd{i}." for i in range(10))
        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_check(
                body=body,
                timeout=30.0,
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert result["success"] is True
        fb = result["feedback"]
        # 200K total / 50K per step = 4 steps collected
        assert len(fb) == 4
        total = sum(len(text) for _, text in fb)
        assert total == 200_000

    def test_exact_boundary_not_truncated(self):
        """Text at exactly _MAX_FEEDBACK_LENGTH passes through unchanged."""
        from rocq_mcp.interactive import _MAX_FEEDBACK_LENGTH, _truncate_result

        text = "a" * _MAX_FEEDBACK_LENGTH
        assert _truncate_result(text, _MAX_FEEDBACK_LENGTH) == text
        assert _MAX_FEEDBACK_LENGTH == 50_000


# ---------------------------------------------------------------------------
# Mock-based tests for feedback collection in run_step_multi
# ---------------------------------------------------------------------------


class TestStepMultiFeedback:
    """Test per-tactic feedback in run_step_multi. Mock-based."""

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
        from unittest.mock import MagicMock

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
        from unittest.mock import MagicMock

        import rocq_mcp.interactive as _interactive

        _interactive._state_table.clear()
        _interactive._state_next_id = 1
        _interactive._state_current_id = None

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

        lifespan_state = {
            "pet_client": mock_pet,
            "pet_timeout": 30.0,
            "current_workspace": "/tmp",
        }

        return sid, mock_pet, lifespan_state

    @pytest.mark.asyncio
    async def test_step_multi_feedback_collected(self):
        """Feedback appears in per-tactic result entries."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            fb = [(3, f"output of {cmd}")] if "Print" in cmd else []
            return SimpleNamespace(st=100, proof_finished=False, feedback=fb)

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_step_multi(
                tactics=["auto.", "Print nat."],
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        results = result["results"]
        assert len(results) == 2
        # auto. has no feedback
        assert "feedback" not in results[0]
        # Print nat. has feedback
        assert "feedback" in results[1]
        assert "output of Print nat." in results[1]["feedback"]

    @pytest.mark.asyncio
    async def test_step_multi_feedback_truncated(self):
        """Large per-tactic feedback is truncated."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(
                st=200, proof_finished=False, feedback=[(1, "Y" * 100_000)]
            )

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_step_multi(
                tactics=["auto."],
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        fb = result["results"][0]["feedback"]
        assert len(fb) < 60_000
        assert "truncated" in fb
        assert "100000 total chars" in fb

    @pytest.mark.asyncio
    async def test_step_multi_feedback_absent_when_empty(self):
        """No feedback key when tactic produces no output."""
        from types import SimpleNamespace
        from unittest.mock import patch

        import rocq_mcp.server
        import rocq_mcp.interactive as _interactive

        def fake_run(state, cmd, timeout=None):
            return SimpleNamespace(st=300, proof_finished=False, feedback=[])

        sid, mock_pet, lifespan_state = self._setup_state_and_pet(fake_run)

        with patch.object(rocq_mcp.server, "_ensure_pet", return_value=mock_pet):
            result = await _interactive.run_step_multi(
                tactics=["auto."],
                lifespan_state=lifespan_state,
                from_state=sid,
            )

        assert "feedback" not in result["results"][0]
