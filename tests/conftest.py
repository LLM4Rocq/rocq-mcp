"""Shared fixtures for rocq-mcp test suite."""

from __future__ import annotations

import shutil

import pytest

# ---------------------------------------------------------------------------
# Availability flags
# ---------------------------------------------------------------------------

COQC_AVAILABLE: bool = shutil.which("coqc") is not None
PET_AVAILABLE: bool = shutil.which("pet") is not None


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
        "Lemma helper : forall n, n = n. Admitted.\n\n"
        "Theorem add_0_r : forall n : nat, n + 0 = n.\n"
        "Proof.\n"
        "  intros n. apply helper.\n"
        "Qed.\n"
    )


@pytest.fixture
def timeout_proof():
    """A proof that loops forever, causing subprocess timeout.

    Uses a recursive Ltac that truly diverges. The test must use a short
    subprocess timeout (e.g. 3s) to trigger TimeoutExpired.
    """
    return (
        "Ltac loop := idtac; loop.\n"
        "Theorem loop_thm : True.\n"
        "Proof.\n"
        "  loop.\n"
        "Qed.\n"
    )


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
