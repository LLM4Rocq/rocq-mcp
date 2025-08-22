(* Simple example Coq file for testing the Rocq MCP server *)

Require Import Arith.

Theorem addnC : forall n m : nat, n + m = m + n.
Admitted.

Theorem mult_comm : forall n m : nat, n * m = m * n.
Admitted.

Require Import Reals.
Open Scope R_scope.

Theorem mathd_algebra_33 :
  forall (x y z : R),
  x <> 0 ->
  2 * x = 5 * y ->
  7 * y = 10 * z ->
  z / x = 7 / 25.