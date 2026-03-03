(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Equations package — well-founded recursion via Equations. *)

From Stdlib Require Import Arith List Lia.
From Equations Require Import Equations.
Import ListNotations.

Module Equations.

Equations gcd (p : nat * nat) : nat by wf p (lexprod _ _ lt lt) :=
  gcd (0, y) := y;
  gcd (x, 0) := x;
  gcd (x, y) with Nat.ltb x y := {
    | true => gcd (x, y - x);
    | false => gcd (x - y, y)
  }.
Solve All Obligations with intros; try (left; lia) || (right; lia).

Equations collatz_steps (n : nat) : nat by wf n lt :=
  collatz_steps 0 := 0;
  collatz_steps 1 := 0;
  collatz_steps n with Nat.even n := {
    | true => S (collatz_steps (Nat.div2 n));
    | false => S (collatz_steps (3 * n + 1))
  }.
Admit Obligations.

Definition test_gcd : nat := gcd (12, 8).
Definition test_collatz : nat := collatz_steps 6.

End Equations.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "equations" Equations.
