(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: PrimInt63 arithmetic operations. *)

From Stdlib Require Import PrimInt63.

Module Int63Arith.

Definition i_zero : int := 0%int63.
Definition i_one : int := 1%int63.

Definition i_add : int := add 10 20.
Definition i_mul : int := mul 6 7.
Definition i_sub : int := sub 50 8.

Definition i_eqb_true : bool := eqb 42 42.
Definition i_eqb_false : bool := eqb 42 43.
Definition i_ltb_true : bool := ltb 3 5.
Definition i_ltb_false : bool := ltb 5 3.
Definition i_leb_true : bool := leb 3 3.
Definition i_leb_false : bool := leb 5 3.

Definition i_abs (x : int) : int :=
  if ltb x 0 then sub 0 x else x.

Definition test_abs_pos : int := i_abs 42.
Definition test_abs_neg : int := i_abs (sub 0 42).

End Int63Arith.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extraction "int63_arith" Int63Arith.
