(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import BinNat BinPos.

Require Crane.Extraction.
Require Crane.Mapping.NInt.

Module NIntTest.

Import N.

(* Arithmetic *)
Definition add_test (a b : N) := N.add a b.
Definition mul_test (a b : N) := N.mul a b.
Definition sub_test (a b : N) := N.sub a b.
Definition div_test (a b : N) := N.div a b.

(* Comparisons *)
Definition eqb_test (a b : N) := N.eqb a b.
Definition ltb_test (a b : N) := N.ltb a b.
Definition leb_test (a b : N) := N.leb a b.

(* Unary *)
Definition succ_test (n : N) := N.succ n.
Definition pred_test (n : N) := N.pred n.
Definition double_test (n : N) := N.double n.

(* Literals *)
Definition zero_val : N := 0%N.
Definition five_val : N := 5%N.
Definition big_val : N := 1000%N.

(* Pattern matching *)
Definition is_zero (n : N) : bool :=
  match n with
  | N0 => true
  | Npos _ => false
  end.

(* Using positive *)
Definition pos_add (a b : positive) := Pos.add a b.
Definition pos_succ (p : positive) := Pos.succ p.

End NIntTest.

Crane Extraction "n_int" NIntTest.
