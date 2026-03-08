(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import BinInt BinNat.

Require Crane.Extraction.
Require Crane.Mapping.ZGMP.

Module ZGMPTest.

Import Z.

(* Arithmetic *)
Definition add_test (a b : Z) := Z.add a b.
Definition mul_test (a b : Z) := Z.mul a b.
Definition sub_test (a b : Z) := Z.sub a b.
Definition abs_test (z : Z) := Z.abs z.
Definition opp_test (z : Z) := Z.opp z.

(* Comparisons *)
Definition eqb_test (a b : Z) := Z.eqb a b.
Definition ltb_test (a b : Z) := Z.ltb a b.
Definition leb_test (a b : Z) := Z.leb a b.

(* Literals *)
Definition zero_val : Z := 0%Z.
Definition pos_val : Z := 42%Z.
Definition neg_val : Z := (-7)%Z.
Definition big_val : Z := 1000%Z.

(* Pattern matching *)
Definition z_sign (z : Z) : Z :=
  match z with
  | Z0 => 0
  | Zpos _ => 1
  | Zneg _ => (-1)
  end.

End ZGMPTest.

Crane Extraction "z_gmp" ZGMPTest.
