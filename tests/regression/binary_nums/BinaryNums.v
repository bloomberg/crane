(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Positive/N/Z binary number types from Stdlib. *)

From Stdlib Require Import BinNat BinInt BinPos Nat.

Module BinaryNums.

(* === Positive === *)

Definition pos_one : positive := 1%positive.
Definition pos_five : positive := 5%positive.
Definition pos_add_result : positive := Pos.add 3 7.
Definition pos_mul_result : positive := Pos.mul 4 5.
Definition pos_succ_result : positive := Pos.succ 9.

(* === N (natural with zero) === *)

Definition n_zero : N := 0%N.
Definition n_five : N := 5%N.
Definition n_add_result : N := N.add 10 20.
Definition n_mul_result : N := N.mul 6 7.
Definition n_sub_result : N := N.sub 10 3.
Definition n_pred_result : N := N.pred 5.
Definition n_compare_result : comparison := N.compare 3 5.

(* === Z (integers) === *)

Definition z_zero : Z := 0%Z.
Definition z_pos : Z := 42%Z.
Definition z_neg : Z := (-7)%Z.
Definition z_add_result : Z := Z.add 10 (-3).
Definition z_mul_result : Z := Z.mul (-4) 5.
Definition z_sub_result : Z := Z.sub 3 10.
Definition z_abs_result : Z := Z.abs (-42).
Definition z_compare_result : comparison := Z.compare (-3) 5.

(* === Conversions === *)

Definition pos_to_nat : nat := Pos.to_nat 7.
Definition n_to_nat : nat := N.to_nat 15.
Definition z_to_nat : nat := Z.to_nat 10.

(* === Functions over binary numbers === *)

Definition n_max (a b : N) : N :=
  match N.compare a b with
  | Lt => b
  | _ => a
  end.

Definition z_sign (z : Z) : Z :=
  match z with
  | Z0 => 0
  | Zpos _ => 1
  | Zneg _ => (-1)
  end.

Definition test_n_max : N := n_max 3 7.
Definition test_z_sign_pos : Z := z_sign 5.
Definition test_z_sign_neg : Z := z_sign (-3).
Definition test_z_sign_zero : Z := z_sign 0.

End BinaryNums.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "binary_nums" BinaryNums.
