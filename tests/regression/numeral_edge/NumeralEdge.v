(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for numeral folding. *)

From Corelib Require Import PrimInt63.
From Stdlib Require Import BinNat BinPos BinInt.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Import Mapping.NInt Mapping.ZInt.

Module NumeralEdge.

(** 1. Zero *)
Definition nat_zero : nat := 0.
Definition n_zero : N := 0%N.
Definition z_zero : Z := 0%Z.

(** 2. Small values *)
Definition nat_one : nat := 1.
Definition nat_ten : nat := 10.
Definition z_neg : Z := (-5)%Z.
Definition z_neg_one : Z := (-1)%Z.

(** 3. Moderate values *)
Definition nat_hundred : nat := 100.
Definition z_thousand : Z := 1000%Z.
Definition n_large : N := 65535%N.

(** 4. Powers of 2 *)
Definition nat_pow2_8 : nat := 256.
Definition nat_pow2_16 : nat := 65536.
Definition z_pow2_30 : Z := 1073741824%Z.

(** 5. Numerals in arithmetic expressions *)
Definition add_numerals : nat := 100 + 200.
Definition mul_numerals : Z := (10 * 20)%Z.
Definition sub_numerals : Z := (100 - 1)%Z.

(** 6. Numeral as function argument *)
Definition take_nat (n : nat) : nat := n + 1.
Definition test_arg : nat := take_nat 42.

(** 7. Numeral in list *)
Definition nat_list : list nat := cons 1 (cons 2 (cons 3 nil)).

(** 8. Numeral in option *)
Definition some_nat : option nat := Some 99.

(** 9. Numeral in pair *)
Definition nat_pair : nat * nat := (10, 20).

(** 10. Numeral in match *)
Definition classify (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | _ => 2
  end.

(** 11. Comparison with numeral *)
Definition is_big (n : nat) : bool := Nat.leb 100 n.

(** 12. Multiple Z values in one function *)
Definition z_arith : Z := (Z.add 10 (Z.mul 3 7))%Z.

(** 13. Negative Z in a pair *)
Definition z_pair : Z * Z := ((-42)%Z, 42%Z).

(** 14. N conversion *)
Definition n_to_nat_test : nat := N.to_nat 255%N.

End NumeralEdge.

Crane Extraction "numeral_edge" NumeralEdge.
