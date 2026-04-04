(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Stress test for numeral folding.

   Targets:
   - numerals inside constructors (not standalone)
   - numerals in records
   - numerals inside fixpoints
   - numerals inside pattern matching
   - negative Z in complex expressions
   - numeral used as match scrutinee
*)
From Corelib Require Import PrimInt63.
From Stdlib Require Import BinNat BinPos BinInt.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Import Mapping.NInt Mapping.ZInt.

Module NumeralStress.

(** 1. Numeral inside option *)
Definition opt_100 : option nat := Some 100.
Definition opt_neg : option Z := Some ((-50)%Z).

(** 2. Numeral in a pair *)
Definition pair_nums : (nat * Z) := (42, (-7)%Z).

(** 3. Numeral in a list *)
Definition z_list : list Z := cons 1%Z (cons (-2)%Z (cons 3%Z nil)).

(** 4. Numeral as argument to Nat.add *)
Definition add_big : nat := Nat.add 1000 2000.

(** 5. Numeral in match scrutinee *)
Definition match_numeral : nat :=
  match 42 with
  | O => 0
  | _ => 1
  end.

(** 6. Numeral inside a fixpoint *)
Fixpoint count_from (n : nat) (target : nat) : nat :=
  match n with
  | O => 0
  | S n' =>
    if Nat.eqb n target then n
    else count_from n' target
  end.
Definition test_count : nat := count_from 100 50.

(** 7. Z arithmetic with literals *)
Definition z_complex : Z := Z.add (Z.mul 100 200)%Z (Z.sub 50 25)%Z.

(** 8. Multiple numerals in one record *)
Record point := mk_point { px : nat; py : nat }.
Definition origin : point := mk_point 0 0.
Definition far_point : point := mk_point 999 888.

(** 9. Numeral in boolean expression *)
Definition check_range (n : nat) : bool :=
  andb (Nat.leb 10 n) (Nat.leb n 100).
Definition test_range : bool := check_range 50.

(** 10. Mixed nat and Z in one function *)
Definition mixed_arith (n : nat) : Z :=
  Z.add (Z.of_nat n) 100%Z.
Definition test_mixed : Z := mixed_arith 42.

End NumeralStress.

Crane Extraction "numeral_stress" NumeralStress.
