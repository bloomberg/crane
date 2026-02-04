(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test boolean operations *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module BoolOps.

(* Basic boolean values *)
Definition bool_true : bool := true.
Definition bool_false : bool := false.

(* Negation *)
Definition my_negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* And *)
Definition my_andb (a b : bool) : bool :=
  match a with
  | true => b
  | false => false
  end.

(* Or *)
Definition my_orb (a b : bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

(* Xor *)
Definition my_xorb (a b : bool) : bool :=
  match a, b with
  | true, false => true
  | false, true => true
  | _, _ => false
  end.

(* If-then-else *)
Definition if_nat (b : bool) (t f : nat) : nat :=
  if b then t else f.

(* Complex boolean expression *)
Definition complex_bool (a b c : bool) : bool :=
  my_orb (my_andb a b) (my_andb (my_negb a) c).

(* Boolean from comparison *)
Definition nat_eq (a b : nat) : bool := Nat.eqb a b.
Definition nat_lt (a b : nat) : bool := Nat.ltb a b.
Definition nat_le (a b : nat) : bool := Nat.leb a b.

(* Test values *)
Definition test_neg_t := my_negb true.
Definition test_neg_f := my_negb false.
Definition test_and_tt := my_andb true true.
Definition test_and_tf := my_andb true false.
Definition test_or_ff := my_orb false false.
Definition test_or_ft := my_orb false true.
Definition test_xor_tt := my_xorb true true.
Definition test_xor_tf := my_xorb true false.
Definition test_if_t := if_nat true five three.
Definition test_if_f := if_nat false five three.
Definition test_complex := complex_bool true false true.
Definition test_eq_tt := nat_eq five five.
Definition test_eq_tf := nat_eq five three.
Definition test_lt := nat_lt three five.

End BoolOps.

Crane Extraction "bool_ops" BoolOps.
