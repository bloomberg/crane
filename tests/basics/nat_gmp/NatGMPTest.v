(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Nat Lists.List.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatGMP.

Module NatGMPTest.

Import Nat.

(* Basic arithmetic *)
Definition add_test (a b : nat) := a + b.
Definition mul_test (a b : nat) := a * b.
Definition sub_test (a b : nat) := a - b.

(* Comparisons *)
Definition eqb_test (a b : nat) := eqb a b.
Definition ltb_test (a b : nat) := ltb a b.
Definition leb_test (a b : nat) := leb a b.

(* Pattern matching / pred *)
Definition pred_test (n : nat) := pred n.
Definition match_test (n : nat) : nat :=
  match n with
  | O => 42
  | S m => m
  end.

(* Numeral folding - numbers > 150 will use the format string *)
Definition big_num : nat := 200.
Definition another_big : nat := 1000.

(* Use a literal in computation *)
Definition add_big (n : nat) : nat := n + 200.

End NatGMPTest.

Crane Extract Inductive bool =>
  "bool"
  [ "true" "false" ]
  "if (%scrut) { %br0 } else { %br1 }".

Crane Extraction "nat_gmp" NatGMPTest.
