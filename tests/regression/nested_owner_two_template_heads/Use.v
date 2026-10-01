From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsRegression Require Import nested_owner_two_template_heads.A.
From CraneTestsRegression Require Import nested_owner_two_template_heads.Aux.
From CraneTestsRegression Require Import nested_owner_two_template_heads.Bag.
From CraneTestsRegression Require Import nested_owner_two_template_heads.BagUtil.

Definition count_odd_is (b : bag nat) (n : nat) : bool :=
  Nat.eqb (countIf (fun x => Nat.odd x) b) n.

Definition limit : nat := depth_limit.

Definition round (b : bag nat) : bag nat := roundtrip b.

Crane Extraction "nested_owner_two_template_heads" count_odd_is limit round.
