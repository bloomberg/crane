From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsRegression Require Import template_merge_outlined_member.A.
From CraneTestsRegression Require Import template_merge_outlined_member.Aux.
From CraneTestsRegression Require Import template_merge_outlined_member.BoxDec.

Definition sz_is (b : box nat) (n : nat) : bool := Nat.eqb (size b) n.

Definition round (x : box nat) : box nat := roundtrip x.

Crane Extraction "template_merge_outlined_member" sz_is round.
