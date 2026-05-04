From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Definition sum_list (l : list nat) : nat :=
  fold_left Nat.add l 0.

Definition make_pair_list (n m : nat) : list nat :=
  [n; m].

Crane Separate Extraction sum_list make_pair_list.
