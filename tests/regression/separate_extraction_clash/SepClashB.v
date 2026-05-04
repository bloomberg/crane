From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Definition clash_add (n m : nat) : nat := n + m + 1.

Definition only_b (n : nat) : nat := n + 2.

Crane Separate Extraction clash_add only_b.
