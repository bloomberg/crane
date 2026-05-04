From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Definition clash_add (n m : nat) : nat := n + m.

Definition only_a (n : nat) : nat := n + 1.

Crane Separate Extraction clash_add only_a.
