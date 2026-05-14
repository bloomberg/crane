From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Definition sep_add (n m : nat) : nat := n + m.

Inductive color : Type :=
| Red : color
| Green : color
| Blue : color.

Definition color_to_nat (c : color) : nat :=
  match c with
  | Red => 1
  | Green => 2
  | Blue => 3
  end.

Crane Separate Extraction sep_add color color_to_nat.
