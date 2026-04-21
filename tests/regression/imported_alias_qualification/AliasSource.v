From Stdlib Require Import List.

Inductive player : Type :=
| black
| white.

Definition cell : Type := option player.

Definition id_cell (c : cell) : cell := c.

Definition empty_cell : cell := None.
