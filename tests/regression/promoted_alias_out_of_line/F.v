From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import promoted_alias_out_of_line.Defs.

Definition lst {T : Type} (x : T) (l : list (@dval natIPtr)) : nat :=
  match l with nil => 0 | cons _ _ => 1 end.

Definition size (n : nat) : nat := n.
