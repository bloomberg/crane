(* Regression: three nested list layers get no iterative drain.

   [node : nat -> list (list (list t)) -> t].  Each layer's drain walks its
   own spine but not its element, so only the outermost list is handled and
   the two inner ones -- plus the [t] at the bottom -- recurse.

   Included alongside [list_of_list_drain] because a fix that unwraps exactly
   one element layer would make that test pass and leave this one failing. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import Stdlib.Lists.List.
Import ListNotations.
Module TripleListDrain.
Inductive t : Type := node : nat -> list (list (list t)) -> t.
Definition wrap (k : nat) (acc : t) : t := node k (((acc :: nil) :: nil) :: nil).
Definition empty : t := node 0 nil.
End TripleListDrain.
Crane Extraction "triple_list_drain" TripleListDrain.
