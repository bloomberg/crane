(* Regression: two user-defined mediating layers in sequence get no iterative drain.

   [t] recurses through [w t], and [w A] holds its payload in a [list A].
   Neither layer alone hides the recursion: [w] is a single-constructor
   wrapper and [list] is list-shaped, both of which the classifier knows.  It
   is the composition it cannot follow, because the wrapper case looks for a
   *direct* self-reference in the wrapper's fields and finds a [list] instead.

   Destroying 300k levels recurses ~t -> ~w<t> -> ~List<t> -> ~t -> ... *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import Stdlib.Lists.List.
Import ListNotations.
Module TwoLevelMediation.
Inductive w (A : Type) : Type := mkw : nat -> list A -> w A.
Arguments mkw {A} _ _.
Inductive t : Type := node : w t -> t.
Definition wrap (k : nat) (acc : t) : t := node (mkw k (acc :: nil)).
Definition empty : t := node (mkw 0 nil).
End TwoLevelMediation.
Crane Extraction "two_level_mediation" TwoLevelMediation.
