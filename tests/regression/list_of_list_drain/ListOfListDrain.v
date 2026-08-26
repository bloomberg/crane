(* Regression: recursion nested two list layers deep gets no iterative drain.

   [node : nat -> lst (lst t) -> t].  The [`List] drain walks a [lst X] spine
   without descending into the element, so with [X = lst t] the inner list --
   which is what actually holds the recursive occurrence -- is destroyed
   recursively.

   Recognising the outer [lst] is not enough; the classifier has to follow the
   element type as well.  Build is done with a C++ loop so the failure is
   purely in destruction. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ListOfListDrain.
Inductive lst (A : Type) : Type := nil : lst A | cons : A -> lst A -> lst A.
Arguments nil {A}. Arguments cons {A} _ _.
Inductive t : Type := node : nat -> lst (lst t) -> t.
Definition wrap (k : nat) (acc : t) : t := node k (cons (cons acc nil) nil).
Definition empty : t := node 0 nil.
End ListOfListDrain.
Crane Extraction "list_of_list_drain" ListOfListDrain.
