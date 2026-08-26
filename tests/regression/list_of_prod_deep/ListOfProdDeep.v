(* Regression: recursion nested inside [lst (t * nat)] gets no iterative drain.

   A user-defined list whose element is a [prod] holding the recursive
   occurrence.  The [`List] drain walks the [lst] spine but never descends
   into the element, and the element is exactly where the recursion lives, so
   destruction recurses one C++ frame per level.

   This is [assoc_pair_list] with the *user-defined* list instead of the
   stdlib one and the recursive component first rather than second, which is
   enough to exercise a different path through the classifier. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ListOfProdDeep.
Inductive lst (A : Type) : Type := lnil : lst A | lcons : A -> lst A -> lst A.
Arguments lnil {A}. Arguments lcons {A} _ _.
Inductive t : Type := node : lst (t * nat) -> t.
Definition wrap (k : nat) (acc : t) : t := node (lcons (acc, k) lnil).
Definition empty : t := node lnil.
End ListOfProdDeep.
Crane Extraction "list_of_prod_deep" ListOfProdDeep.
