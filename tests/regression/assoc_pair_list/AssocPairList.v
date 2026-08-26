(* Regression: recursion nested inside [list (nat * t)] gets no iterative drain.

   An association list is the common spelling for a node's children.  The
   [`List] drain walks the [list] spine but not the element, and the element
   here is a [prod] that holds the recursive occurrence, so destruction
   recurses one C++ frame per level.

   Two mediating layers ([list] then [prod]) have to be seen through at once;
   handling either alone does not fix this. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import Stdlib.Lists.List.
Import ListNotations.
Module AssocPairList.
Inductive t : Type := node : list (nat * t) -> t.
Definition wrap (k : nat) (acc : t) : t := node ((k, acc) :: nil).
Definition empty : t := node nil.
Fixpoint count (x : t) : nat :=
  match x with
  | node l => S (fold_left (fun a p => a + count (snd p)) l 0)
  end.
End AssocPairList.
Crane Extraction "assoc_pair_list" AssocPairList.
