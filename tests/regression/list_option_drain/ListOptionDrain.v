(* Regression: recursion nested inside [list (option t)] gets no iterative drain.

   The list spine is walked iteratively, but each element is an [optional<t>]
   holding the recursive occurrence, and the drain does not descend into it.

   This is the [assoc_pair_list] shape with [option] instead of [prod] as the
   inner mediator, and it fails the same way -- evidence that the fix has to
   be about following element types in general, not about special-casing one
   more wrapper. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import Stdlib.Lists.List.
Import ListNotations.
Module ListOptionDrain.
Inductive t : Type := node : nat -> list (option t) -> t.
Definition wrap (k : nat) (acc : t) : t := node k (Some acc :: nil).
Definition empty : t := node 0 nil.
End ListOptionDrain.
Crane Extraction "list_option_drain" ListOptionDrain.
