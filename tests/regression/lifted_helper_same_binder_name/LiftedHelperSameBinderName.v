(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Two polymorphic let-bound lambdas in one declaration, bound to the same
    name in sibling branches, are both lifted to helper templates.  A lifted
    helper was identified by its declaration and the source name of its
    binder, so the second lambda was taken for the first: one helper,
    [two_crane_g], was emitted, and the [false] branch called the [true]
    branch's lambda, so [two false 3] was 4 rather than 2.  The two binders
    are not told apart by name, nor by Core binder level, which is 2 for
    both; a helper is now identified by the occurrence of the let that bound
    it. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LiftedHelperSameBinderName.

Definition two (b : bool) (n : nat) : nat :=
  if b then
    let g := fun (A : Type) (x : A) => [x; x] in
    length (g nat n) + length (g bool true)
  else
    let g := fun (A : Type) (x : A) => [x] in
    length (g nat n) + length (g (list nat) [n]).

Definition t1 : nat := two true 3.
Definition t2 : nat := two false 3.

End LiftedHelperSameBinderName.

Crane Extraction "lifted_helper_same_binder_name" LiftedHelperSameBinderName.
