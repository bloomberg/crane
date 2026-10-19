(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: two polymorphic let-bound lambdas in one declaration, bound
    to the same name in sibling branches, are both lifted to helper
    templates, and a lifted helper is identified by its declaration and the
    source name of its binder ([Lifted.Key]).  The second lambda is taken for
    the first: one helper, [two_crane_g], is emitted, and the [false] branch
    calls the [true] branch's lambda, so [two false 3] is 4 rather than 2.
    Under [CRANE_CHECK_IR] extraction stops at the "lifted helpers" check.

    The two binders are not told apart by name, nor by Core binder level,
    which is 2 for both.  What identifies a let is its binding occurrence,
    which [MLletin] does not carry ([MLfix] carries one); the fix is to give
    it one and key the helper by it. *)

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
