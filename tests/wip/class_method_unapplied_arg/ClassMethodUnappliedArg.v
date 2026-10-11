(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a two-argument class method passed unapplied to [List.map], so
    that each element is applied to it once, does not compile.  The method
    reaches [map] as the instance's static two-parameter member [opN::op],
    where [map] needs a one-argument function returning another: "no
    matching member function for call to 'map'".  An ordinary two-argument
    definition in the same position is curried at the call
    ([regression/map_over_partial_app]); a dictionary's method is not. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ClassMethodUnappliedArg.

Class Op (A : Type) := { op : A -> A -> A }.
#[export] Instance opN : Op nat := { op := Nat.add }.

Definition adders : list (nat -> nat) := List.map op [1; 2].

Definition result : nat := fold_left (fun a f => f a) adders 0.

End ClassMethodUnappliedArg.

Crane Extraction "class_method_unapplied_arg" ClassMethodUnappliedArg.
