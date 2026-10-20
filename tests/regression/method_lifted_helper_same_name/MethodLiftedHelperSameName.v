(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Two methods of an eponymous record each lift a polymorphic local
    fixpoint bound to [len] out of their bodies.  A method body has no
    declaration recorded as the origin of the helpers it lifts, and a
    helper was keyed by its origin and the name of its binder, so the two
    were one helper: [doubled] called [total]'s [len] and counted each
    element once. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module MethodLiftedHelperSameName.

Module Bag.
  Record bag := { nats : list nat; flags : list bool }.

  Definition total (b : bag) : nat :=
    let fix len {B : Type} (xs : list B) : nat :=
      match xs with [] => 0 | _ :: r => S (len r) end in
    len (nats b) + len (flags b).

  Definition doubled (b : bag) : nat :=
    let fix len {B : Type} (xs : list B) : nat :=
      match xs with [] => 0 | _ :: r => S (S (len r)) end in
    len (nats b) + len (flags b).
End Bag.

Definition sample : Bag.bag := {| Bag.nats := [1; 2]; Bag.flags := [true] |}.
Definition t1 : nat := Bag.total sample.
Definition t2 : nat := Bag.doubled sample.

End MethodLiftedHelperSameName.

Crane Extraction "method_lifted_helper_same_name" MethodLiftedHelperSameName.
