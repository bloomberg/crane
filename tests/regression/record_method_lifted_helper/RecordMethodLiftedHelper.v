(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A method of an eponymous record merged into its module's struct lifts a
    helper out of its body.  The helper used to travel through a queue the
    next element emptied, so it was called and never declared; it now comes
    back from the methods' generation and is a member beside them. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module RecordMethodLiftedHelper.

Module Bag.
  Record bag := { nats : list nat; flags : list bool }.

  Definition total (b : bag) : nat :=
    let fix len {B : Type} (xs : list B) : nat :=
      match xs with [] => 0 | _ :: r => S (len r) end in
    len (nats b) + len (flags b).
End Bag.

Definition use : nat := Bag.total {| Bag.nats := [1; 2]; Bag.flags := [true] |}.

End RecordMethodLiftedHelper.

Crane Extraction "record_method_lifted_helper" RecordMethodLiftedHelper.
