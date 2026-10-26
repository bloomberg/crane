(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A loopified method whose recursive calls pass its receiver back
    unchanged.  [wlast] becomes a method of [wrap] taking only [n]: its loop
    varies [n] alone, so no copy of the receiver is made, and the body reads
    the receiver as it was on entry.  It used to read it through a [_self]
    pointer nothing declared. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Set Crane Loopify.

Module MethodInvariantReceiver.
  (** A second inductive in the module is what makes [wlast] methodifiable. *)
  Inductive lst : Set := Nil | Cons : nat -> lst -> lst.
  Inductive wrap : Set := W : lst -> wrap | WW : wrap -> wrap.

  Fixpoint wlast (n : nat) (w : wrap) : wrap :=
    match n with O => w | S k => wlast k w end.

  Fixpoint wraps (n : nat) (w : wrap) : wrap :=
    match n with O => w | S k => WW (wraps k w) end.

  Fixpoint wdepth (w : wrap) : nat :=
    match w with W _ => 0 | WW x => S (wdepth x) end.

  Definition deep : nat := wdepth (wlast 100000 (wraps 3 (W Nil))).
End MethodInvariantReceiver.

Crane Extraction "method_invariant_receiver" MethodInvariantReceiver.
