(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: binding the fields of a record a call returns evaluated the
    call once per field, so a function taking its own recursive result apart
    into three fields made three recursive calls at every level --
    [FMapAVL]'s [split] among them.  [count 40] made 3^40 calls. *)

From Stdlib Require Import Nat.

Module RecordDestructureOnce.

Record triple : Type := Mk { t_steps : nat; t_twice : nat; t_zero : nat }.

Fixpoint count (n : nat) : triple :=
  match n with
  | O => Mk 0 0 0
  | S m => let (a, b, c) := count m in Mk (S a) (b + 2) c
  end.

Definition r_steps : nat := t_steps (count 40).
Definition r_twice : nat := t_twice (count 40).
Definition r_zero : nat := t_zero (count 40).

End RecordDestructureOnce.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "record_destructure_once" RecordDestructureOnce.
