(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A call can write exactly as many type arguments as its callee has scheme
    variables and still not write one per variable.  [@pick_second P nat]
    writes [P], which has no variable, and [A]; the callee's variables are
    [A] and [B].  Paired by list position, [nat] is handed to [B] -- the
    length agrees, so no count check notices.  Through the schema's binder
    map, [nat] goes to [A] and [B] stays open for the later argument. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TyargEqualCountShift.

Definition pick_second {P : nat -> Prop} {A : Type} {B : Type} (a : A) (b : B) : B := b.

Definition partial_pick := @pick_second (fun n => n = 0) nat.

Definition chosen : bool := partial_pick bool 3 true.

Definition chosen_nat : nat := partial_pick nat 3 9.

Definition full_pick : bool := @pick_second (fun n => n = 0) nat bool 3 false.

End TyargEqualCountShift.

Crane Extraction "tyarg_equal_count_shift" TyargEqualCountShift.
