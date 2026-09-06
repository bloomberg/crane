(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A typeclass dictionary stored in a record field.  The class was emitted
    as a C++ concept, and a concept cannot be the type of a struct member. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module InstanceInRecord.
Class Monoid (A : Type) := { unit_ : A ; op : A -> A -> A }.
Instance MNat : Monoid nat := { unit_ := 0 ; op := Nat.add }.
Record bundle := { carrierDict : Monoid nat ; seed : nat }.
Definition b : bundle := {| carrierDict := MNat ; seed := 5 |}.
Definition run : nat := @op nat (carrierDict b) (seed b) (@unit_ nat (carrierDict b)).
End InstanceInRecord.

Crane Extraction "instance_in_record" InstanceInRecord.run.
