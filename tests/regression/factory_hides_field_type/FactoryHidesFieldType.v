(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a constructor's factory method takes its name by lowercasing the
    constructor, and nothing checks the result against the types the
    inductive's other factories mention.  [Pt : pt -> shape] gets the factory
    [shape::pt], which hides the record type [pt] inside [shape], so the
    next factory, [static shape tag(pt a0)], no longer names the type:
    "must use 'struct' tag to refer to type 'pt' in this scope". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FactoryHidesFieldType.

Record pt := { px : nat; py : nat }.

Inductive shape := Pt : pt -> shape | Tag : pt -> shape.

Definition area (s : shape) : nat :=
  match s with Pt p => px p * py p | Tag p => px p end.

Definition result : nat := area (Tag {| px := 2; py := 3 |}) + area (Pt {| px := 2; py := 3 |}).

End FactoryHidesFieldType.

Crane Extraction "factory_hides_field_type" FactoryHidesFieldType.
