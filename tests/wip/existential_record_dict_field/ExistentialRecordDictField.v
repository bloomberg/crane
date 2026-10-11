(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a record that packs a type together with a parameterised record
    of functions over it does not compile.  In [Pack nat shN 4], the field
    [dict : ShR ty] holds [shN : ShR nat], whose field is a
    [crane::fn<uint64_t(uint64_t)>]; with [ty] erased the field's type is
    [ShR<crane::obj>], and converting the one into the other needs a
    [crane::fn<uint64_t(crane::obj)>] built from a
    [crane::fn<uint64_t(uint64_t)>], a conversion that does not exist.
    [regression/record_with_type_field] covers a function field directly in
    the packing record, not one nested in a parameterised record. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ExistentialRecordDictField.

Record ShR (A : Type) := { sh : A -> nat }.

Definition shN : ShR nat := {| sh := fun n => n |}.

Record packed := Pack { ty : Type; dict : ShR ty; val : ty }.

Definition shp (p : packed) : nat := sh _ (dict p) (val p).

Definition result : nat := shp (Pack nat shN 4).

End ExistentialRecordDictField.

Crane Extraction "existential_record_dict_field" ExistentialRecordDictField.
