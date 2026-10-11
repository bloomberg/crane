(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module type declaring a record becomes a concept that its
    implementations cannot satisfy.  The concept models each field
    projection as a static function, requiring
    [M::px(std::declval<typename M::pt>())], but the implementing module
    emits the record as a struct whose field [px] is a data member, with no
    static projection: "no member named 'px' in 'Impl'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeRecordConcept.

Module Type T. Record pt := { px : nat }. End T.

Module Impl <: T. Record pt := { px : nat }. End Impl.

Module Use (X : T). Definition f (p : X.pt) : nat := S (X.px p). End Use.

Module U := Use Impl.

Definition result : nat := U.f {| Impl.px := 4 |}.

End ModuleTypeRecordConcept.

Crane Extraction "module_type_record_concept" ModuleTypeRecordConcept.
