(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A record merged into its module's struct has a field, and a method,
    whose types are written through a synthesised alias template, for
    [itree noE] in [stateT nat (itree noE) bool].  Its body names the
    enclosing module's own [noE], so it is declared inside that module's
    struct, in front of the first member that writes it.  The record's
    fields and methods are that member, but were written as text that
    needed nothing, so the alias went in front of [mk], after the struct
    that already named it; and the templates were planned with the fields
    and methods read outside any module's element, which gives the alias
    no home and another name. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module RecordFieldCarrierAlias.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Variant noE : Type -> Type := .

  Module Holder.
    Record holder := { run : stateT nat (itree noE) bool; tag : nat }.

    Definition runner (h : holder) : stateT nat (itree noE) bool :=
      run h.
  End Holder.

  Definition mk (m : stateT nat (itree noE) bool) : Holder.holder :=
    {| Holder.run := m; Holder.tag := 1 |}.

  Definition five : nat := 5.
End RecordFieldCarrierAlias.

Crane Extraction "record_field_carrier_alias" RecordFieldCarrierAlias.
