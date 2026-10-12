(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a value of a type computed from an index, built at a
    container that a [Crane Extract Inductive] mapping provides, boxes its
    payload but keeps the mapping's concrete type argument.  Deep erasure
    stores [den (TOpt a)] as an [option] of boxes, and Crane's own [List]
    is built that way ([regression/den_value_not_deep_erased]); a mapped
    constructor template's [%t0] is still filled with the concrete type:
    [std::make_optional<std::optional<uint64_t>>(crane::obj(...))] for the
    literal [Some (Some 5)] and for the call [mk n]: "no matching function
    for call to 'make_optional'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ValueFamilyOverMappedContainer.

Inductive ty := TNat | TOpt : ty -> ty.

Fixpoint den (t : ty) : Type := match t with TNat => nat | TOpt a => option (den a) end.

Fixpoint sz (t : ty) : den t -> nat :=
  match t return den t -> nat with
  | TNat => fun n => n
  | TOpt a => fun o => match o with Some x => S (sz a x) | None => 0 end
  end.

Definition v : den (TOpt (TOpt TNat)) := Some (Some 5).
Definition from_literal : nat := sz (TOpt (TOpt TNat)) v.

Definition mk (n : nat) : den (TOpt TNat) := Some n.
Definition from_call : nat := sz (TOpt TNat) (mk 4).

End ValueFamilyOverMappedContainer.

Crane Extraction "value_family_over_mapped_container" ValueFamilyOverMappedContainer.
