(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a definition whose type is an alias for a rank-2 function type
    -- a Church encoding such as [clist A := forall R, (A -> R -> R) -> R ->
    R] -- cannot be used as a value.  Its function-typed parameter is
    generalised to [template <typename F0> F0&&], which makes the definition
    a function template, and the places that use it as a value name that
    template bare: [crane_erase_global<fnil, crane::obj>()],
    [crane_erase_fn<crane::obj>(cnil<uint64_t>)] and [crane_convert<...>(bnat)]
    all fail to deduce.  A definition of type [forall A, (A -> A) -> A -> A]
    ([regression/rank1_polymorphic_definition]) and an ordinary
    higher-order definition used as a value work. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module Rank2AliasDefinitionAsValue.

Definition clist (A : Type) := forall R, (A -> R -> R) -> R -> R.
Definition cnil {A} : clist A := fun R c n => n.
Definition csum (l : clist nat) : nat := l nat Nat.add 0.

Definition nfold := forall R, (nat -> R -> R) -> R -> R.
Definition fnil : nfold := fun R c n => n.
Definition fsum (l : nfold) : nat := l nat Nat.add 0.

Definition box (A : Type) := forall R, (A -> R) -> R.
Definition bnat : box nat := fun R k => k 3.
Definition unbox (b : box nat) : nat := b nat (fun x => x).

Definition result : nat := csum cnil + fsum fnil + unbox bnat.

End Rank2AliasDefinitionAsValue.

Crane Extraction "rank2_alias_definition_as_value" Rank2AliasDefinitionAsValue.
