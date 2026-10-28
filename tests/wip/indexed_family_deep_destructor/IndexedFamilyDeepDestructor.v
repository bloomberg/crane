(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Tearing down a deep value of a type-indexed family.

    A plain inductive whose constructors hold children of its own type is
    destroyed iteratively: its destructor drains the children it owns into
    a worklist rather than recursing.  An indexed family -- [expr], whose
    index a constructor fixes -- gets no such destructor, so destroying a
    [succE] chain recurses once per node and a chain a hundred thousand
    deep exhausts the stack.

    Expected: stack overflow destroying the [expr] chain.  When fixed:
    prints ok. *)
Module IndexedFamilyDeepDestructor.

Inductive expr : Type -> Type :=
| lit : nat -> expr nat
| bl : bool -> expr bool
| succE : expr nat -> expr nat
| ite : forall A : Type, expr bool -> expr A -> expr A -> expr A
| pairE : forall A B : Type, expr A -> expr B -> expr (A * B)
| fstE : forall A B : Type, expr (A * B) -> expr A.
Arguments ite {A} _ _ _.
Arguments pairE {A B} _ _.
Arguments fstE {A B} _.

Definition sample : expr nat := succE (lit 1).

End IndexedFamilyDeepDestructor.

Crane Extraction "indexed_family_deep_destructor" IndexedFamilyDeepDestructor.
