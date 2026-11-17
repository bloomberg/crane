(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** The recursive calls of a type-indexed family's recursor.

    [expr_rect]'s C++ template spells its motive [T1] only in its result
    type, so no argument deduces it.  Its recursive calls wrote no template
    arguments, leaving every one to deduction from the recursive argument,
    as for a nested inductive, whose self-calls are at another
    instantiation; but [expr]'s C++ type takes no index, so the header
    compiled until the recursor was instantiated, and then no call matched.
    The calls now write the motive. *)
Module RecursorSelfCallNoMotive.

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

Definition sample : expr nat := fstE (pairE (succE (lit 3)) (bl true)).

End RecursorSelfCallNoMotive.

Crane Extraction "recursor_self_call_no_motive" RecursorSelfCallNoMotive.
