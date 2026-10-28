(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** The recursive calls of a type-indexed family's recursor.

    [expr_rect]'s C++ template spells its motive [T1] only in its result
    type, so no argument deduces it, yet its recursive calls write no
    template arguments.  The header compiles until the recursor is
    instantiated, and then no call matches.  Under [Set Crane Loopify] the
    calls Loopify leaves in the machine (those under a coercion, see
    [wip/loopify_coerced_recursive_call]) are written the same way.

    Expected: the C++ test fails to compile (no matching function for call
    to [expr_rect]).  When fixed: prints ok. *)
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
