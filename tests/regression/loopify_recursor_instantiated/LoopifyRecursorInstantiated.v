(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** A recursor of a type-indexed family, loopified and instantiated.

    [expr_rect] reads its recursive calls through a coercion, at the motive
    of the index each constructor fixes.  Normalize left them in place,
    ordinary C++ calls inside the machine, and a call left there names no
    instantiation: the recursor's C++ spells its motive [T1] only in its
    result type, nothing deduces it (wip/recursor_self_call_no_motive), and
    [size] did not compile.  Each is now bound at the motive, which the
    recursor's C++ spells, and the machine resumes after it: a [succE] chain
    a hundred thousand deep runs in one machine. *)
Module LoopifyRecursorInstantiated.

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

Definition size {A} (e : expr A) : nat :=
  expr_rect (fun _ _ => nat)
    (fun _ => 1)
    (fun _ => 1)
    (fun _ n => S n)
    (fun _ _ c _ t _ f => S (c + t + f))
    (fun _ _ _ x _ y => S (x + y))
    (fun _ _ _ p => S p)
    A e.

Definition sample : expr nat := fstE (pairE (succE (lit 3)) (bl true)).

Definition run : nat := size sample.

End LoopifyRecursorInstantiated.

Set Crane Loopify.
Crane Extraction "loopify_recursor_instantiated" LoopifyRecursorInstantiated.
