(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Recursive calls at a constructor's existential types, read at the
    function's own result type, in a function Loopify lowers to a machine
    with a stack of frames.

    In [(eval x, eval y)] each call is at a type [pairE] hides, which no
    C++ type spells, so only the box [eval] returns can hold its value.
    The pair reads it at [eval]'s own result type [A], and translation reads
    a boxed temporary at [A] by casting it to [eval]'s template parameter,
    which in a machine is the outermost call's: a [bool] component would be
    cast to the [nat] of the whole.  So Normalize leaves these calls in
    place, ordinary C++ calls inside [eval]'s machine, and a [fstE]/[pairE]
    nest a hundred thousand deep exhausts the stack.  ([fst (eval p)] reads
    its call through a coercion into a pair, and is bound: see
    [regression/loopify_coerced_recursive_call].)

    Expected: stack overflow in [eval].  When fixed: prints ok. *)
Module LoopifyExistentialRecursiveCall.

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

Fixpoint eval {A} (e : expr A) : A :=
  match e in expr T return T with
  | lit n => n
  | bl b => b
  | succE x => S (eval x)
  | ite c t f => if eval c then eval t else eval f
  | pairE x y => (eval x, eval y)
  | fstE p => fst (eval p)
  end.

Definition sample : expr nat := fstE (pairE (succE (lit 3)) (bl true)).

Definition run : nat := eval sample.

End LoopifyExistentialRecursiveCall.

Set Crane Loopify.
Crane Extraction "loopify_existential_recursive_call" LoopifyExistentialRecursiveCall.
