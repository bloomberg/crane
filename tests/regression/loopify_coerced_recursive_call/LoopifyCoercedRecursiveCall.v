(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Recursive calls under a coercion, in a function Loopify lowers to a
    machine with a stack of frames.

    A type-indexed evaluator reads a recursive result at the type its
    branch gives it, through a coercion: [S (eval x)], [fst (eval p)],
    [if eval c].  Normalize bound only the last, and the others stayed
    ordinary C++ calls inside [eval]'s machine, each running a machine of
    its own: a [succE] chain a hundred thousand deep exhausted the stack.
    Normalize now binds a call under a coercion like any other, the
    coercion kept around the temporary.  [eval] returns its result boxed;
    the temporary of [eval x] is declared at [nat] and cast where it is
    bound, while that of [eval p], at the [A * B] that [fstE] hides and no
    C++ type spells, stays the box the coercion opens. *)
Module LoopifyCoercedRecursiveCall.

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

End LoopifyCoercedRecursiveCall.

Set Crane Loopify.
Crane Extraction "loopify_coerced_recursive_call" LoopifyCoercedRecursiveCall.
