(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Recursive calls under a coercion, in a function Loopify lowers to a
    machine with a stack of frames.

    A type-indexed evaluator reads a recursive result at the type its
    branch gives it, through a coercion: [S (eval x)], [(eval x, eval y)],
    [fst (eval p)].  Normalize binds every recursive call that is not a
    tail call, so that the machine resumes after it, but touches nothing
    under a coercion (only a call matched through one, [if eval c]).  The
    calls above stay ordinary C++ calls inside [eval]'s machine, each
    running a machine of its own, and a [succE] chain a hundred thousand
    deep exhausts the stack.  Binding them needs a temporary whose C++ type
    the coercion can still cast from: typed at the call's instantiated type,
    or at the coercion's source type, the coercion is dropped
    ([_result.first] on a [crane::obj]).

    Expected: stack overflow in [eval].  When fixed: prints ok. *)
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
