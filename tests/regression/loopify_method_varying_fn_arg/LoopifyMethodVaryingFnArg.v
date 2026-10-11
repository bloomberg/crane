(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a loopified method whose function argument changes between
    recursive calls does not compile.  [go] becomes a method of [tree] (a
    second inductive in the module makes it one), and methods are
    loopified.  The method takes its function as [template <typename F0>
    F0 &&f], and the loop's frame stores it as [std::decay_t<F0>], a type
    that fits only the caller's own lambda; the recursive call passes a new
    lambda, [fun y => f (y + x)], which does not convert to it.  The free
    function version stores [crane::fn], and so does the method under
    [Crane NoLoopify]. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyMethodVaryingFnArg.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Inductive tagged (A : Type) : A -> Type := Tag : forall x : A, tagged A x.

Fixpoint go (t : tree) (f : nat -> nat) : nat :=
  match t with
  | Leaf => f 0
  | Node l x r => go l (fun y => f (y + x)) + go r f
  end.

Definition result : nat := go (Node (Node Leaf 1 Leaf) 2 Leaf) S.

End LoopifyMethodVaryingFnArg.

Crane Extraction "loopify_method_varying_fn_arg" LoopifyMethodVaryingFnArg.
