(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Fibonacci with two ST references updated in a loop (after
    https://wiki.haskell.org/Monad/ST), next to the pure definition.
    [StFibonacciProofs] shows that the two agree. *)

From Stdlib Require Import Arith.PeanoNat.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.STMonad
.

Import Monads.
Local Open Scope monad_scope.

Section Fibonacci.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST : STRefClass T}.

  Let V : T -> Type := fun _ => nat.
  Let E0 := (STEvent T S V) +' exceptE Err.

  (** Run [k] steps of [(x, y) := (y, x + y)] and return [x]. *)
  Fixpoint fib_loop (k : nat) (x y : STRef S nat) (idx_x idx_y : T) : itree E0 nat :=
    match k with
    | 0 => readSTRef (idx := idx_x) x
    | Datatypes.S k' =>
        x' <- readSTRef (idx := idx_x) x;;
        y' <- readSTRef (idx := idx_y) y;;
        writeSTRef (idx := idx_x) x y';;
        writeSTRef (idx := idx_y) y (x' + y');;
        fib_loop k' x y idx_x idx_y
    end.

  Definition fib_ST (n : nat) : itree E0 nat :=
    if Nat.ltb n 2
    then Ret n
    else
      x <- newSTRef zero 0;;
      y <- newSTRef (suc zero) 1;;
      fib_loop n x y zero (suc zero).

End Fibonacci.

Definition fib_fun (n : nat) : nat :=
  let fix fib' (n : nat) :=
    match n with
    | 0 => 0
    | 1 => 1
    | Datatypes.S (Datatypes.S m as m0) => fib' m0 + fib' m
    end in
  fib' n.

Module StFibonacci.
  (* The index instances are unfolded so that they are extracted here. *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.

  Definition fib_ST := Eval unfold fib_ST, fib_loop in (@fib_ST nat unit Nat.le).
  Definition fib_fun := Eval unfold fib_fun in fib_fun.
End StFibonacci.

Set Crane Loopify.

Crane Extraction "st_fibonacci" StFibonacci.
