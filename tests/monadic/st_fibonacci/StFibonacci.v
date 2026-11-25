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
  Monads.STMonad
.

Import Monads.
Local Open Scope monad_scope.

Section Fibonacci.

  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  (** Run [k] steps of [(x, y) := (y, x + y)] and return [x]. *)
  Fixpoint fib_loop (k : nat) (x y : STRef nat) : itree E0 nat :=
    match k with
    | 0 => readSTRef x
    | Datatypes.S k' =>
        x' <- readSTRef x;;
        y' <- readSTRef y;;
        writeSTRef x y';;
        writeSTRef y (x' + y');;
        fib_loop k' x y
    end.

  Definition fib_ST (n : nat) : itree E0 nat :=
    if Nat.ltb n 2
    then Ret n
    else
      x <- newSTRef 0;;
      y <- newSTRef 1;;
      fib_loop n x y.

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
  Definition fib_ST := Eval unfold fib_ST, fib_loop in (@fib_ST cpp_refs).
  Definition fib_fun := Eval unfold fib_fun in fib_fun.
End StFibonacci.

Set Crane Loopify.

Crane Extraction "st_fibonacci" StFibonacci.
