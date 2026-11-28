(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Fibonacci with two ST references updated in a loop (after
    https://wiki.haskell.org/Monad/ST), next to the pure definition.
    [STFibonacciProofs] shows that the two agree. *)

From Stdlib Require Import Arith.PeanoNat.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Monads.ST.
From Crane Require Import
  Mapping.NatInt
  Monads.Error
  Monads.ITree
.

Import Monads.
Local Open Scope monad_scope.

Section Fibonacci.

  (** The programs are polymorphic in [R], as [ST.run] requires. *)
  Context {R : ST.Refs}.
  (** Effects of a program whose store holds only [nat]s. *)
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  (** Run [k] steps of [(x, y) := (y, x + y)] and return [x]. *)
  Fixpoint fib_loop (k : nat) (x y : ST.ref nat) : itree E0 nat :=
    match k with
    | 0 => ST.read_ref x
    | Datatypes.S k' =>
        x' <- ST.read_ref x;;
        y' <- ST.read_ref y;;
        ST.write_ref x y';;
        ST.write_ref y (x' + y');;
        fib_loop k' x y
    end.

  (** The [n]th Fibonacci number, computed in two references. *)
  Definition fib_ST (n : nat) : itree E0 nat :=
    if Nat.ltb n 2
    then Ret n
    else
      x <- ST.new_ref 0;;
      y <- ST.new_ref 1;;
      fib_loop n x y.

End Fibonacci.

(** The [n]th Fibonacci number by the doubly recursive definition. *)
Definition fib_fun (n : nat) : nat :=
  let fix fib' (n : nat) :=
    match n with
    | 0 => 0
    | 1 => 1
    | Datatypes.S (Datatypes.S m as m0) => fib' m0 + fib' m
    end in
  fib' n.

Module STFibonacci.
  (** [fib_ST] at the C++ references, its loop unfolded in place. *)
  Definition fib_ST := Eval unfold fib_ST, fib_loop in (@fib_ST ST.cpp_refs).
  (** [fib_fun], unfolded so it extracts here. *)
  Definition fib_fun := Eval unfold fib_fun in fib_fun.
End STFibonacci.

Set Crane Loopify.

Crane Extraction "st_fibonacci" STFibonacci.
