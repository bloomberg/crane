(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A per-function reuse setting overrides the global flag.
    The global [Crane Reuse] flag is off and [Crane Reuse incr_reused] turns
    it on for one function: only [incr_reused] takes its list owned and
    rebuilds it in place; [incr_fresh], of the same shape, allocates. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module ReusePerFunctionOn.

Inductive lst : Type :=
| Nil : lst
| Cons : nat -> lst -> lst.

Fixpoint incr_reused (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (S x) (incr_reused xs)
  end.

Fixpoint incr_fresh (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (S (S x)) (incr_fresh xs)
  end.

Fixpoint upto (n : nat) : lst :=
  match n with
  | O => Nil
  | S m => Cons n (upto m)
  end.

Fixpoint sum (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x xs => x + sum xs
  end.

End ReusePerFunctionOn.

Set Crane NonAtomicRc.
Crane Reuse ReusePerFunctionOn.incr_reused.
Crane Extraction "reuse_per_function_on" ReusePerFunctionOn.
