(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A per-function reuse setting overrides the global flag.
    The global [Crane Reuse] flag is on and [Crane NoReuse incr_fresh] turns
    it off for one function: only [incr_reused] takes its list owned and
    rebuilds it in place; [incr_fresh], of the same shape, allocates. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ReusePerFunctionOff.

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

End ReusePerFunctionOff.

Set Crane NonAtomicRc.
Set Crane Reuse.
Crane NoReuse ReusePerFunctionOff.incr_fresh.
Crane Extraction "reuse_per_function_off" ReusePerFunctionOff.
