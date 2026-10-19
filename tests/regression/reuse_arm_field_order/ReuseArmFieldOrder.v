(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Perceus reuse for a constructor whose pattern names one field and leaves
    the other anonymous.  The reuse arm decided which fields to bind out of
    the recycled node by reading the pattern's binders last field first
    against the fields first field first, so [Cons x _] bound the anonymous
    tail and not [x], which the body then named undeclared, and [Cons _ xs]
    bound nothing it could recycle and declined reuse. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ReuseArmFieldOrder.

Inductive lst : Type :=
| Nil : lst
| Cons : nat -> lst -> lst.

Fixpoint zero_heads (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons _ xs => Cons 0 (zero_heads xs)
  end.

Definition keep_head (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x _ => Cons x Nil
  end.

Fixpoint sum (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x xs => x + sum xs
  end.

Fixpoint len (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons _ xs => S (len xs)
  end.

Definition l3 : lst := Cons 5 (Cons 6 (Cons 7 Nil)).

Definition zeroed_len : nat := len (zero_heads l3).
Definition zeroed_sum : nat := sum (zero_heads l3).
Definition kept_sum : nat := sum (keep_head l3).
Definition kept_len : nat := len (keep_head l3).

End ReuseArmFieldOrder.

Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "reuse_arm_field_order" ReuseArmFieldOrder.
