(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Perceus reuse where the rebuilt node uses one of the old node's fields
    twice.  The reuse arm generated its body under the pattern's binders but
    kept the function's move sets as they were outside them, so the de Bruijn
    index that had named the scrutinee -- owned, and dead after the match --
    named the innermost field instead: [Cons x (app2 xs xs)] moved [xs] into
    both arguments, and the second read a moved-from list. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ReuseArmFieldUsedTwice.

Inductive lst : Type :=
| Nil : lst
| Cons : nat -> lst -> lst.

Fixpoint len (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons _ xs => S (len xs)
  end.

Fixpoint app2 (a b : lst) : lst :=
  match a with
  | Nil => b
  | Cons x xs => Cons x (app2 xs b)
  end.

Definition dbl (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons x (app2 xs xs)
  end.

Fixpoint pairs (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (x + len xs) (pairs xs)
  end.

Fixpoint sum (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x xs => x + sum xs
  end.

Definition l3 : lst := Cons 1 (Cons 2 (Cons 3 Nil)).

Definition dbl_len : nat := len (dbl l3).
Definition pairs_sum : nat := sum (pairs l3).

End ReuseArmFieldUsedTwice.

Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "reuse_arm_field_used_twice" ReuseArmFieldUsedTwice.
