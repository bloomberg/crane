(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A tail-modulo-cons loop with the Perceus reuse cursor, where the
    iteration reads the recursive field it walks to besides walking to it.

    [crane::reuse_step] moves that field out of a uniquely owned cell, ahead
    of the cell being recycled into the output.  The new cell's argument
    [x + len xs] in [pairs], and the next accumulator [len xs] in [weigh],
    were evaluated after the step, through the null handle it had left. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyReuseCursorReadsField.

Inductive lst : Type :=
| Nil : lst
| Cons : nat -> lst -> lst.

Fixpoint len (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons _ xs => S (len xs)
  end.

Fixpoint sum (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x xs => x + sum xs
  end.

Fixpoint pairs (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (x + len xs) (pairs xs)
  end.

Fixpoint weigh (acc : nat) (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (x * acc) (weigh (len xs) xs)
  end.

End LoopifyReuseCursorReadsField.

Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "loopify_reuse_cursor_reads_field" LoopifyReuseCursorReadsField.
