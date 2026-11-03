(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loops built tail modulo cons whose turns the Perceus reuse cursor
    cannot all follow, or follows only by reading first what the turn reads
    of the cell it rebuilds.

    The cursor holds the cell it stands on by an owning handle, steals the
    field it walks on to, and rebuilds the cell as the turn's outermost one.
    [keep_even] walks on by a turn building nothing, which left the handle
    on the cell it had left: the next steal took a field out of a cell the
    loop did not own, emptying the caller's shared list.  [swap] walks two
    cells at a time: the field it stole was the second cell's, whose
    uniqueness nothing tested.  [stutter], [scale] and [suffix_sums] read the
    cell after the steal or the rebuilding: the inner cell's argument, the
    next accumulator, and the walked list whole, each through the rebuilt
    cell or the emptied field. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyReuseCursorTurns.

Inductive lst : Type :=
| Nil : lst
| Cons : nat -> lst -> lst.

Fixpoint sum (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x xs => x + sum xs
  end.

Fixpoint keep_even (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => if Nat.even x then Cons x (keep_even xs) else keep_even xs
  end.

Fixpoint swap (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs =>
    match xs with
    | Nil => Cons x Nil
    | Cons y ys => Cons y (Cons x (swap ys))
    end
  end.

Fixpoint stutter (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (S x) (Cons x (stutter xs))
  end.

Fixpoint scale (acc : nat) (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (x * acc) (scale (acc + x) xs)
  end.

Fixpoint suffix_sums (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (sum l) (suffix_sums xs)
  end.

End LoopifyReuseCursorTurns.

Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "loopify_reuse_cursor_turns" LoopifyReuseCursorTurns.
