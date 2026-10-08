(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane SingleThreaded]: the runtime's block heap is one global rather
    than one per thread.  A tree is built and rebuilt, a list is built and
    dropped, and a closure is kept: every kind of block is allocated and
    freed through the global heap. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SingleThreadedHeap.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint insert (k : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf k Leaf
  | Node l k' r => if Nat.ltb k k' then Node (insert k l) k' r else Node l k' (insert k r)
  end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => 1 + size l + size r end.

Definition adder (n : nat) : nat -> nat := fun m => n + m.

Definition result : nat :=
  let t := fold_left (fun t k => insert k t) (seq 0 200) Leaf in
  size t + adder 5 (length (map S (seq 0 1000))).

End SingleThreadedHeap.

Set Crane SharedVariant.
Set Crane NonAtomicRc.
Set Crane SingleThreaded.
Crane Extraction "single_threaded_heap" SingleThreadedHeap.
