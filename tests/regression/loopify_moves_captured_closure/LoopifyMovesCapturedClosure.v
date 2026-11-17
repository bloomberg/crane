(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a loopified local fixpoint moves a closure bound outside it into
    every continuation frame.  [weigh] does not change between iterations,
    but the loop treats it as one of the fixpoint's varying parameters and
    saves it with [std::move]: [CraneCont_Node{a1, crane_raw(a2),
    std::move(weigh)}].  The second frame moves from the [crane::fn] the
    first left empty, and calling it throws [std::bad_function_call] -- a
    use after move.  The same over a list, in a non-tail and in a tail
    position.  A free variable of list type is not moved. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyMovesCapturedClosure.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Definition sumw (w : nat) (t : tree) : nat :=
  let weigh := fun x => x * w in
  (fix go (t : tree) : nat := match t with Leaf => 0 | Node l x r => go l + weigh x + go r end) t.

Definition in_tree : nat := sumw 2 (Node (Node Leaf 1 Leaf) 1 (Node Leaf 1 Leaf)).

Definition sumw_list (w : nat) (l : list nat) : nat :=
  let weigh := fun x => x * w in
  (fix go (l : list nat) : nat := match l with [] => 0 | x :: t => weigh x + go t end) l.

Definition in_list : nat := sumw_list 2 [1; 2; 3].

Definition sumw_acc (w : nat) (l : list nat) : nat :=
  let weigh := fun x => x * w in
  (fix go (l : list nat) (acc : nat) : nat := match l with [] => acc | x :: t => go t (acc + weigh x) end) l 0.

Definition in_acc : nat := sumw_acc 3 [1; 2].

End LoopifyMovesCapturedClosure.

Set Crane Loopify.
Crane Extraction "loopify_moves_captured_closure" LoopifyMovesCapturedClosure.
