From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module CpsEscape.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Inductive box : Type :=
| Box : (nat -> nat) -> box.

(** Sum all values in a tree. *)
Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** CPS-style: take a tree, produce a continuation (nat -> nat)
    that adds tree_sum to its argument. The continuation captures t. *)
Definition make_adder (t : tree) : nat -> nat :=
  fun x => tree_sum t + x.

(** Store the continuation in a Box. The function receives the closure
    as an argument and wraps it - the closure flows THROUGH a parameter. *)
Definition store_in_box (f : nat -> nat) : box :=
  Box f.

(** BUG HYPOTHESIS: make_adder creates [&t] lambda.
    store_in_box receives it and puts it in Box.
    When cps_escape returns, t is destroyed but Box holds the lambda.

    Expected: tree_sum(Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf)))
            = 10 + 20 + 30 = 60
            adder 5 = 60 + 5 = 65 *)
Definition cps_escape : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let adder := make_adder t in
  let b := store_in_box adder in
  match b with
  | Box f => f 5
  end.

(** Same but inline: no intermediate let for adder.
    The closure goes directly from make_adder into store_in_box. *)
Definition cps_escape_inline : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b := store_in_box (make_adder t) in
  match b with
  | Box f => f 5
  end.

(** CPS with two stored continuations.
    Build two adders from different trees and store both. *)
Definition cps_escape_two : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let t2 := Node Leaf 100 Leaf in
  let b1 := store_in_box (make_adder t1) in
  let b2 := store_in_box (make_adder t2) in
  match b1 with
  | Box f1 =>
    match b2 with
    | Box f2 => f1 0 + f2 0
    end
  end.

End CpsEscape.

Crane Extraction "cps_escape" CpsEscape.
