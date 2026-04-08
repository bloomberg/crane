From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module MethodPartialApp.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** add_to_sum: methodified on first arg (tree).
    Takes a tree and a nat, returns the tree's sum plus the nat. *)
Definition add_to_sum (t : tree) (x : nat) : nat :=
  tree_sum t + x.

(** BUG HYPOTHESIS: Partially apply add_to_sum to get a (nat -> nat) closure.
    If add_to_sum is methodified (becomes t.add_to_sum(x)),
    then partial application "add_to_sum t" needs to capture `t`.
    If the capture is by [&] on a unique_ptr, it could dangle. *)

(** Direct partial app stored in let, called twice. *)
Definition method_partial_bug : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := add_to_sum t in
  f 5 + f 10.

(** Partial app stored in a constructor. *)
Inductive box : Type :=
| Box : (nat -> nat) -> box.

Definition method_partial_box : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b := Box (add_to_sum t) in
  match b with
  | Box f => f 5 + f 10
  end.

(** Two partial apps from different trees. *)
Definition method_partial_two : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f1 := add_to_sum t1 in
  let f2 := add_to_sum t2 in
  f1 0 + f2 0.

End MethodPartialApp.

Crane Extraction "method_partial_app" MethodPartialApp.
