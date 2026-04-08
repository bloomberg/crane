From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module MapPartialApp.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** wrap: takes tree and nat, builds Node with leaves. *)
Definition wrap (t : tree) (v : nat) : tree :=
  Node t v Leaf.

(** Sum a list of nats. *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: rest => x + sum_list rest
  end.

(** BUG HYPOTHESIS: Create a partial application (wrap t), store it,
    then apply it to multiple values from a list via map.
    The same closure is invoked repeatedly through list traversal.
    If std::move(t) is inside the lambda, first invocation moves t,
    subsequent ones get null.

    Expected:
      t = Node Leaf 10 Leaf (sum = 10)
      f = wrap t
      map (fun v => tree_sum (f v)) [1; 2; 3]
        = [tree_sum(Node(t,1,Leaf)); tree_sum(Node(t,2,Leaf)); tree_sum(Node(t,3,Leaf))]
        = [10+1; 10+2; 10+3]
        = [11; 12; 13]
      sum_list [11; 12; 13] = 36 *)
Definition map_partial_bug : nat :=
  let t := Node Leaf 10 Leaf in
  let f := wrap t in
  let results := map (fun v => tree_sum (f v)) (1 :: 2 :: 3 :: nil) in
  sum_list results.

(** Variation: store the partial app in a pair, extract it, then map.
    Extra indirection through pair. *)
Definition map_partial_pair : nat :=
  let t := Node Leaf 10 Leaf in
  let f := wrap t in
  let p := (f, 0) in
  let results := map (fun v => tree_sum (fst p v)) (1 :: 2 :: 3 :: nil) in
  sum_list results.

(** Variation: two closures mapped over same list. *)
Definition map_two_closures : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f1 := wrap t1 in
  let f2 := wrap t2 in
  let r1 := map (fun v => tree_sum (f1 v)) (1 :: 2 :: nil) in
  let r2 := map (fun v => tree_sum (f2 v)) (3 :: 4 :: nil) in
  sum_list r1 + sum_list r2.

End MapPartialApp.

Crane Extraction "map_partial_app" MapPartialApp.
