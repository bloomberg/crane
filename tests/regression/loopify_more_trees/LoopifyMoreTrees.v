From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyMoreTrees.

(* Additional tree operations *)

Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

(* Mirror/flip a tree *)
Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (mirror r) x (mirror l)
  end.

(* Check if two trees have the same shape (ignore values) *)
Fixpoint same_shape (t1 t2 : tree) : bool :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node l1 _ r1, Node l2 _ r2 => same_shape l1 l2 && same_shape r1 r2
  | _, _ => false
  end.

(* Convert tree to list (in-order) *)
Fixpoint tree_to_list (t : tree) : list nat :=
  match t with
  | Leaf => []
  | Node l x r => tree_to_list l ++ [x] ++ tree_to_list r
  end.

(* Check if a tree equals its mirror *)
Fixpoint mirror_equal (t : tree) : bool :=
  same_shape t (mirror t).

(* Count internal nodes (non-leaves) *)
Fixpoint count_nodes (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 1 + count_nodes l + count_nodes r
  end.

(* Tree with max values at each position *)
Fixpoint tree_max (t1 t2 : tree) : tree :=
  match t1, t2 with
  | Leaf, t => t
  | t, Leaf => t
  | Node l1 x1 r1, Node l2 x2 r2 =>
    Node (tree_max l1 l2) (max x1 x2) (tree_max r1 r2)
  end.

(* Sum of all values along maximum branch *)
Fixpoint sum_of_max_branches (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l x r =>
    x + max (sum_of_max_branches l) (sum_of_max_branches r)
  end.

(* Insert into BST *)
Fixpoint insert_bst (x : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l y r =>
    if x <=? y then Node (insert_bst x l) y r
    else Node l y (insert_bst x r)
  end.

(* Build BST from list *)
Fixpoint build_bst (l : list nat) : tree :=
  match l with
  | [] => Leaf
  | x :: xs => insert_bst x (build_bst xs)
  end.

(* Collect tree by levels (BFS) *)
Fixpoint append_lists (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | h :: t => h :: append_lists t l2
  end.

Fixpoint flatten (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | l :: rest => append_lists l (flatten rest)
  end.

Fixpoint map_tree_to_list (lt : list tree) : list (list nat) :=
  match lt with
  | [] => []
  | t :: rest => tree_to_list t :: map_tree_to_list rest
  end.

Fixpoint tree_children (t : tree) : list tree :=
  match t with
  | Leaf => []
  | Node l _ r => [l; r]
  end.

Fixpoint append_trees (l1 l2 : list tree) : list tree :=
  match l1 with
  | [] => l2
  | h :: t => h :: append_trees t l2
  end.

Fixpoint concat_map_children (lt : list tree) : list tree :=
  match lt with
  | [] => []
  | t :: rest => append_trees (tree_children t) (concat_map_children rest)
  end.

Fixpoint tree_levels_fuel (fuel : nat) (level : list tree) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match level with
    | [] => []
    | _ =>
      let values := flatten (map_tree_to_list level) in
      let next := concat_map_children level in
      values :: tree_levels_fuel fuel' next
    end
  end.

Definition tree_levels (t : tree) : list (list nat) :=
  tree_levels_fuel 100 [t].

End LoopifyMoreTrees.

Set Crane Loopify.
Crane Extraction "loopify_more_trees" LoopifyMoreTrees.
