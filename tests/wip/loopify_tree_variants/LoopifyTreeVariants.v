From Stdlib Require Import Nat.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyTreeVariants.

(* Various tree structures and operations *)

(* Ternary tree - three children *)
Inductive ternary : Type :=
  | TLeaf : ternary
  | TNode : ternary -> nat -> ternary -> ternary -> ternary.

Fixpoint ternary_sum (t : ternary) : nat :=
  match t with
  | TLeaf => 0
  | TNode l x m r => ternary_sum l + x + ternary_sum m + ternary_sum r
  end.

Fixpoint ternary_count (t : ternary) : nat :=
  match t with
  | TLeaf => 0
  | TNode l _ m r => 1 + ternary_count l + ternary_count m + ternary_count r
  end.

(* Quad tree - four children *)
Inductive quadtree : Type :=
  | QLeaf : nat -> quadtree
  | Quad : quadtree -> quadtree -> quadtree -> quadtree -> quadtree.

Fixpoint quad_sum (t : quadtree) : nat :=
  match t with
  | QLeaf x => x
  | Quad nw ne sw se => quad_sum nw + quad_sum ne + quad_sum sw + quad_sum se
  end.

(* Binary tree with leaves holding values *)
Inductive leaf_tree : Type :=
  | LLeaf : nat -> leaf_tree
  | LNode : leaf_tree -> leaf_tree -> leaf_tree.

Fixpoint leaf_tree_sum (t : leaf_tree) : nat :=
  match t with
  | LLeaf x => x
  | LNode l r => leaf_tree_sum l + leaf_tree_sum r
  end.

Fixpoint leaf_tree_max (t : leaf_tree) : nat :=
  match t with
  | LLeaf x => x
  | LNode l r =>
    let lmax := leaf_tree_max l in
    let rmax := leaf_tree_max r in
    if lmax <? rmax then rmax else lmax
  end.

End LoopifyTreeVariants.

Set Crane Loopify.
Crane Extraction "loopify_tree_variants" LoopifyTreeVariants.
