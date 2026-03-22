(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

(** Consolidated UNIQUE tree algorithms - domain-specific tree operations. *)
Module LoopifyTrees.

Inductive tree (A : Type) : Type :=
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A} l x r.

(* ========== UNIQUE TREE ALGORITHMS ========== *)

Fixpoint tree_sum (t : tree nat) : nat :=
  match t with
  | Leaf => O
  | Node l x r => Nat.add x (Nat.add (tree_sum l) (tree_sum r))
  end.

Fixpoint tree_height {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf => O
  | Node l _ r =>
    let lh := tree_height l in
    let rh := tree_height r in
    S (if Nat.leb lh rh then rh else lh)
  end.

Fixpoint tree_size {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf => O
  | Node l _ r => S (Nat.add (tree_size l) (tree_size r))
  end.

Fixpoint mirror {A : Type} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (mirror r) x (mirror l)
  end.

(** [same_shape] tests structural equality. *)
Fixpoint same_shape {A B : Type} (t1 : tree A) (t2 : tree B) : bool :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node l1 _ r1, Node l2 _ r2 =>
    if same_shape l1 l2 then same_shape r1 r2 else false
  | _, _ => false
  end.

(** [leftmost/rightmost] finds edge values. *)
Fixpoint leftmost {A : Type} (default : A) (t : tree A) : A :=
  match t with
  | Leaf => default
  | Node Leaf x _ => x
  | Node l _ _ => leftmost default l
  end.

Fixpoint rightmost {A : Type} (default : A) (t : tree A) : A :=
  match t with
  | Leaf => default
  | Node _ x Leaf => x
  | Node _ _ r => rightmost default r
  end.

(** [count_leaves] counts leaf nodes. *)
Fixpoint count_leaves {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf => 1
  | Node l _ r => Nat.add (count_leaves l) (count_leaves r)
  end.

(** [leaf_sum] sums only leaf values. *)
Fixpoint leaf_sum (t : tree nat) : nat :=
  match t with
  | Leaf => O
  | Node Leaf x Leaf => x
  | Node l _ r => Nat.add (leaf_sum l) (leaf_sum r)
  end.

(** [insert_bst] BST insertion. *)
Fixpoint insert_bst (x : nat) (t : tree nat) : tree nat :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l y r =>
    if Nat.leb x y
    then Node (insert_bst x l) y r
    else Node l y (insert_bst x r)
  end.

(** [tree_to_list] inorder traversal. *)
Fixpoint tree_to_list {A : Type} (t : tree A) : list A :=
  match t with
  | Leaf => nil
  | Node l x r => app (tree_to_list l) (cons x (tree_to_list r))
  end.

(** [count_paths t n] counts root-to-leaf paths that sum to n. *)
Fixpoint count_paths (t : tree nat) (n : nat) : nat :=
  match t with
  | Leaf => if Nat.eqb n O then 1 else O
  | Node l x r =>
    if Nat.leb n x
    then
      if Nat.eqb n x
      then Nat.add (count_paths l O) (count_paths r O)
      else O
    else
      let remaining := Nat.sub n x in
      Nat.add (count_paths l remaining) (count_paths r remaining)
  end.

(** [sum_of_max_branches] sums maximum values along each path. *)
Fixpoint sum_of_max_branches (t : tree nat) : nat :=
  match t with
  | Leaf => O
  | Node l x r =>
    let lsum := sum_of_max_branches l in
    let rsum := sum_of_max_branches r in
    Nat.add x (if Nat.leb lsum rsum then rsum else lsum)
  end.

(* ========== MULTI-WAY TREES ========== *)

Inductive ternary : Type :=
| TLeaf : ternary
| TNode : ternary -> ternary -> ternary -> nat -> ternary.

Fixpoint ternary_sum (t : ternary) : nat :=
  match t with
  | TLeaf => O
  | TNode t1 t2 t3 x =>
    Nat.add x (Nat.add (ternary_sum t1)
                (Nat.add (ternary_sum t2) (ternary_sum t3)))
  end.

Fixpoint ternary_depth (t : ternary) : nat :=
  match t with
  | TLeaf => O
  | TNode t1 t2 t3 _ =>
    let d1 := ternary_depth t1 in
    let d2 := ternary_depth t2 in
    let d3 := ternary_depth t3 in
    S (if Nat.leb (if Nat.leb d1 d2 then d2 else d1) d3
       then d3
       else (if Nat.leb d1 d2 then d2 else d1))
  end.

(* ========== ROSE TREES ========== *)

(** Rose tree: a tree with variable number of children. *)
Inductive rose : Type :=
| RNode : nat -> list rose -> rose.

(** Helper: sum all values in a list of rose trees (processes both tree and
    list levels in one recursive function to enable full loopification). *)
Fixpoint sum_rose_list_fuel (fuel : nat) (cs : list rose) : nat :=
  match fuel with
  | O => O
  | S f =>
    match cs with
    | nil => O
    | cons c rest =>
      match c with
      | RNode x children =>
        Nat.add x (Nat.add (sum_rose_list_fuel f children)
                           (sum_rose_list_fuel f rest))
      end
    end
  end.

(** [rose_sum t] sums all values in a rose tree. *)
Definition rose_sum (t : rose) : nat :=
  match t with
  | RNode x children => Nat.add x (sum_rose_list_fuel 1000 children)
  end.

(** Helper: map function over all values in a list of rose trees. *)
Fixpoint map_rose_list_fuel (fuel : nat) (f : nat -> nat)
                            (cs : list rose) : list rose :=
  match fuel with
  | O => nil
  | S g =>
    match cs with
    | nil => nil
    | cons c rest =>
      match c with
      | RNode x children =>
        cons (RNode (f x) (map_rose_list_fuel g f children))
             (map_rose_list_fuel g f rest)
      end
    end
  end.

(** [rose_map f t] applies f to all values in a rose tree. *)
Definition rose_map (f : nat -> nat) (t : rose) : rose :=
  match t with
  | RNode x children => RNode (f x) (map_rose_list_fuel 1000 f children)
  end.

(** Helper: flatten a list of rose trees to a flat list of nats. *)
Fixpoint flatten_rose_list_fuel (fuel : nat) (cs : list rose) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match cs with
    | nil => nil
    | cons c rest =>
      match c with
      | RNode x children =>
        cons x (app (flatten_rose_list_fuel f children)
                             (flatten_rose_list_fuel f rest))
      end
    end
  end.

(** [rose_flatten t] flattens a rose tree to a list (pre-order). *)
Definition rose_flatten (t : rose) : list nat :=
  match t with
  | RNode x children => cons x (flatten_rose_list_fuel 1000 children)
  end.

(** Helper: compute maximum depth among a list of rose trees. *)
Fixpoint depth_rose_list_fuel (fuel : nat) (cs : list rose) : nat :=
  match fuel with
  | O => O
  | S f =>
    match cs with
    | nil => O
    | cons c rest =>
      match c with
      | RNode _ children =>
        let d := S (depth_rose_list_fuel f children) in
        let rest_max := depth_rose_list_fuel f rest in
        if Nat.leb d rest_max then rest_max else d
      end
    end
  end.

(** [rose_depth t] computes the depth of a rose tree. *)
Definition rose_depth (t : rose) : nat :=
  match t with
  | RNode _ children => S (depth_rose_list_fuel 1000 children)
  end.

(* ========== TREE OPERATIONS ========== *)

(** [tree_max t1 t2] element-wise maximum of two trees. *)
Fixpoint tree_max (t1 t2 : tree nat) : tree nat :=
  match t1, t2 with
  | Leaf, Leaf => Leaf
  | Node l1 x r1, Node l2 y r2 =>
    let max_val := if Nat.leb x y then y else x in
    Node (tree_max l1 l2) max_val (tree_max r1 r2)
  | Node _ _ _, Leaf => t1
  | Leaf, Node _ _ _ => t2
  end.

(** Helper: extract values from trees. *)
Fixpoint extract_tree_values (ts : list (tree nat)) : list nat :=
  match ts with
  | nil => nil
  | cons t rest =>
    match t with
    | Leaf => extract_tree_values rest
    | Node _ x _ => cons x (extract_tree_values rest)
    end
  end.

(** Helper: extract children from trees. *)
Fixpoint extract_tree_children (ts : list (tree nat)) : list (tree nat) :=
  match ts with
  | nil => nil
  | cons t rest =>
    match t with
    | Leaf => extract_tree_children rest
    | Node l _ r => cons l (cons r (extract_tree_children rest))
    end
  end.

(** [tree_levels t] returns list of lists, one per level (breadth-first). *)
Fixpoint tree_levels_fuel (fuel : nat) (trees : list (tree nat)) : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    let values := extract_tree_values trees in
    match values with
    | nil => nil
    | _ =>
      let children := extract_tree_children trees in
      cons values (tree_levels_fuel f children)
    end
  end.

Definition tree_levels (t : tree nat) : list (list nat) :=
  tree_levels_fuel 100 (cons t nil).

(* ========== TREE COMPARISONS & AGGREGATIONS ========== *)

(** [count_nodes t] returns tuple (node_count, sum_of_values). *)
Fixpoint count_nodes (t : tree nat) : nat * nat :=
  match t with
  | Leaf => (O, O)
  | Node l x r =>
    let '(lc, ls) := count_nodes l in
    let '(rc, rs) := count_nodes r in
    (S (Nat.add lc rc), Nat.add x (Nat.add ls rs))
  end.

(** [mirror_equal t1 t2] checks if t1 and t2 are mirror images. *)
Fixpoint mirror_equal {A : Type} (t1 t2 : tree A) : bool :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node l1 x r1, Node l2 y r2 =>
    andb (andb (mirror_equal l1 r2) (mirror_equal r1 l2)) true
  | _, _ => false
  end.

(** [tree_map f t] applies f to all values in tree. *)
Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (tree_map f l) (f x) (tree_map f r)
  end.

(** Helper: append two lists of lists. *)
Fixpoint append_list_lists (l1 l2 : list (list nat)) : list (list nat) :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (append_list_lists xs l2)
  end.

(** Helper: prepend value to all lists in a list of lists. *)
Fixpoint map_cons_to_all (x : nat) (lsts : list (list nat)) : list (list nat) :=
  match lsts with
  | nil => nil
  | cons p ps => cons (cons x p) (map_cons_to_all x ps)
  end.

(** [paths t] returns all root-to-leaf paths in tree. *)
Fixpoint paths (t : tree nat) : list (list nat) :=
  match t with
  | Leaf => cons nil nil
  | Node l x r =>
    append_list_lists (map_cons_to_all x (paths l)) (map_cons_to_all x (paths r))
  end.

(** [collect_sorted t] collects and sorts all tree values. *)
Fixpoint collect_unsorted (t : tree nat) : list nat :=
  match t with
  | Leaf => nil
  | Node l x r => app (collect_unsorted l) (cons x (collect_unsorted r))
  end.

(** Simple insertion sort for collect_sorted. *)
Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons x nil
  | cons y ys =>
    if Nat.leb x y
    then cons x (cons y ys)
    else cons y (insert_sorted x ys)
  end.

Fixpoint sort_list (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => insert_sorted x (sort_list xs)
  end.

Definition collect_sorted (t : tree nat) : list nat :=
  sort_list (collect_unsorted t).

(** [or_search p t] searches tree for element satisfying predicate. *)
Fixpoint or_search (p : nat -> bool) (t : tree nat) : bool :=
  match t with
  | Leaf => false
  | Node l x r =>
    if p x then true
    else orb (or_search p l) (or_search p r)
  end.

(* ========== QUADTREE (4-way trees) ========== *)

Inductive quadtree : Type :=
| QLeaf : nat -> quadtree
| Quad : quadtree -> quadtree -> quadtree -> quadtree -> quadtree.

(** [quad_sum t] sums all values in a quadtree. *)
Fixpoint quad_sum (t : quadtree) : nat :=
  match t with
  | QLeaf x => x
  | Quad nw ne sw se =>
    Nat.add (quad_sum nw)
      (Nat.add (quad_sum ne)
        (Nat.add (quad_sum sw) (quad_sum se)))
  end.

(** Helper: max of 4 values using nested max. *)
Fixpoint max4_impl (a b c d : nat) : nat :=
  if Nat.leb (if Nat.leb a b then b else a)
             (if Nat.leb c d then d else c)
  then (if Nat.leb c d then d else c)
  else (if Nat.leb a b then b else a).

(** [quad_depth t] computes depth of quadtree. *)
Fixpoint quad_depth (t : quadtree) : nat :=
  match t with
  | QLeaf _ => O
  | Quad nw ne sw se =>
    S (max4_impl (quad_depth nw) (quad_depth ne)
                 (quad_depth sw) (quad_depth se))
  end.

(* ========== SIMPLE BINARY TREE (no values at nodes) ========== *)

(** Simple binary tree with values only at leaves. *)
Inductive simple_tree : Type :=
| SLeaf : nat -> simple_tree
| SNode : simple_tree -> simple_tree -> simple_tree.

(** [simple_tree_sum t] sums all leaf values. *)
Fixpoint simple_tree_sum (t : simple_tree) : nat :=
  match t with
  | SLeaf x => x
  | SNode l r => Nat.add (simple_tree_sum l) (simple_tree_sum r)
  end.

(** [count_paths_simple t n] counts paths with sum n (simpler variant). *)
Fixpoint count_paths_simple (t : simple_tree) (n : nat) : nat :=
  match t with
  | SLeaf x => if Nat.eqb x n then 1 else O
  | SNode l r =>
    if Nat.leb n O
    then O
    else Nat.add (count_paths_simple l (Nat.sub n 1))
                 (count_paths_simple r (Nat.sub n 1))
  end.

(* ========== ADDITIONAL TREE OPERATIONS ========== *)

(** Helper: compute minimum of three values. *)
Fixpoint min3 (a b c : nat) : nat :=
  if Nat.leb a b then (if Nat.leb a c then a else c)
  else (if Nat.leb b c then b else c).

(** Helper: compute maximum of three values. *)
Fixpoint max3 (a b c : nat) : nat :=
  if Nat.leb b a then (if Nat.leb c a then a else c)
  else (if Nat.leb c b then b else c).

(** [tree_min_max t] finds minimum and maximum values in tree. *)
Fixpoint tree_min_max (t : tree nat) : nat * nat :=
  match t with
  | Leaf => (O, O)
  | Node l x r =>
    let '(lmin, lmax) := tree_min_max l in
    let '(rmin, rmax) := tree_min_max r in
    (min3 (if Nat.eqb lmin O then x else lmin) (if Nat.eqb rmin O then x else rmin) x,
     max3 lmax rmax x)
  end.

(** [all_paths_sum t] sums all root-to-leaf path sums. *)
Fixpoint all_paths_sum (t : tree nat) : nat :=
  let fix sum_with_acc acc tree :=
    match tree with
    | Leaf => acc
    | Node l x r =>
      let new_acc := Nat.add acc x in
      Nat.add (sum_with_acc new_acc l) (sum_with_acc new_acc r)
    end
  in sum_with_acc O t.

(** [tree_contains x t] checks if value exists in tree. *)
Fixpoint tree_contains (x : nat) (t : tree nat) : bool :=
  match t with
  | Leaf => false
  | Node l v r =>
    orb (Nat.eqb x v)
        (orb (tree_contains x l) (tree_contains x r))
  end.

End LoopifyTrees.

Set Crane Loopify.
Crane Extraction "loopify_trees" LoopifyTrees.
