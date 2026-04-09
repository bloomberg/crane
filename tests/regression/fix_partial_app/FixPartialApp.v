From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixPartialApp.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** count_nodes: counts nodes in a tree. Will be partially applied. *)
Fixpoint count_nodes (t : tree) (base : nat) : nat :=
  match t with
  | Leaf => base
  | Node l v r => count_nodes l (count_nodes r (base + 1))
  end.

(** BUG HYPOTHESIS: Partially applying a fixpoint.
    f := count_nodes big_tree creates a closure (nat -> nat).
    The closure captures the fixpoint AND the tree.
    If either is captured by [&], it's a dangling reference.

    big_tree = Node(Node(Leaf,0,Leaf), 0, Node(Leaf,0,Leaf))
    count_nodes big_tree 0 = count_nodes left (count_nodes right (0+1))
                            = count_nodes left (count_nodes right 1)
                            = count_nodes Leaf (count_nodes Leaf (1+1))
                            = count_nodes Leaf (count_nodes Leaf 2)
                            = count_nodes Leaf 2 = 2
    Wait that's wrong. Let me recalculate:
    count_nodes (Node l v r) base = count_nodes l (count_nodes r (base + 1))

    tree = Node(Node(Leaf,0,Leaf), 0, Node(Leaf,0,Leaf))
    count_nodes tree 0
    = count_nodes (Node(Leaf,0,Leaf)) (count_nodes (Node(Leaf,0,Leaf)) (0+1))
    = count_nodes (Node(Leaf,0,Leaf)) (count_nodes (Node(Leaf,0,Leaf)) 1)

    count_nodes (Node(Leaf,0,Leaf)) 1
    = count_nodes Leaf (count_nodes Leaf (1+1))
    = count_nodes Leaf (count_nodes Leaf 2)
    = count_nodes Leaf 2
    = 2

    count_nodes (Node(Leaf,0,Leaf)) 2
    = count_nodes Leaf (count_nodes Leaf (2+1))
    = count_nodes Leaf 3
    = 3

    So count_nodes tree 0 = 3
*)
Definition fix_partial_bug : nat :=
  let t := Node (Node Leaf 0 Leaf) 0 (Node Leaf 0 Leaf) in
  let f := count_nodes t in
  f 0 + f 100.

(** Same but store partial app in pair *)
Definition fix_partial_pair : nat :=
  let t := Node (Node Leaf 0 Leaf) 0 (Node Leaf 0 Leaf) in
  let f := count_nodes t in
  let p := (f, 42) in
  fst p 0 + fst p 100.

(** More complex: partial app of tree_map, a structure-preserving function. *)
Fixpoint tree_map (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_map f l) (f v) (tree_map f r)
  end.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** Partial app of tree_map: g := tree_map (fun x => x + 1)
    Then apply g to two different trees.
    If the closure for g captures the function arg by [&], it could dangle. *)
Definition map_partial_bug : nat :=
  let g := tree_map (fun x => x + 1) in
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  tree_sum (g t1) + tree_sum (g t2).

End FixPartialApp.

Crane Extraction "fix_partial_app" FixPartialApp.
