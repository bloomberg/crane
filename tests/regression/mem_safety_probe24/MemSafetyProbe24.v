From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe24.

(** Probe 24: Complex value-type interactions.

    Attack vectors:
    1. Use-after-move in pair/constructor arguments: if Crane
       generates std::move(t) alongside t.field in the same expression
    2. Rose-tree with list children: complex ownership when
       flattening nested value types
    3. Multi-use of owned variable in constructor calls: t used in
       both constructor position AND field-access position
    4. Value-type stored in option/pair then accessed through
       projection — tests whether projections access moved-from data *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

Fixpoint app {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (app xs l2)
  end.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => 1 + length xs
  end.

(** TEST 1: Variable used as BOTH whole value AND for field access
    in the same constructor. In C++, tree::node(t, tree_sum(t), Leaf)
    where t must be cloned and tree_sum accesses t's children. *)
Definition self_annotate (t : tree) : tree :=
  Node t (tree_sum t) Leaf.

Definition test_self_annotate : nat :=
  tree_sum (self_annotate (Node Leaf 5 Leaf)).
(** Node (Node Leaf 5 Leaf) 5 Leaf => sum = 5 + 5 = 10 *)

(** TEST 2: Pair where BOTH elements use t, one as value
    and one through a function. *)
Definition pair_self (t : tree) : tree * nat :=
  (t, tree_sum t).

Definition test_pair_self : nat :=
  let p := pair_self (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  tree_sum (fst p) + snd p.
(** sum=21 each; total=42 *)

(** TEST 3: Triple use of t in one expression. *)
Definition triple_use (t : tree) : tree * tree * nat :=
  (t, t, tree_sum t).

Definition test_triple_use : nat :=
  let p := triple_use (Node Leaf 5 Leaf) in
  tree_sum (fst (fst p)) + tree_sum (snd (fst p)) + snd p.
(** 5+5+5=15 *)

(** TEST 4: Recursive function where result uses BOTH t (for return)
    and t's children (through recursive calls) — not loopified because
    return type is pair. Tests use-after-move in make_pair. *)
Fixpoint tag_tree (t : tree) : tree * nat :=
  match t with
  | Leaf => (Leaf, 0)
  | Node l v r =>
    let pl := tag_tree l in
    let pr := tag_tree r in
    (t, v + snd pl + snd pr)
  end.

Definition test_tag_tree : nat :=
  let p := tag_tree (Node (Node Leaf 2 Leaf) 5 (Node Leaf 8 Leaf)) in
  tree_sum (fst p) + snd p.
(** fst = original tree, sum=15; snd=2+5+8=15; total=30 *)

(** TEST 5: Nested value type — list of trees stored in a tree-like
    structure. Tests clone correctness and ownership for nested types. *)
Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (map_tree f l) (f v) (map_tree f r)
  end.

Fixpoint tree_to_list (t : tree) : mylist nat :=
  match t with
  | Leaf => mynil
  | Node l v r => app (tree_to_list l) (mycons v (tree_to_list r))
  end.

Definition test_nested_ops : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  let doubled := map_tree (fun n => n * 2) t in
  let flat := tree_to_list doubled in
  sum_list flat + tree_sum t.
(** doubled = Node (NL6L) 14 (NL22L), flat = [6,14,22], sum=42
    tree_sum t = 21; total = 63 *)

(** TEST 6: Store a tree AND its sum in a pair, then transform
    both. Tests that clone is independent of original. *)
Definition clone_and_transform (t : tree) : nat :=
  let p := (t, tree_sum t) in
  let t2 := fst p in
  let s := snd p in
  let t3 := map_tree (fun n => n + s) t2 in
  tree_sum t3.

Definition test_clone_and_transform : nat :=
  clone_and_transform (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)).
(** s = 6; map adds 6 to each: Node (NL7L) 8 (NL9L); sum = 24 *)

(** TEST 7: Build a tree from a list, using accumulated state.
    Tests interaction between list recursion and tree construction. *)
Fixpoint list_to_tree (l : mylist nat) (acc : tree) : tree :=
  match l with
  | mynil => acc
  | mycons x xs => list_to_tree xs (Node acc x Leaf)
  end.

Definition test_list_to_tree : nat :=
  tree_sum (list_to_tree (mycons 1 (mycons 2 (mycons 3 mynil))) Leaf).
(** Leaf -> Node Leaf 1 Leaf -> Node (Node Leaf 1 Leaf) 2 Leaf
    -> Node (Node (Node Leaf 1 Leaf) 2 Leaf) 3 Leaf
    sum = 1 + 2 + 3 = 6 *)

(** TEST 8: Zip two trees, producing a list of pairs.
    Both trees are destructured simultaneously. *)
Fixpoint zip_trees (t1 t2 : tree) : mylist (nat * nat) :=
  match t1, t2 with
  | Node l1 v1 r1, Node l2 v2 r2 =>
    app (zip_trees l1 l2) (mycons (v1, v2) (zip_trees r1 r2))
  | _, _ => mynil
  end.

Definition test_zip_trees : nat :=
  sum_list (
    let pairs := zip_trees
      (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
      (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) in
    let add_pair := fun p : nat * nat => fst p + snd p in
    match pairs with
    | mynil => mycons 0 mynil
    | mycons p1 rest =>
      match rest with
      | mynil => mycons (add_pair p1) mynil
      | mycons p2 rest2 =>
        match rest2 with
        | mynil => mycons (add_pair p1) (mycons (add_pair p2) mynil)
        | mycons p3 _ =>
          mycons (add_pair p1) (mycons (add_pair p2) (mycons (add_pair p3) mynil))
        end
      end
    end).
(** pairs = [(1,10), (2,20), (3,30)]
    sums = [11, 22, 33] = 66 *)

End MemSafetyProbe24.

Crane Extraction "mem_safety_probe24" MemSafetyProbe24.
