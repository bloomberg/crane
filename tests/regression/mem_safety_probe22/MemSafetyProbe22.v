From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe22.

(** Probe 22: Owned-parameter loopification with continuation frames.

    Attack vector: When a recursive function takes a value-type tree
    by value (owned, not pointer-safe), the loopifier uses v_mut()
    for the match and optimize_frame_push_args can std::move children
    in _Enter frames. If continuation frames (_After) store raw pointers
    to OTHER children, those pointers dangle when the local tree goes
    out of scope at the end of the handler block.

    Key: the recursive call must take a DIFFERENT tree (not the original
    parameter) so the parameter is not pointer-safe. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 1: Two recursive calls on CHILDREN, but the
    function takes tree by value because it also returns/stores it. *)
Fixpoint sum_and_rebuild (t : tree) : tree * nat :=
  match t with
  | Leaf => (Leaf, 0)
  | Node l v r =>
    let pl := sum_and_rebuild l in
    let pr := sum_and_rebuild r in
    (Node (fst pl) v (fst pr), snd pl + v + snd pr)
  end.

Definition test_sum_and_rebuild : nat :=
  snd (sum_and_rebuild (Node (Node Leaf 1 Leaf) 5 (Node Leaf 2 Leaf))).
(** sum = 1 + 5 + 2 = 8 *)

(** TEST 2: Function that recurses on children AND stores result
    in constructor, forcing the tree to be owned. *)
Fixpoint double_tree (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (double_tree l) (v * 2) (double_tree r)
  end.

Definition test_double_tree : nat :=
  tree_sum (double_tree (Node (Node Leaf 3 Leaf) 5 (Node Leaf 7 Leaf))).
(** double: Node (Node Leaf 6 Leaf) 10 (Node Leaf 14 Leaf)
    sum = 6 + 10 + 14 = 30 *)

(** TEST 3: Two recursive calls with child + value in result. *)
Fixpoint weighted_sum (t : tree) (w : nat) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    weighted_sum l (w + 1) + v * w + weighted_sum r (w + 1)
  end.

Definition test_weighted_sum : nat :=
  weighted_sum (Node (Node Leaf 3 Leaf) 5 (Node Leaf 7 Leaf)) 1.
(** weighted_sum (Node(NL3L) 5 (NL7L)) 1
    = weighted_sum (NL3L) 2 + 5*1 + weighted_sum (NL7L) 2
    = (weighted_sum Leaf 3 + 3*2 + weighted_sum Leaf 3) + 5 + (weighted_sum Leaf 3 + 7*2 + weighted_sum Leaf 3)
    = (0 + 6 + 0) + 5 + (0 + 14 + 0)
    = 6 + 5 + 14 = 25 *)

(** TEST 4: Function with constructed-tree recursive calls. *)
Fixpoint split_sum (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' =>
    match t with
    | Leaf => 0
    | Node l v r =>
      split_sum (Node l (v + 1) Leaf) n' + split_sum (Node Leaf (v + 1) r) n'
    end
  end.

Definition test_split_sum : nat :=
  split_sum (Node Leaf 10 Leaf) 1.
(** split_sum (Node Leaf 10 Leaf) 1
    = split_sum (Node Leaf 11 Leaf) 0 + split_sum (Node Leaf 11 Leaf) 0
    = tree_sum (NL11L) + tree_sum (NL11L)
    = 11 + 11 = 22 *)

(** TEST 5: Tree map with two recursive calls on children. *)
Fixpoint tree_map (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_map f l) (f v) (tree_map f r)
  end.

Definition test_tree_map : nat :=
  tree_sum (tree_map (fun n => n + 10) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))).
(** Mapped: Node (Node Leaf 11 Leaf) 12 (Node Leaf 13 Leaf)
    sum = 11 + 12 + 13 = 36 *)

(** TEST 6: Mirror tree (swap children). Two recursive calls. *)
Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (mirror r) v (mirror l)
  end.

Definition test_mirror : nat :=
  tree_sum (mirror (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))).
(** Mirror: Node (Node Leaf 3 Leaf) 2 (Node Leaf 1 Leaf)
    sum = 3 + 2 + 1 = 6 *)

(** TEST 7: Insert into BST (non-pointer-safe because constructed tree
    in recursive call). *)
Fixpoint insert (t : tree) (x : nat) : tree :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l v r =>
    if Nat.leb x v
    then Node (insert l x) v r
    else Node l v (insert r x)
  end.

Fixpoint insert_all (t : tree) (xs : list nat) : tree :=
  match xs with
  | nil => t
  | cons x rest => insert_all (insert t x) rest
  end.

Definition test_insert : nat :=
  tree_sum (insert_all Leaf (cons 5 (cons 3 (cons 7 (cons 1 (cons 9 nil)))))).
(** Inserted: 5, 3, 7, 1, 9. Sum = 5+3+7+1+9 = 25 *)

(** TEST 8: Deep tree transformation with two recursive calls. *)
Fixpoint label_depth (t : tree) (d : nat) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (label_depth l (d + 1)) (v + d) (label_depth r (d + 1))
  end.

Definition test_label_depth : nat :=
  tree_sum (label_depth (Node (Node Leaf 0 Leaf) 0 (Node Leaf 0 Leaf)) 1).
(** label_depth at depth 1:
    Node (label_depth (NL0L) 2) (0+1) (label_depth (NL0L) 2)
    = Node (Node Leaf (0+2) Leaf) 1 (Node Leaf (0+2) Leaf)
    = Node (Node Leaf 2 Leaf) 1 (Node Leaf 2 Leaf)
    sum = 2 + 1 + 2 = 5 *)

End MemSafetyProbe22.

Crane Extraction "mem_safety_probe22" MemSafetyProbe22.
