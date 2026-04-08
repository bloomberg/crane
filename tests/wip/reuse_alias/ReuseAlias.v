From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseAlias.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** BUG PATTERN 1: Reuse optimization with function call on scrutinee.
    match t with Node l v r => Node l (some_fn t) r
    If reuse fires: moves l and r out of t, then calls some_fn(t).
    But t's fields are now null/moved, so some_fn reads garbage.

    Different from reuse_scrutinee: here the function is applied
    directly to the scrutinee, not to a separate variable. *)
Definition transform_tree (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node l (tree_sum t) r
  end.

Definition reuse_fn_bug : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  tree_sum (transform_tree t).

(** BUG PATTERN 2: Nested match where inner match uses outer scrutinee.
    Outer match on t, inner match on something else, but result
    uses both outer pattern vars AND the outer scrutinee. *)
Definition nested_match_reuse (t : tree) (flag : nat) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r =>
    match flag with
    | 0 => Node Leaf (tree_sum t) r
    | _ => Node l (tree_sum t) Leaf
    end
  end.

Definition nested_reuse_bug : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  tree_sum (nested_match_reuse t 0) + tree_sum (nested_match_reuse t 1).

(** BUG PATTERN 3: Recursive function where the recursive call uses
    the original tree while pattern vars are also used in constructor.
    map_tree modifies each node's value but the modification depends
    on the FULL subtree structure. *)
Fixpoint annotate_sum (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (annotate_sum l) (tree_sum t) (annotate_sum r)
  end.

Definition recursive_reuse_bug : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  tree_sum (annotate_sum t).

End ReuseAlias.

Crane Extraction "reuse_alias" ReuseAlias.
