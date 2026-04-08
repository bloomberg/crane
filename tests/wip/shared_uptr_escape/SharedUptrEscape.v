From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module SharedUptrEscape.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** BUG HYPOTHESIS: Escape analysis might use unique_ptr for a value
    that doesn't appear to escape but later needs sharing.

    Pattern: build a tree in a let, use it in a match,
    and in different branches use it in ways that require sharing
    vs. ways that don't. The conservative analysis might pick
    unique_ptr but one branch needs shared_ptr. *)

(** identity: takes a tree and returns it unchanged.
    The tree enters as owned and leaves as owned. *)
Definition identity (t : tree) : tree := t.

(** dup: takes a tree and returns a pair with two references to it.
    This REQUIRES the tree to be shared_ptr, since both elements
    of the pair point to the same tree. *)
Definition dup (t : tree) : tree * tree := (t, t).

(** BUG: Build a tree, then conditionally either return it once
    (unique_ptr sufficient) or duplicate it (needs shared_ptr).
    If escape analysis optimistically picks unique_ptr based on
    one branch, the other branch's sharing crashes. *)
Definition conditional_share (flag : nat) : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  match flag with
  | 0 => tree_sum (identity t)
  | _ =>
    let p := dup t in
    tree_sum (fst p) + tree_sum (snd p)
  end.

(** Test: both branches should give 60.
    flag=0: identity returns same tree, sum = 60
    flag=1: dup returns (t, t), sum + sum = 60 + 60 = 120 *)

(** Pattern 2: Return tree from match, then use it twice.
    The match result is a temporary that might be unique_ptr. *)
Definition extract_subtree (t : tree) (which : nat) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r =>
    match which with
    | 0 => l
    | _ => r
    end
  end.

Definition use_extracted_twice : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let sub := extract_subtree t 0 in
  tree_sum sub + tree_sum sub.

(** Pattern 3: Build a value, pass to a function that returns it
    wrapped in a constructor, then unwrap and use twice. *)
Inductive wrapper : Type :=
| Wrap : tree -> wrapper.

Definition wrap_tree (t : tree) : wrapper := Wrap t.

Definition unwrap_and_dup : nat :=
  let t := Node Leaf 42 Leaf in
  let w := wrap_tree t in
  match w with
  | Wrap inner =>
    tree_sum inner + tree_sum inner
  end.

End SharedUptrEscape.

Crane Extraction "shared_uptr_escape" SharedUptrEscape.
