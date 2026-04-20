From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseMoveShadow.

(** Define [node] FIRST so it gets variant index 0 and the reuse
    optimization picks the [node] branch via [List.hd reuse_candidates]. *)

Inductive tree : Type :=
  | node : nat -> tree -> tree -> tree
  | leaf : tree.

Arguments node _ _ _.
Arguments leaf.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | node v l r => v + tree_sum l + tree_sum r
  | leaf => 0
  end.

(** BUG: The reuse branch does not shift [move_dead_after] or
    [move_owned_vars] when pushing pattern variables.

    In [dup_left], the parameter [t] is at de Bruijn index 2, and is owned
    (escapes in the [else] branch).  After pushing 3 pattern variables
    (v at 1, l at 2, r at 3), the pattern variable [l] lands at index 2 —
    colliding with the un-shifted index for [t] in [move_dead_after] and
    [move_owned_vars].

    The non-reuse path correctly calls [with_shifted_move_tracking] which
    shifts both sets by [n_pat_vars] and clears [move_dead_after].  But the
    reuse path (lines ~4537-4602 in translation.ml) calls
    [process_match_pattern_vars] WITHOUT shifting.

    Since [l] appears TWICE in the body ([node v l l]), the assign loop
    generates [gen_expr body_env (MLrel 2)] for each.  Both checks hit
    [move_dead_after] and [move_owned_vars] at index 2 (thinking it refers to
    the dead/owned [t]), so both emit [std::move(l)]:

      _rf.d_a1 = std::move(l);   // l moved, now null
      _rf.d_a2 = std::move(l);   // l is null!  assigns null

    The returned tree has [d_a2 = nullptr].  Traversing the right subtree
    crashes with a null-pointer dereference. *)

Definition dup_left (t : tree) (b : bool) : tree :=
  if b then
    match t with
    | node v l r => node v l l
    | leaf => leaf
    end
  else t.

(** test1: [dup_left (node 10 (node 1 leaf leaf) (node 2 leaf leaf)) true]
    Expected result: [node 10 (node 1 leaf leaf) (node 1 leaf leaf)]
    tree_sum = 10 + 1 + 0 + 0 + 1 + 0 + 0 = 12
    BUG: right subtree is null -> crash in tree_sum. *)
Definition test1 : nat :=
  tree_sum (dup_left (node 10 (node 1 leaf leaf) (node 2 leaf leaf)) true).

(** test2: Deeper tree to stress memory.
    [dup_left (node 5 (node 3 (node 4 leaf leaf) leaf) leaf) true]
    Expected: [node 5 (node 3 (node 4 leaf leaf) leaf) (node 3 (node 4 leaf leaf) leaf)]
    tree_sum = 5 + (3 + 4 + 0) + (3 + 4 + 0) = 19
    BUG: right subtree is null -> crash. *)
Definition test2 : nat :=
  tree_sum (dup_left (node 5 (node 3 (node 4 leaf leaf) leaf) leaf) true).

(** test3: Non-reuse path (use_count > 1).
    This should work correctly because the normal branch uses
    [with_shifted_move_tracking] which properly shifts the indices. *)
Definition test3 : nat :=
  let t := node 7 (node 8 leaf leaf) (node 9 leaf leaf) in
  tree_sum (dup_left t true) + tree_sum t.
(** Expected: dup_left t true = node 7 (node 8 leaf leaf) (node 8 leaf leaf)
    tree_sum(dup_left) = 7+8+8 = 23.  tree_sum(t) = 7+8+9 = 24.
    Total = 47.
    Here use_count(t) == 2, so reuse does NOT fire -> correct path. *)

End ReuseMoveShadow.

Crane Extraction "reuse_move_shadow" ReuseMoveShadow.
