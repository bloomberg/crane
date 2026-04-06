From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MoveSafety.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Definition sum_values (t : tree) (x : nat) : nat :=
  match t with
  | Leaf => x
  | Node l v r =>
    match l with
    | Leaf => v + x
    | Node _ lv _ =>
      match r with
      | Leaf => lv + x
      | Node _ rv _ => lv + rv + v + x
      end
    end
  end.

(** A function that stores its tree argument inside a constructor.
    This causes the parameter to be passed by value (it "escapes"). *)
Definition wrap_tree (t : tree) : tree :=
  Node t 0 Leaf.

(** A wrapper for closures. *)
Inductive fn_box : Type :=
| Box : (nat -> nat) -> fn_box.

Definition apply_box (b : fn_box) (x : nat) : nat :=
  match b with
  | Box f => f x
  end.

(** TEST 1: Partial application + function taking by value.
    The [&] lambda from partial application captures t by reference.
    Then wrap_tree takes t by value, so std::move(t) is generated.
    The lambda then holds a dangling reference. *)
Definition bug_partial_then_wrap : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  let _ := wrap_tree t in
  f 99.

(** TEST 2: Store partial application in a Box.
    If the eta-expanded lambda uses [&] capture,
    the Box will hold a dangling reference after the
    function returns. *)
Definition make_box (t : tree) : fn_box :=
  Box (sum_values t).

Definition bug_box_escape : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b := make_box t in
  apply_box b 99.

(** TEST 3: Two partial applications of same variable.
    Second one should not move t. *)
Definition bug_double_partial : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  let g := sum_values t in
  f 1 + g 2.

(** TEST 4: Partial application followed by identity function
    that takes by value (returns its argument). *)
Definition tree_id (t : tree) : tree := t.

Definition bug_partial_then_id : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  let t2 := tree_id t in
  match t2 with
  | Leaf => f 0
  | Node _ v _ => f v
  end.

End MoveSafety.

Crane Extraction "move_safety" MoveSafety.
