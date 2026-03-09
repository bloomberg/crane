(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined test: nested inductives with both custom and stdlib lists. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module NestedInd.

(* ===================================================================== *)
(* Part 1: Nested inductives with CUSTOM list (from nested_ind_custom_list) *)
(* ===================================================================== *)

(* Simple custom list for nesting *)
Inductive custom_list (A : Type) : Type :=
| cnil : custom_list A
| ccons : A -> custom_list A -> custom_list A.

Arguments cnil {A}.
Arguments ccons {A} _ _.

(* Rose tree - tree with list of children (nested inductive) *)
Inductive rose (A : Type) : Type :=
| Node : A -> custom_list (rose A) -> rose A.

Arguments Node {A} _ _.

(* Get the root value *)
Definition root {A : Type} (t : rose A) : A :=
  match t with
  | Node x _ => x
  end.

(* Get custom list length *)
Fixpoint custom_list_length {A : Type} (l : custom_list A) : nat :=
  match l with
  | cnil => 0
  | ccons _ rest => Nat.add 1 (custom_list_length rest)
  end.

(* Get children count (not recursive into children) *)
Definition children_count {A : Type} (t : rose A) : nat :=
  match t with
  | Node _ children => custom_list_length children
  end.

(* Test rose tree *)
Definition leaf (n : nat) : rose nat := Node n cnil.
Definition small_tree : rose nat :=
  Node 1 (ccons (leaf 2) (ccons (leaf 3) cnil)).

Definition bigger_tree : rose nat :=
  Node 1 (ccons small_tree (ccons (leaf 4) cnil)).

(* Test values for custom list rose tree *)
Definition test_root_leaf := root (leaf 5).
Definition test_root_small := root small_tree.
Definition test_children_leaf := children_count (leaf 5).
Definition test_children_small := children_count small_tree.
Definition test_children_bigger := children_count bigger_tree.

(* ===================================================================== *)
(* Part 2: Nested inductives with STDLIB list (from nested_ind_stdlib_list) *)
(* ===================================================================== *)

(* === Nested inductive: expr uses list expr in constructors === *)

Inductive expr : Type :=
| Lit : nat -> expr
| Add : list expr -> expr
| Mul : list expr -> expr.

(* === Recursive functions via nested fix === *)

Fixpoint eval (e : expr) : nat :=
  match e with
  | Lit n => n
  | Add es =>
      (fix sum_all (l : list expr) : nat :=
         match l with
         | nil => 0
         | cons e' rest => eval e' + sum_all rest
         end) es
  | Mul es =>
      (fix prod_all (l : list expr) : nat :=
         match l with
         | nil => 1
         | cons e' rest => eval e' * prod_all rest
         end) es
  end.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | Lit _ => 1
  | Add es =>
      S ((fix aux (l : list expr) : nat :=
            match l with
            | nil => 0
            | cons e' rest => expr_size e' + aux rest
            end) es)
  | Mul es =>
      S ((fix aux (l : list expr) : nat :=
            match l with
            | nil => 0
            | cons e' rest => expr_size e' + aux rest
            end) es)
  end.

Fixpoint expr_depth (e : expr) : nat :=
  match e with
  | Lit _ => 0
  | Add es =>
      S ((fix aux (l : list expr) : nat :=
            match l with
            | nil => 0
            | cons e' rest => max (expr_depth e') (aux rest)
            end) es)
  | Mul es =>
      S ((fix aux (l : list expr) : nat :=
            match l with
            | nil => 0
            | cons e' rest => max (expr_depth e') (aux rest)
            end) es)
  end.

Fixpoint literals (e : expr) : list nat :=
  match e with
  | Lit n => [n]
  | Add es =>
      (fix aux (l : list expr) : list nat :=
         match l with
         | nil => nil
         | cons e' rest => literals e' ++ aux rest
         end) es
  | Mul es =>
      (fix aux (l : list expr) : list nat :=
         match l with
         | nil => nil
         | cons e' rest => literals e' ++ aux rest
         end) es
  end.

Fixpoint lit_map (f : nat -> nat) (e : expr) : expr :=
  match e with
  | Lit n => Lit (f n)
  | Add es =>
      Add ((fix aux (l : list expr) : list expr :=
              match l with
              | nil => nil
              | cons e' rest => cons (lit_map f e') (aux rest)
              end) es)
  | Mul es =>
      Mul ((fix aux (l : list expr) : list expr :=
              match l with
              | nil => nil
              | cons e' rest => cons (lit_map f e') (aux rest)
              end) es)
  end.

(* === Test values for stdlib list expr === *)

(* 1 + 2 + 3 = 6 *)
Definition test_add : expr := Add [Lit 1; Lit 2; Lit 3].

(* 2 * 3 * 4 = 24 *)
Definition test_mul : expr := Mul [Lit 2; Lit 3; Lit 4].

(* (1 + 2) * (3 + 4) = 3 * 7 = 21 *)
Definition test_nested : expr :=
  Mul [Add [Lit 1; Lit 2]; Add [Lit 3; Lit 4]].

Definition test_eval_add    : nat := eval test_add.        (* 6 *)
Definition test_eval_mul    : nat := eval test_mul.        (* 24 *)
Definition test_eval_nested : nat := eval test_nested.     (* 21 *)
Definition test_size_nested : nat := expr_size test_nested. (* 7 *)
Definition test_depth_nested : nat := expr_depth test_nested. (* 2 *)
Definition test_literals    : list nat := literals test_nested. (* [1;2;3;4] *)

(* lit_map: double all literals, then eval *)
Definition test_doubled : nat :=
  eval (lit_map (fun n => n * 2) test_nested). (* (2+4)*(6+8) = 6*14 = 84 *)

(* ===================================================================== *)
(* Combined test tuple (all test values from both parts) *)
(* ===================================================================== *)

Definition t : nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * list nat * nat :=
  (test_root_leaf,
   test_root_small,
   test_children_leaf,
   test_children_small,
   test_children_bigger,
   test_eval_add,
   test_eval_mul,
   test_eval_nested,
   test_size_nested,
   test_depth_nested,
   test_literals,
   test_doubled).

End NestedInd.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nested_ind" NestedInd.
