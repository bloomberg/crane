(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Nested inductives with Stdlib list — expression AST. *)
(* The existing regression/nested_inductive uses a custom list type. *)
(* This test uses Stdlib's list, exercising a different extraction path. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module NestedIndStdlibList.

(* === Nested inductive: expr uses list expr in constructors === *)

Inductive expr : Type :=
| Lit : nat -> expr
| Add : list expr -> expr
| Mul : list expr -> expr.

(* === Recursive functions via nested fix === *)
(* The nested fix pattern is required because Rocq's guard checker
   needs to see that recursive calls are on structural subterms
   reached through the list. *)

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

(* === Test values === *)

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

End NestedIndStdlibList.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nested_ind_stdlib_list" NestedIndStdlibList.
