(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Multiple inductives, cross-referencing, expression evaluation. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module WhereClause.

(* Arithmetic expression type *)
Inductive Expr : Type :=
  | Num : nat -> Expr
  | Plus : Expr -> Expr -> Expr
  | Times : Expr -> Expr -> Expr.

Notation "a [+] b" := (Plus a b) (at level 50, left associativity).
Notation "a [*] b" := (Times a b) (at level 40, left associativity).

Fixpoint eval (e : Expr) : nat :=
  match e with
  | Num n => n
  | Plus a b => eval a + eval b
  | Times a b => eval a * eval b
  end.

Fixpoint expr_size (e : Expr) : nat :=
  match e with
  | Num _ => 1
  | Plus a b => 1 + expr_size a + expr_size b
  | Times a b => 1 + expr_size a + expr_size b
  end.

(* Boolean expression type *)
Inductive BExpr : Type :=
  | BTrue : BExpr
  | BFalse : BExpr
  | BAnd : BExpr -> BExpr -> BExpr
  | BOr : BExpr -> BExpr -> BExpr
  | BNot : BExpr -> BExpr.

Fixpoint beval (e : BExpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BAnd a b => andb (beval a) (beval b)
  | BOr a b => orb (beval a) (beval b)
  | BNot a => negb (beval a)
  end.

(* Combined expression referencing both *)
Inductive AExpr : Type :=
  | ANum : nat -> AExpr
  | APlus : AExpr -> AExpr -> AExpr
  | AIf : BExpr -> AExpr -> AExpr -> AExpr.

Fixpoint aeval (e : AExpr) : nat :=
  match e with
  | ANum n => n
  | APlus a b => aeval a + aeval b
  | AIf c t f => if beval c then aeval t else aeval f
  end.

(* Test values *)
Definition test_eval_plus : nat := eval (Num 3 [+] Num 4).
Definition test_eval_times : nat := eval (Num 5 [*] Num 6).
Definition test_eval_nested : nat :=
  eval ((Num 2 [*] Num 3) [+] Num 1).
Definition test_size : nat :=
  expr_size ((Num 2 [*] Num 3) [+] Num 1).
Definition test_beval : bool := beval (BAnd BTrue (BNot BFalse)).
Definition test_aeval : nat :=
  aeval (AIf (BAnd BTrue BTrue) (ANum 10) (ANum 20)).

End WhereClause.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "where_clause" WhereClause.
