(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Large mutual inductives — 5+ types defined together. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module LargeMutual.

(* === 5-way mutual inductive: simple expression language === *)

Inductive stmt : Type :=
  | SAssign : nat -> expr -> stmt
  | SSeq : stmt -> stmt -> stmt
  | SIf : bexpr -> stmt -> stmt -> stmt
  | SWhile : bexpr -> stmt -> stmt
  | SSkip : stmt
with expr : Type :=
  | ENum : nat -> expr
  | EVar : nat -> expr
  | EAdd : expr -> expr -> expr
  | EMul : expr -> expr -> expr
  | ECond : bexpr -> expr -> expr -> expr
with bexpr : Type :=
  | BTrue : bexpr
  | BFalse : bexpr
  | BEq : expr -> expr -> bexpr
  | BLt : expr -> expr -> bexpr
  | BAnd : bexpr -> bexpr -> bexpr
  | BOr : bexpr -> bexpr -> bexpr
  | BNot : bexpr -> bexpr.

(* === Mutual recursive functions over the 3-way mutual inductive === *)

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | ENum _ => 1
  | EVar _ => 1
  | EAdd l r => S (expr_size l + expr_size r)
  | EMul l r => S (expr_size l + expr_size r)
  | ECond b t f => S (bexpr_size b + expr_size t + expr_size f)
  end
with bexpr_size (b : bexpr) : nat :=
  match b with
  | BTrue => 1
  | BFalse => 1
  | BEq l r => S (expr_size l + expr_size r)
  | BLt l r => S (expr_size l + expr_size r)
  | BAnd l r => S (bexpr_size l + bexpr_size r)
  | BOr l r => S (bexpr_size l + bexpr_size r)
  | BNot b0 => S (bexpr_size b0)
  end.

Fixpoint stmt_size (s : stmt) : nat :=
  match s with
  | SAssign _ e => S (expr_size e)
  | SSeq s1 s2 => S (stmt_size s1 + stmt_size s2)
  | SIf b s1 s2 => S (bexpr_size b + stmt_size s1 + stmt_size s2)
  | SWhile b body => S (bexpr_size b + stmt_size body)
  | SSkip => 1
  end.

(* === Test values === *)

Definition test_expr : expr := EAdd (ENum 1) (EMul (ENum 2) (ENum 3)).
Definition test_bexpr : bexpr := BAnd (BEq (EVar 0) (ENum 5)) (BLt (EVar 1) (ENum 10)).
Definition test_stmt : stmt :=
  SSeq (SAssign 0 (ENum 42))
       (SIf (BEq (EVar 0) (ENum 42)) SSkip (SAssign 0 (ENum 0))).

Definition test_expr_size : nat := expr_size test_expr.
Definition test_bexpr_size : nat := bexpr_size test_bexpr.
Definition test_stmt_size : nat := stmt_size test_stmt.

End LargeMutual.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "large_mutual" LargeMutual.
