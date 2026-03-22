From Stdlib Require Import Nat.
From Stdlib Require Import List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyExprVariants.

(* Expression with conditional evaluation *)
Inductive cond_expr : Type :=
  | Lit : nat -> cond_expr
  | Add : cond_expr -> cond_expr -> cond_expr
  | Cond : cond_expr -> cond_expr -> cond_expr -> cond_expr.

Fixpoint eval_cond (e : cond_expr) : nat :=
  match e with
  | Lit n => n
  | Add a b => eval_cond a + eval_cond b
  | Cond cond then_ else_ =>
    if 0 <? eval_cond cond then eval_cond then_ else eval_cond else_
  end.

Fixpoint size_cond (e : cond_expr) : nat :=
  match e with
  | Lit _ => 1
  | Add a b => 1 + size_cond a + size_cond b
  | Cond c t e => 1 + size_cond c + size_cond t + size_cond e
  end.

(* Expression with multiplication and division *)
Inductive arith_expr : Type :=
  | ANum : nat -> arith_expr
  | AAdd : arith_expr -> arith_expr -> arith_expr
  | AMul : arith_expr -> arith_expr -> arith_expr
  | ADiv : arith_expr -> arith_expr -> arith_expr.

Fixpoint eval_arith (e : arith_expr) : nat :=
  match e with
  | ANum n => n
  | AAdd a b => eval_arith a + eval_arith b
  | AMul a b => eval_arith a * eval_arith b
  | ADiv a b =>
    match eval_arith b with
    | 0 => 0
    | b' => eval_arith a / b'
    end
  end.

Fixpoint count_ops (e : arith_expr) : nat :=
  match e with
  | ANum _ => 0
  | AAdd a b => 1 + count_ops a + count_ops b
  | AMul a b => 1 + count_ops a + count_ops b
  | ADiv a b => 1 + count_ops a + count_ops b
  end.

(* Boolean expression *)
Inductive bool_expr : Type :=
  | BTrue : bool_expr
  | BFalse : bool_expr
  | BAnd : bool_expr -> bool_expr -> bool_expr
  | BOr : bool_expr -> bool_expr -> bool_expr
  | BNot : bool_expr -> bool_expr.

Fixpoint eval_bool (e : bool_expr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BAnd a b => eval_bool a && eval_bool b
  | BOr a b => eval_bool a || eval_bool b
  | BNot a => negb (eval_bool a)
  end.

Fixpoint simplify_bool (e : bool_expr) : bool_expr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BAnd a b =>
    match simplify_bool a, simplify_bool b with
    | BFalse, _ => BFalse
    | _, BFalse => BFalse
    | BTrue, b' => b'
    | a', BTrue => a'
    | a', b' => BAnd a' b'
    end
  | BOr a b =>
    match simplify_bool a, simplify_bool b with
    | BTrue, _ => BTrue
    | _, BTrue => BTrue
    | BFalse, b' => b'
    | a', BFalse => a'
    | a', b' => BOr a' b'
    end
  | BNot a =>
    match simplify_bool a with
    | BTrue => BFalse
    | BFalse => BTrue
    | a' => BNot a'
    end
  end.

(* List expression - evaluates to a list *)
Inductive list_expr : Type :=
  | LNil : list_expr
  | LCons : nat -> list_expr -> list_expr
  | LAppend : list_expr -> list_expr -> list_expr
  | LReplicate : nat -> nat -> list_expr.

Fixpoint eval_list (e : list_expr) : list nat :=
  match e with
  | LNil => []
  | LCons x rest => x :: eval_list rest
  | LAppend a b => app (eval_list a) (eval_list b)
  | LReplicate n x => repeat x n
  end.

Fixpoint list_expr_size (e : list_expr) : nat :=
  match e with
  | LNil => 1
  | LCons _ rest => 1 + list_expr_size rest
  | LAppend a b => 1 + list_expr_size a + list_expr_size b
  | LReplicate _ _ => 1
  end.

End LoopifyExprVariants.

Set Crane Loopify.
Crane Extraction "loopify_expr_variants" LoopifyExprVariants.
