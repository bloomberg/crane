(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyExpr.

(** Simple expression ADT with multiple recursive constructors. *)
Inductive expr : Type :=
| Val : nat -> expr
| Succ : expr -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr
| Cond : expr -> expr -> expr -> expr.

(** [eval e] evaluates an expression. Multi-constructor recursion. *)
Fixpoint eval (e : expr) : nat :=
  match e with
  | Val n => n
  | Succ e1 => S (eval e1)
  | Add e1 e2 => Nat.add (eval e1) (eval e2)
  | Mul e1 e2 => Nat.mul (eval e1) (eval e2)
  | Cond cond then_ else_ =>
    if Nat.ltb O (eval cond)
    then eval then_
    else eval else_
  end.

(** [depth e] computes expression depth. *)
Fixpoint depth (e : expr) : nat :=
  match e with
  | Val _ => O
  | Succ e1 => S (depth e1)
  | Add e1 e2 => S (Nat.max (depth e1) (depth e2))
  | Mul e1 e2 => S (Nat.max (depth e1) (depth e2))
  | Cond c t e_ => S (Nat.max (depth c) (Nat.max (depth t) (depth e_)))
  end.

(** [count_vals e] counts the number of Val nodes. *)
Fixpoint count_vals (e : expr) : nat :=
  match e with
  | Val _ => 1
  | Succ e1 => count_vals e1
  | Add e1 e2 => Nat.add (count_vals e1) (count_vals e2)
  | Mul e1 e2 => Nat.add (count_vals e1) (count_vals e2)
  | Cond c t e_ => Nat.add (count_vals c) (Nat.add (count_vals t) (count_vals e_))
  end.

(** [size e] counts total number of nodes. *)
Fixpoint size (e : expr) : nat :=
  match e with
  | Val _ => 1
  | Succ e1 => S (size e1)
  | Add e1 e2 => S (Nat.add (size e1) (size e2))
  | Mul e1 e2 => S (Nat.add (size e1) (size e2))
  | Cond c t e_ => S (Nat.add (size c) (Nat.add (size t) (size e_)))
  end.

(** [simplify e] performs algebraic simplification:
    Add(x, Val 0) = x, Add(Val 0, x) = x,
    Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0. *)
Fixpoint simplify (e : expr) : expr :=
  match e with
  | Val n => Val n
  | Succ e1 => Succ (simplify e1)
  | Add e1 e2 =>
    match simplify e1, simplify e2 with
    | Val O, s2 => s2
    | s1, Val O => s1
    | s1, s2 => Add s1 s2
    end
  | Mul e1 e2 =>
    match simplify e1, simplify e2 with
    | Val O, _ => Val O
    | _, Val O => Val O
    | Val n, s2 => if Nat.eqb n 1 then s2 else Mul (Val n) s2
    | s1, Val n => if Nat.eqb n 1 then s1 else Mul s1 (Val n)
    | s1, s2 => Mul s1 s2
    end
  | Cond c t e_ => Cond (simplify c) (simplify t) (simplify e_)
  end.

(* ========== ALTERNATIVE EXPRESSION ADT ========== *)

(** Alternative expression type for testing different evaluation strategy. *)
Inductive simple_expr : Type :=
| Lit : nat -> simple_expr
| Plus : simple_expr -> simple_expr -> simple_expr
| IfPos : simple_expr -> simple_expr -> simple_expr -> simple_expr.

(** [eval_simple e] evaluates simple expression with positive test. *)
Fixpoint eval_simple (e : simple_expr) : nat :=
  match e with
  | Lit n => n
  | Plus a b => Nat.add (eval_simple a) (eval_simple b)
  | IfPos cond then_ else_ =>
    if Nat.ltb O (eval_simple cond)
    then eval_simple then_
    else eval_simple else_
  end.

(** [depth_simple e] computes depth of simple expression tree. *)
Fixpoint depth_simple (e : simple_expr) : nat :=
  match e with
  | Lit _ => O
  | Plus a b => S (Nat.max (depth_simple a) (depth_simple b))
  | IfPos c t e_ => S (Nat.max (depth_simple c) (Nat.max (depth_simple t) (depth_simple e_)))
  end.

(* ========== SHAPE ADT WITH OR-PATTERNS ========== *)

(** Shape type demonstrating or-pattern matching. *)
Inductive shape : Type :=
| Circle : nat -> shape
| Square : nat -> shape
| Triangle : nat -> shape.

(** [sum_shapes l] sums values from shapes using unified pattern.
    Tests or-pattern style matching in Coq. *)
Fixpoint sum_shapes (l : list shape) : nat :=
  match l with
  | nil => O
  | cons s rest =>
    let val := match s with
              | Circle x => x
              | Square x => x
              | Triangle x => x
              end
    in Nat.add val (sum_shapes rest)
  end.

(** [count_by_shape l] counts shapes: (circles, squares, triangles). *)
Fixpoint count_by_shape (l : list shape) : nat * nat * nat :=
  match l with
  | nil => (O, O, O)
  | cons s rest =>
    let '(c, sq, t) := count_by_shape rest in
    match s with
    | Circle _ => (S c, sq, t)
    | Square _ => (c, S sq, t)
    | Triangle _ => (c, sq, S t)
    end
  end.

(* ========== CONDITIONAL EXPRESSION ADT ========== *)

(** Alternative expression type with conditionals for testing different evaluation patterns. *)
Inductive cond_expr : Type :=
| CLit : nat -> cond_expr
| CPlus : cond_expr -> cond_expr -> cond_expr
| CCond : cond_expr -> cond_expr -> cond_expr -> cond_expr.

(** [eval_cond e] evaluates conditional expression. *)
Fixpoint eval_cond (e : cond_expr) : nat :=
  match e with
  | CLit n => n
  | CPlus a b => Nat.add (eval_cond a) (eval_cond b)
  | CCond cond then_ else_ =>
    if Nat.ltb O (eval_cond cond)
    then eval_cond then_
    else eval_cond else_
  end.

(** [depth_cond e] computes depth of conditional expression tree. *)
Fixpoint depth_cond (e : cond_expr) : nat :=
  match e with
  | CLit _ => O
  | CPlus a b => S (Nat.max (depth_cond a) (depth_cond b))
  | CCond c t e_ => S (Nat.max (depth_cond c) (Nat.max (depth_cond t) (depth_cond e_)))
  end.

End LoopifyExpr.

Set Crane Loopify.
Crane Extraction "loopify_expr" LoopifyExpr.
