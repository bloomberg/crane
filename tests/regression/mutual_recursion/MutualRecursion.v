(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Test mutually recursive functions and types.
   These might create complex ML AST patterns.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module MutualRecursion.

(* Mutually recursive functions *)
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S n' => odd n'
  end
with odd (n : nat) : bool :=
  match n with
  | O => false
  | S n' => even n'
  end.

(* More complex mutual recursion *)
Fixpoint sum_even_indices (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S n' => sum_odd_indices n' acc
  end
with sum_odd_indices (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S n' => sum_even_indices n' (acc + n)
  end.

(* Mutually recursive with multiple arguments *)
Fixpoint process_a (n : nat) (m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => process_b n' m + n
  end
with process_b (n : nat) (m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => process_a n' m + m
  end.

(* Mutually recursive types *)
Inductive expr : Type :=
| Val : nat -> expr
| BinOp : nat -> expr -> expr -> expr
| UnOp : nat -> expr -> expr.

(* Mutually recursive functions on the type *)
Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | Val n => n
  | BinOp op l r =>
      match op with
      | O => eval_expr l + eval_expr r
      | S _ => eval_expr l * eval_expr r
      end
  | UnOp op e' =>
      match op with
      | O => eval_expr e'
      | S _ => 0
      end
  end.

(* Three-way mutual recursion *)
Fixpoint f1 (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => 1 + f2 n'
  end
with f2 (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => 2 + f3 n'
  end
with f3 (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => 3 + f1 n'
  end.

Definition test_even := even 10.
Definition test_sum := sum_even_indices 5 0.
Definition test_eval := eval_expr (BinOp 0 (Val 5) (Val 10)).

End MutualRecursion.

Crane Extraction "mutual_recursion" MutualRecursion.
