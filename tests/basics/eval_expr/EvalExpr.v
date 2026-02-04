(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

Inductive ty : Type := TNat | TBool.

Inductive expr : ty -> Type :=
| ENat  : nat -> expr TNat
| EBool : bool -> expr TBool
| EAdd  : expr TNat -> expr TNat -> expr TNat
| EEq   : expr TNat -> expr TNat -> expr TBool
| EIf   : forall t, expr TBool -> expr t -> expr t -> expr t.

Fixpoint eval {t} (e : expr t) : match t with TNat => nat | TBool => bool end :=
  match e with
  | ENat n => n
  | EBool b => b
  | EAdd a b => eval a + eval b
  | EEq a b => Nat.eqb (eval a) (eval b)
  | EIf _ c th el => if eval c then eval th else eval el
  end.

Require Crane.Extraction.
Require Import Crane.Mapping.Std 
               Crane.Mapping.NatIntStd.

Crane Extraction "eval_expr" eval.
