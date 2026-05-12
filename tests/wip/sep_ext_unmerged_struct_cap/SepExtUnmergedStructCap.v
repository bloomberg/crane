From Crane Require Extraction.
From Crane Require Import Mapping.Std.

(* When Module Exprs contains Inductive expr (names differ),
   the inner struct should be 'Expr' (capitalized) to match references. *)
Module Exprs.
  Inductive expr : Type :=
  | Lit : nat -> expr
  | Neg : expr -> expr.
End Exprs.

Module UseExprs.
  Import Exprs.
  Definition make_neg (e : expr) : expr := Neg e.
End UseExprs.

Crane Separate Extraction UseExprs.
