(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An evaluator for a type-indexed inductive.  Its result type is pinned down
    only by the index, so it erases to [std::any]; neither the pair-returning
    branch nor a call passed to [map] recovers the concrete type, and the two
    disagree about what the box holds. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module GadtIndexErasure.

Inductive expr : Type -> Type :=
| Lit : nat -> expr nat
| Bl : bool -> expr bool
| Ite : forall A, expr bool -> expr A -> expr A -> expr A
| Pair : forall A B, expr A -> expr B -> expr (A * B).

Fixpoint eval (A : Type) (e : expr A) : A :=
  match e with
  | Lit n => n
  | Bl b => b
  | Ite _ c t f => if eval _ c then eval _ t else eval _ f
  | Pair _ _ a b => (eval _ a, eval _ b)
  end.

(** The result is read out of the box at a pair type. *)
Definition direct : nat :=
  fst (eval _ (Pair _ _ (Ite _ (Bl true) (Lit 3) (Lit 4)) (Bl false))).

(** The evaluator is passed as a function value to [map], which instantiates
    it at [nat] while its signature still returns [std::any]. *)
Definition evalAll (l : list (expr nat)) : list nat := map (eval nat) l.

Definition run : nat := direct + fold_right Nat.add 0 (evalAll [Lit 1; Lit 2]).

End GadtIndexErasure.

Crane Extraction "gadt_index_erasure" GadtIndexErasure.run.
