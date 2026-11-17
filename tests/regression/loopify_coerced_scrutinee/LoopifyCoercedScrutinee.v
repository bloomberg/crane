From Crane Require Import Extraction.
From Crane.Mapping Require Import Std NatIntStd.

Set Crane Loopify.

(** A recursive call matched through a coercion is bound before the match,
    as one matched directly is.

    In a type-indexed evaluator [if eval c then ...] reads the call through a
    coercion to [bool], since [eval] returns its index erased.  Normalize left
    anything under a coercion where it stood, so the plan had no point to
    resume at, and Loopify bound the call itself, in a variable the plan knew
    nothing of.  Normalize now binds it; the continuation casts the result of
    the call it re-enters by. *)

Module LoopifyCoercedScrutinee.

Inductive expr : Type -> Type :=
| lit : nat -> expr nat
| bl : bool -> expr bool
| ite : forall A : Type, expr bool -> expr A -> expr A -> expr A
| iszero : expr nat -> expr bool.

Arguments ite {A} _ _ _.

Fixpoint eval {A} (e : expr A) : A :=
  match e in expr T return T with
  | lit n => n
  | bl b => b
  | ite c t f => if eval c then eval t else eval f
  | iszero n => Nat.eqb (eval n) 0
  end.

(** [n] conditionals, each taking its else branch until the innermost. *)
Fixpoint nest (n : nat) : expr nat :=
  match n with
  | O => lit 7
  | S m => ite (iszero (lit (S m))) (lit 1) (nest m)
  end.

Definition deep : nat := eval (nest 50).
Definition chosen : nat := eval (ite (ite (bl false) (bl false) (iszero (lit 0))) (lit 3) (lit 4)).

End LoopifyCoercedScrutinee.

Crane Extraction "loopify_coerced_scrutinee" LoopifyCoercedScrutinee.
