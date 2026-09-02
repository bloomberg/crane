From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module GadtEvalBranchType.

(** A type-indexed [expr] evaluated recursively.  Each branch of [eval] has a
    different result type; Crane gives the whole match one branch's type:

      error: no viable conversion from returned value of type 'const Nat'
             to function return type 'std::pair<Nat, bool>' *)

Inductive expr : Type -> Type :=
| lit : nat -> expr nat
| bl : bool -> expr bool
| ite : forall A : Type, expr bool -> expr A -> expr A -> expr A
| pairE : forall A B : Type, expr A -> expr B -> expr (A * B).
Arguments ite {A} _ _ _.
Arguments pairE {A B} _ _.

Fixpoint eval {A} (e : expr A) : A :=
  match e in expr T return T with
  | lit n => n
  | bl b => b
  | ite c t f => if eval c then eval t else eval f
  | pairE x y => (eval x, eval y)
  end.

Definition run : nat * bool := eval (pairE (lit 3) (bl true)).

End GadtEvalBranchType.

Crane Extraction "gadt_eval_branch_type" GadtEvalBranchType.run.
