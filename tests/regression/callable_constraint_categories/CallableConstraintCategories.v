From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module CallableConstraintCategories.

(** A callable parameter's constraint states the calls the body makes, with
    the operands' real categories: [map] hands its callback a borrowed
    element, [curry] a temporary pair, [foldl] a moved accumulator. *)
Inductive lst (A : Type) := nil | cons (a : A) (l : lst A).
Arguments nil {A}. Arguments cons {A}.

Definition curry {A B C} (f : A * B -> C) (a : A) (b : B) : C := f (a, b).

End CallableConstraintCategories.

Module CallableOps.
Import CallableConstraintCategories.

Fixpoint map {A B} (f : A -> B) (l : lst A) : lst B :=
  match l with nil => nil | cons a r => cons (f a) (map f r) end.

Fixpoint foldl {A B} (f : B -> A -> B) (acc : B) (l : lst A) : B :=
  match l with nil => acc | cons a r => foldl f (f acc a) r end.

End CallableOps.

Crane Extraction "callable_constraint_categories" CallableConstraintCategories CallableOps.
