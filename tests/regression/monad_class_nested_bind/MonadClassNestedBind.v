From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module MonadClassNestedBind.

(** A monad class whose [bind] is polymorphic in both type arguments boxes
    and unboxes inconsistently across nested binds. *)
Class Monad (M : Type -> Type) := {
  ret : forall A : Type, A -> M A ;
  bind : forall A B : Type, M A -> (A -> M B) -> M B
}.

#[export] Instance MOption : Monad option := {
  ret := fun A x => Some x ;
  bind := fun A B m f => match m with Some x => f x | None => None end
}.

#[export] Instance MList : Monad list := {
  ret := fun A x => [x] ;
  bind := fun A B m f => flat_map f m
}.

Definition chain {M : Type -> Type} `{Monad M} (x : nat) : M (list nat) :=
  bind _ _ (ret _ x) (fun n => bind _ _ (ret _ (n + 1)) (fun m => ret _ [n; m])).

Definition total : nat :=
  match @chain option _ 1 with Some l => List.length l | None => 0 end
  + List.length (@chain list _ 2).

End MonadClassNestedBind.
Crane Extraction "monad_class_nested_bind" MonadClassNestedBind.
