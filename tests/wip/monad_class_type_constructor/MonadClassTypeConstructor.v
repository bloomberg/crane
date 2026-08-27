From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A monad typeclass over a type constructor (`Mon (M : Type -> Type)`) emits
    the instance name in value position (`MOpt` used as a value), and the bind
    body applies a `std::any`. *)

Module MonadClassTypeConstructor.
Class Mon (M : Type -> Type) := { mret : forall A, A -> M A ; mbind : forall A B, M A -> (A -> M B) -> M B }.
Definition Opt (A : Type) := option A.
Instance MOpt : Mon Opt := { mret A a := Some a ; mbind A B m f := match m with Some a => f a | None => None end }.
Definition prog : Opt nat := mbind _ _ (mret _ 20) (fun a => mret _ (a + 22)).
Definition go : nat := match prog with Some n => n | None => 0 end.
End MonadClassTypeConstructor.
Crane Extraction "monad_class_type_constructor" MonadClassTypeConstructor.
