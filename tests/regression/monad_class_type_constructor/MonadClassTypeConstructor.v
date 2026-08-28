From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A monad typeclass over a type constructor (`Mon (M : Type -> Type)`), with a
    carrier (`Opt`) that is itself a definition.  Exercises the higher-kinded
    class parameter together with an erased callback passed to `mbind`. *)

Module MonadClassTypeConstructor.
Class Mon (M : Type -> Type) := { mret : forall A, A -> M A ; mbind : forall A B, M A -> (A -> M B) -> M B }.
Definition Opt (A : Type) := option A.
Instance MOpt : Mon Opt := { mret A a := Some a ; mbind A B m f := match m with Some a => f a | None => None end }.
Definition prog : Opt nat := mbind _ _ (mret _ 20) (fun a => mret _ (a + 22)).
Definition go : nat := match prog with Some n => n | None => 0 end.
End MonadClassTypeConstructor.
Crane Extraction "monad_class_type_constructor" MonadClassTypeConstructor.
