From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A typeclass parameterised by a type constructor (`Container (F : Type -> Type)`).
    The higher-kinded parameter is demoted to a promoted associated type holding
    the element-erased carrier, so the concept, the instance and the method
    wrappers all agree. *)

Module ClassTypeConstructorParam.
Class Container (F : Type -> Type) := { cmap : forall A B, (A -> B) -> F A -> F B ; cwrap : forall A, A -> F A ; cout : forall A, F A -> A }.
Instance IdC : Container (fun A => A) := { cmap A B f x := f x ; cwrap A x := x ; cout A x := x }.
Definition go : nat := cout _ (cmap _ _ (fun n : nat => n + 1) (cwrap _ 4)).
End ClassTypeConstructorParam.
Crane Extraction "class_type_constructor_param" ClassTypeConstructorParam.
