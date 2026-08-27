From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
(** WIP: A typeclass method that is polymorphic in its own type argument
    (`forall A, (A -> A) -> A -> A`) erases the argument to
    `std::function<std::any(std::any)>`, but the instance body is emitted as a
    concrete lambda, so no viable conversion exists. *)

Module ClassPolyMethodErasedFn.
Class Mapper := { mapf : forall (A : Type), (A -> A) -> A -> A }.
Instance Twice : Mapper := { mapf A f x := f (f x) }.
Definition go : nat := mapf nat (fun n => n + 3) 1.
End ClassPolyMethodErasedFn.
Crane Extraction "class_poly_method_erased_fn" ClassPolyMethodErasedFn.
