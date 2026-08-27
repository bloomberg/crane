From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
(** A typeclass method polymorphic in its own type argument
    (`forall A, (A -> A) -> A -> A`): the instance takes the erased
    `std::function<std::any(std::any)>`, so the projection must adapt the
    caller's concrete closure to it. *)

Module ClassPolyMethodErasedFn.
Class Mapper := { mapf : forall (A : Type), (A -> A) -> A -> A }.
Instance Twice : Mapper := { mapf A f x := f (f x) }.
Definition go : nat := mapf nat (fun n => n + 3) 1.
End ClassPolyMethodErasedFn.
Crane Extraction "class_poly_method_erased_fn" ClassPolyMethodErasedFn.
