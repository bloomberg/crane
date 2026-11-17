(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an instance binder that occurs only in the instance's
    constraints, not in its class arguments, is dropped from the template
    header.  [via {A B C} `{Conv A B} `{Conv B C} : Sz (A * C)] mentions [B]
    only in its two constraints.  The template header is built from the
    variables of the class arguments, renumbered densely, so it declares
    [T1, T2] for [A] and [C]; the constraints and the body still use the
    original numbering, and name [T3]: "use of undeclared identifier
    'T3'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module InstanceConstraintOnlyBinder.

Class Sz (A : Type) := { sz : A -> nat }.
Class Conv (A B : Type) := { conv : A -> B }.

#[export] Instance natBool : Conv nat bool := { conv := fun n => Nat.eqb n 0 }.
#[export] Instance boolNat : Conv bool nat := { conv := fun b => if b then 1 else 0 }.

#[export] Instance via {A B C} `{Conv A B} `{Conv B C} : Sz (A * C) :=
  { sz := fun _ => 1 }.

Definition result : nat := @sz _ (@via nat bool nat _ _) (0, 0).

End InstanceConstraintOnlyBinder.

Crane Extraction "instance_constraint_only_binder" InstanceConstraintOnlyBinder.
