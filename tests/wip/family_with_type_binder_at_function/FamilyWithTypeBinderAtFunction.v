(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a type family parameter that takes a type as well as a value,
    instantiated at a constant family whose body is a function type, gets
    the type of the applied result as its template argument.  [app2]'s
    [P : Type -> nat -> Type] at [fun _ _ => nat -> nat] is called
    [app2<uint64_t>] -- the type of [use2 1], not of [use2] -- with a lambda
    returning a closure: "no matching function for call to 'app2'".  The
    same through a rank-2 motive [P : forall A, list A -> Type] at
    [fun _ _ => nat -> nat]: "no matching function for call to 'grect'".
    A family over values alone ([P : nat -> Type]) is instantiated at its
    body ([regression/type_family_constant_motive]). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FamilyWithTypeBinderAtFunction.

Definition app2 (P : Type -> nat -> Type) (f : forall A n, P A n) (A : Type) (n : nat) : P A n := f A n.

Definition use1 : list nat := app2 (fun A _ => list nat) (fun _ n => [n; n]) bool 3.
Definition use2 : nat -> nat := app2 (fun _ _ => nat -> nat) (fun _ n => fun x => x + n) unit 4.

Definition grect (P : forall A : Type, list A -> Type) (f : forall A, P A [])
  (f0 : forall A x (t : list A), P A t -> P A (x :: t)) (A : Type) (l : list A) : P A l :=
  (fix F (B : Type) (m : list B) {struct m} : P B m :=
     match m with [] => f B | x :: t => f0 B x t (F B t) end) A l.

Definition clos (l : list nat) : nat -> nat :=
  grect (fun _ _ => nat -> nat) (fun _ => fun x => x) (fun _ _ _ k => fun x => k (x + 1)) nat l.

Definition result : nat := List.length use1 + use2 1 + clos [1; 2] 1.

End FamilyWithTypeBinderAtFunction.

Crane Extraction "family_with_type_binder_at_function" FamilyWithTypeBinderAtFunction.
