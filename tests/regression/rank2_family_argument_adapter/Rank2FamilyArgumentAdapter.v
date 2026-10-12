(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a function argument whose type is quantified over a type and
    mentions a family of it, [f0 : forall A x (t : list A), P A t -> P A (x
    :: t)], is adapted with the wrong signature, and the program throws
    [std::bad_any_cast].  The argument is erased to
    [crane_erase_fn<crane::obj>([](crane::obj, List<crane::obj>, uint64_t
    k) { ... })], which unboxes its list parameter as a [List<crane::obj>];
    [grect2] calls it with a [List<uint64_t>].  A rank-2 argument without
    the family works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module Rank2FamilyArgumentAdapter.

Definition grect2 (P : forall (A : Type), list A -> Type) (f : forall A, P A [])
  (f0 : forall A x (t : list A), P A t -> P A (x :: t)) (A : Type) (l : list A) : P A l :=
  (fix F (B : Type) (m : list B) {struct m} : P B m :=
     match m with [] => f B | x :: t => f0 B x t (F B t) end) A l.

Definition len2 (A : Type) (l : list A) : nat :=
  grect2 (fun _ _ => nat) (fun _ => 0) (fun _ _ _ k => S k) A l.

Definition result : nat := len2 nat [1; 2; 3].

End Rank2FamilyArgumentAdapter.

Crane Extraction "rank2_family_argument_adapter" Rank2FamilyArgumentAdapter.
