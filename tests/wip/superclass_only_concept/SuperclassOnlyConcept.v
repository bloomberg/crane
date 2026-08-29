From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module SuperclassOnlyConcept.
  (** A class whose fields are all superclass instances has no methods of its
      own, so Crane emits [concept Both = requires { };] — a C++ requires
      expression must contain at least one requirement. *)
  Class Base (A : Type) := { b0 : A -> nat }.
  Class L1 (A : Type) := { l1_base :: Base A ; l1 : A -> nat }.
  Class L2 (A : Type) := { l2_base :: Base A ; l2 : A -> nat }.
  Class Both (A : Type) := { bl1 :: L1 A ; bl2 :: L2 A }.

  Instance BN : Base nat := { b0 := fun n => n }.
  Instance L1N : L1 nat := { l1_base := BN ; l1 := fun n => n + 1 }.
  Instance L2N : L2 nat := { l2_base := BN ; l2 := fun n => n + 2 }.
  Instance BothN : Both nat := { bl1 := L1N ; bl2 := L2N }.

  Definition go {A} `{Both A} (x : A) : nat := b0 x + l1 x + l2 x.

  Definition run (k : nat) : nat := go (k + 1).
End SuperclassOnlyConcept.

Crane Extraction "superclass_only_concept" SuperclassOnlyConcept.
