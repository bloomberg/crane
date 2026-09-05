From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module Rank1PolymorphicDefinition.

(** A top-level definition whose type is [forall A, ...] erases its whole
    signature to [std::any], but the call sites pass concrete types unboxed. *)
Definition church := forall A : Type, (A -> A) -> A -> A.

Definition three : church := fun A f x => f (f (f x)).

Definition to_nat (c : church) : nat := c nat S 0.
Definition to_bool (c : church) : bool := c bool negb false.

Definition total : nat := to_nat three + (if to_bool three then 10 else 20).

End Rank1PolymorphicDefinition.
Crane Extraction "rank1_polymorphic_definition" Rank1PolymorphicDefinition.
