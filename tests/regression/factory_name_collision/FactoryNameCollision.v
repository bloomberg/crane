(** A constructor's factory method takes its name by lowercasing the
    constructor, without asking the naming oracle for a fresh one.  Two
    independent sources of collision follow, and both are expected to be
    resolved by renaming the factory, not by emitting a clash:

    - [lst] is methodified, so the definition [nil] lands inside the same
      struct as the factory for [Nil].  Both take no argument, so they differ
      only in return type, which C++ refuses to overload.

    - [Cons] and [CONS] differ only in case, so they lowercase to one factory
      name and the second declaration redeclares the first. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module FactoryNameCollision.
  Inductive other : Set := Only.

  Inductive lst : Set := Nil | Cons : nat -> lst -> lst.

  (** Methodified onto [lst]: its C++ name must stay clear of [Nil]'s factory. *)
  Definition nil (l : lst) : nat := match l with Nil => 0 | Cons x _ => x end.

  Inductive cased : Set := Mk : nat -> cased | MK : nat -> cased.

  Definition uncase (c : cased) : nat :=
    match c with Mk n => n | MK n => n + 1 end.

  Definition head : nat := nil (Cons 7 Nil).
  Definition cased_sum : nat := uncase (Mk 1) + uncase (MK 1).
End FactoryNameCollision.

Crane Extraction "factory_name_collision" FactoryNameCollision.
