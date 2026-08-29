From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module TcMethodArityMismatch.
  (** A class method of type [A -> nat -> nat] whose instance is written as a
      one-argument function returning a closure.  The concept requires the
      two-argument form but the instance emits the one-argument form returning
      a lambda, so the [static_assert] on the concept fails. *)
  Class Mk (A : Type) := { mkf : A -> nat -> nat }.

  Instance MkNat : Mk nat :=
    { mkf := fun a => let b := a + 1 in fun k => k + b }.

  Definition useit `{Mk nat} (k : nat) : nat := mkf k k.

  Definition run (k : nat) : nat := useit (k + 2).
End TcMethodArityMismatch.

Crane Extraction "tc_method_arity_mismatch" TcMethodArityMismatch.
