From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module EtaClosureFirstClass.
  (** A definition whose body is a [let] followed by a lambda is eta-expanded
      into a two-argument C++ function.  Passing it first-class to [map] then
      fails, because a [uint64_t(uint64_t, uint64_t)] is not convertible to
      [std::function<uint64_t(uint64_t)>]. *)
  Definition mkclosure (n : nat) : nat -> nat :=
    let big := repeat n 100 in
    fun k => k + fold_left Nat.add big 0.

  Definition run (k : nat) : nat :=
    let fs := map mkclosure [1; 2; 3] in
    fold_left (fun a f => f a) fs k.
End EtaClosureFirstClass.

Crane Extraction "eta_closure_first_class" EtaClosureFirstClass.
