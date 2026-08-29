From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module EtaClosureFixpoint.
  (** The [Fixpoint] form of the eta-expansion arity bug: [adder] is emitted
      as [uint64_t adder(uint64_t, uint64_t)], so [map adder ...] cannot build
      the [std::function<uint64_t(uint64_t)>] it is declared to produce. *)
  Fixpoint adder (n : nat) : nat -> nat :=
    match n with 0 => fun k => k | S j => fun k => S (adder j k) end.

  Definition run (k : nat) : nat :=
    fold_left (fun a f => f a) (map adder [1; 2; 3]) k.
End EtaClosureFixpoint.

Crane Extraction "eta_closure_fixpoint" EtaClosureFixpoint.
