From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module DepTypeFnAnyCast.
  (** The same producer/consumer erasure mismatch as [dep_return_any_cast],
      reached through a type-level function [dt : nat -> Type] instead of an
      [if]: the [any_cast] at the use site names a different type than the one
      stored, giving an uncaught [std::bad_any_cast]. *)
  Definition dt (n : nat) : Type := match n with 0 => nat | _ => list nat end.

  Definition mk (n : nat) : dt n :=
    match n with 0 => 5 | S _ => [1; 2; 3; 4] end.

  Definition run (k : nat) : nat :=
    (mk 0 : nat) + length (mk 1 : list nat) + k.
End DepTypeFnAnyCast.

Crane Extraction "dep_type_fn_any_cast" DepTypeFnAnyCast.
