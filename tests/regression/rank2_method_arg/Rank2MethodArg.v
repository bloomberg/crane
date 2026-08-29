From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module Rank2MethodArg.
  (** A class method taking a rank-2 polymorphic function.  The instance
      applies it at [nat], but the erased callback returns [std::any] where the
      method's declared [uint64_t] return type is required. *)
  Class Applyer := { app2 : (forall A, A -> A) -> nat -> nat }.

  Instance AI : Applyer := { app2 := fun f n => f nat n }.

  Definition run (k : nat) : nat := app2 (fun A x => x) (k + 4).
End Rank2MethodArg.

Crane Extraction "rank2_method_arg" Rank2MethodArg.
