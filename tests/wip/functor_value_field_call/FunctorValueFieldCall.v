From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: Nested functor application emits a call `C::zero()` for a module field that
    the argument module defines as a value (`static inline const uint64_t`), so
    the extracted header fails with "called object type 'uint64_t' is not a
    function or function pointer". *)

Module FunctorValueFieldCall.
Module Type CARRIER. Parameter t : Type. Parameter zero : t. End CARRIER.
Module NatC <: CARRIER. Definition t := nat. Definition zero := 0. End NatC.
Module Pairify (C : CARRIER) <: CARRIER.
  Definition t := (C.t * C.t)%type.
  Definition zero := (C.zero, C.zero).
End Pairify.
Module PN := Pairify NatC.
Module Q := Pairify PN.
Definition go : nat := fst (fst Q.zero).
End FunctorValueFieldCall.
Crane Extraction "functor_value_field_call" FunctorValueFieldCall.
