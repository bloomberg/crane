From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** Nested functor application: a field a functor reads through its module
    parameter may be extracted as a static data member in one argument module
    and as a nullary accessor in another, so the use site must accept both
    spellings, just as the generated concept does. *)

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
