(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug: concept extraction does not handle typeclass functions with derived
   type parameters well. The typeclass extracts as three functions
   that take a singular T first. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Extraction Mapping.Std Mapping.NatIntStd.

Module ConceptParamMismatch.

  Class C (T : Type) :=
    { f : T * T -> T;
      g : T -> T;
      h : list T -> T -> T }.


  Instance cNat : C nat :=
    { f := fun p => fst p + snd p;
      g := S;
      h := fun l e => e }.

  Definition test := h [] (g 5).

End ConceptParamMismatch.

Crane Extraction "concept_param_mismatch" ConceptParamMismatch.
