(** [Vector.caseS] has a return type that mentions a type variable appearing
    nowhere in its value parameters, so the emitted template parameter is not
    deducible at the call site:

    {v
      no matching function for call to 'caseS'
      candidate template ignored: couldn't infer template argument 'T2'
    v} *)

Require Crane.Extraction.
Require Import Vector.

Module VectorCasesDeduction.

Definition v3 : Vector.t nat 3 :=
  Vector.cons _ 1 _ (Vector.cons _ 2 _ (Vector.cons _ 3 _ (Vector.nil _))).

Definition hd3 (v : Vector.t nat 3) : nat := Vector.hd v.

Definition test : nat := hd3 v3.

End VectorCasesDeduction.

Crane Extraction "vector_cases_deduction" VectorCasesDeduction.
