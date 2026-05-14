(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: type args in concept requires bodies must be qualified. *)
(* When a module type parameter uses an external type parameterized by a
   member type (e.g. list t), the type arg must appear as typename M::t
   inside the concept requires body, not bare t. *)

From Stdlib Require Import List.
Import ListNotations.

Module ConceptQualifyArgs.

Module Type HasElements.
  Parameter t : Type.
  Parameter elements : list t.
  Parameter head_or : t -> t.
End HasElements.

Module UseElements (E : HasElements).
  Definition first_or_default (d : E.t) : E.t :=
    E.head_or d.
End UseElements.

Module NatElems <: HasElements.
  Definition t := nat.
  Definition elements : list nat := [1; 2; 3].
  Definition head_or (d : nat) : nat :=
    match elements with
    | x :: _ => x
    | [] => d
    end.
End NatElems.

Module UseNatElems := UseElements NatElems.

Definition test : nat :=
  UseNatElems.first_or_default 0.

End ConceptQualifyArgs.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "concept_qualify_args" ConceptQualifyArgs.
