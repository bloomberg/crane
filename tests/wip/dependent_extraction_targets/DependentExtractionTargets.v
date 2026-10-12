(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: two [Crane Extraction] targets in one file, the later depending
    on the earlier, give a later header that does not compile even on its
    own: it includes the earlier header and then defines the enclosing
    struct, which that header already did -- "redefinition of
    'DependentExtractionTargets'".  The same for a submodule and its parent,
    for sibling modules [A] and [B] with [B] using [A], and for a section's
    definition and then its module.  [regression/cross_unit_duplicate_symbol]
    covers two files. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module DependentExtractionTargets.

Module Inner.
  Inductive t := A | B : nat -> t.
  Definition f (x : t) : nat := match x with A => 0 | B n => n end.
  Module Deep. Definition g : nat := f (B 4). End Deep.
End Inner.

Module A.
  Inductive t := T : nat -> t.
  Definition get (x : t) : nat := match x with T n => n end.
End A.

Module B.
  Definition use : nat := A.get (A.T 9).
End B.

Section S.
  Variable X : Type.
  Variable z : X.
  Fixpoint rep (n : nat) : list X := match n with 0 => [] | S m => z :: rep m end.
End S.

Definition result : nat := Inner.Deep.g + B.use + List.length (rep nat 7 3).

End DependentExtractionTargets.

Crane Extraction "dependent_extraction_targets_inner" DependentExtractionTargets.Inner.
Crane Extraction "dependent_extraction_targets_a" DependentExtractionTargets.A.
Crane Extraction "dependent_extraction_targets_b" DependentExtractionTargets.B.
Crane Extraction "dependent_extraction_targets_rep" DependentExtractionTargets.rep.
Crane Extraction "dependent_extraction_targets" DependentExtractionTargets.
