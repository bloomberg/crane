(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: nested qualified record updates under shadowing *)

From Stdlib Require Import Nat.

Module QualifiedRecordShadow.

Module Shadow.
  Record shadow : Type := Mk { value : nat }.
End Shadow.

Definition bump (x : Shadow.shadow) : Shadow.shadow :=
  match x with
  | Shadow.Mk n => Shadow.Mk (S n)
  end.

Definition t : Shadow.shadow := bump (Shadow.Mk 1).
End QualifiedRecordShadow.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "qualified_record_shadow" QualifiedRecordShadow.
