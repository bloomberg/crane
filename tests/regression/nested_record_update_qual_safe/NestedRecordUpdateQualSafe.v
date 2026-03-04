(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: nested record updates keep qualified names valid *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module NestedRecordUpdateQualSafe.
Record cell : Type := Mk { value : nat }.
Definition bump (x : cell) : cell := match x with | Mk n => Mk (S n) end.
Definition project (x : cell) : nat := match x with | Mk n => n end.
Definition t : nat := project (bump (Mk 1)).
End NestedRecordUpdateQualSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nested_record_update_qual_safe" NestedRecordUpdateQualSafe.