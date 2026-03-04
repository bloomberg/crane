(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: declaration/definition signatures remain aligned *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module MkstateSignatureDriftSafe.
Inductive state : Type := S0 | S1.
Definition score (x : state) : nat := match x with | S0 => 1 | S1 => 2 end.
Definition t : nat := score S0 + score S1.
End MkstateSignatureDriftSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "mkstate_signature_drift_safe" MkstateSignatureDriftSafe.