(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: helper names remain ODR-safe *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module HelperNameOdrSafe.
Definition helper_a (n : nat) : nat := n.
Definition helper_b (n : nat) : nat := S n.
Definition t : nat := helper_a 1 + helper_b 2.
End HelperNameOdrSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "helper_name_odr_safe" HelperNameOdrSafe.