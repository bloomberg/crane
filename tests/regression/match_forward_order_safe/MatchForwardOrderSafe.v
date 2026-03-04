(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: match helper ordering remains valid *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module MatchForwardOrderSafe.
Inductive token : Type := A | B.
Definition choose (b : bool) : token := if b then A else B.
Definition encode (x : token) : nat := match x with | A => 1 | B => 0 end.
Definition t : nat := encode (choose false).
End MatchForwardOrderSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "match_forward_order_safe" MatchForwardOrderSafe.