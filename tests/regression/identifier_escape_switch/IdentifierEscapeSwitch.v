(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: escaping of parameter identifier named switch. *)

From Stdlib Require Import Nat.

Module IdentifierEscapeSwitch.

Definition id_from_param (switch : nat) : nat := switch.
Definition add_one_from_param (switch : nat) : nat := S (id_from_param switch).
Definition t : nat := add_one_from_param 6.

End IdentifierEscapeSwitch.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "identifier_escape_switch" IdentifierEscapeSwitch.
