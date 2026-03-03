(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 7: escaping of parameter/member identifiers colliding in generated C++. *)

From Stdlib Require Import Nat.

Module IdentifierEscapeParam.

Definition id_from_param (double : nat) : nat := double.
Definition add_one_from_param (double : nat) : nat := S (id_from_param double).
Definition t : nat := add_one_from_param 6.

End IdentifierEscapeParam.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "identifier_escape_param" IdentifierEscapeParam.