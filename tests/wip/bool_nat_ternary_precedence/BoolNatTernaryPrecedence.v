(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: bool->nat branch helpers with keyword-style identifiers *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module BoolNatTernaryPrecedence.

Definition class (b : bool) : nat := if b then 1 else 0.
Definition class_ (b : bool) : nat := if b then 2 else 3.
Definition t : nat := class true + class_ false.
End BoolNatTernaryPrecedence.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "bool_nat_ternary_precedence" BoolNatTernaryPrecedence.