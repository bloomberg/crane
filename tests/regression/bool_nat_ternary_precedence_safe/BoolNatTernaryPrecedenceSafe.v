(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: bool/nat branch lowering remains stable *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module BoolNatTernaryPrecedenceSafe.
Definition branch_left (b : bool) : nat := if b then 1 else 0.
Definition branch_right (b : bool) : nat := if b then 2 else 3.
Definition t : nat := branch_left true + branch_right false.
End BoolNatTernaryPrecedenceSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "bool_nat_ternary_precedence_safe" BoolNatTernaryPrecedenceSafe.