(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: comparator helper paths are fully qualified *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module ComparatorLoweringParitySafe.
Module A. Module CmpLeft. Definition f (n : nat) : nat := n. End CmpLeft. End A.
Module B. Module CmpRight. Definition g (n : nat) : nat := S n. End CmpRight. End B.
Definition t : nat := A.CmpLeft.f 0 + B.CmpRight.g 1.
End ComparatorLoweringParitySafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "comparator_lowering_parity_safe" ComparatorLoweringParitySafe.