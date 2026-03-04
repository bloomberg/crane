(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: option/tuple-like constructors compile cleanly *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module OptionTupleWrapperSafe.
Inductive tag : Type := SomeTag | NoneTag.
Definition pick_nat (b : bool) : nat := if b then 1 else 0.
Definition t : nat := pick_nat true.
End OptionTupleWrapperSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "option_tuple_wrapper_safe" OptionTupleWrapperSafe.