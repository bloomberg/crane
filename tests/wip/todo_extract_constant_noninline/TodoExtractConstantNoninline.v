(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: non-inlined extracted constants should remain usable. *)

From Stdlib Require Import Nat.

Module TodoExtractConstantNoninline.

Parameter foreign_inc : nat -> nat.

Definition test_value : nat :=
  foreign_inc 4.

Definition twice_value : nat :=
  foreign_inc (foreign_inc 2).

End TodoExtractConstantNoninline.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extract Constant TodoExtractConstantNoninline.foreign_inc => "foreign_inc_impl" From "todo_extract_constant_noninline_support.h".
Crane Extraction "todo_extract_constant_noninline" TodoExtractConstantNoninline.
