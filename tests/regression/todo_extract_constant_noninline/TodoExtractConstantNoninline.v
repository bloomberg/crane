(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* A Parameter mapped by an operation mapping is a call of the C++ function it names (it was a non-inlined Crane Extract Constant, a generated forwarding function). *)

From Stdlib Require Import Nat.

Module TodoExtractConstantNoninline.

Parameter foreign_inc : nat -> nat.

Definition test_value : nat :=
  foreign_inc 4.

Definition twice_value : nat :=
  foreign_inc (foreign_inc 2).

End TodoExtractConstantNoninline.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.

From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Import PrimString.PStringNotations List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.
#[global] Instance foreign_inc_mapping : OperationMapping (Ref TodoExtractConstantNoninline.foreign_inc) :=
  pure ["todo_extract_constant_noninline_support.h"] ["n"] (Call "foreign_inc_impl" [] [Arg "n"]).
Crane Extraction "todo_extract_constant_noninline" TodoExtractConstantNoninline.
