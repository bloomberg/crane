(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: option/tuple-like wrapper path under shadowed names *)

From Stdlib Require Import Bool.

Module OptionTupleWrapper.

Module Node.
  Inductive shadow : Type := TagA | TagB.
End Node.

Definition pick (b : bool) : Node.shadow := if b then Node.TagA else Node.TagB.
Definition t : Node.shadow := pick true.
End OptionTupleWrapper.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "option_tuple_wrapper" OptionTupleWrapper.