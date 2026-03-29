(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: IIFE inlining must not produce duplicate variable
   declarations when two sequential let-bindings each destructure
   a value with the same pattern variable names. *)

From Stdlib Require Import Nat.

Module IifeNameClash.

Inductive wrapper :=
  | Wrap (n : nat)
  | Empty.

Definition double_get (w1 w2 : wrapper) : nat :=
  let x := match w1 with Wrap n => n | Empty => 0 end in
  let y := match w2 with Wrap n => n | Empty => 0 end in
  x + y.

End IifeNameClash.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "iife_name_clash" IifeNameClash.
