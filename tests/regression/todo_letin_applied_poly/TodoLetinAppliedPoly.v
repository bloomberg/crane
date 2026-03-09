(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: let-bound polymorphic helpers applied immediately. *)

From Stdlib Require Import Nat Bool.

Module TodoLetinAppliedPoly.

Definition demo_nat : nat :=
  (let aux {A : Type} (x : A) : A := x in aux) 7.

Definition demo_bool : bool :=
  (let aux {A : Type} (x : A) : A := x in aux) true.

Definition test_value : nat :=
  if demo_bool then demo_nat else 0.

End TodoLetinAppliedPoly.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_letin_applied_poly" TodoLetinAppliedPoly.
