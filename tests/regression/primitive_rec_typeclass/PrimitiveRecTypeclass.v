(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Primitive projections combined with typeclasses. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PrimitiveRecTypeclass.

Set Primitive Projections.

(* Record with primitive projections *)
Record point := mk_point {
  px : nat;
  py : nat
}.

(* Typeclass using primitive projections *)
Class HasNorm (A : Type) := {
  norm : A -> nat
}.

Instance pointNorm : HasNorm point := {
  norm := fun p => px p + py p
}.

(* Another record with primitive projections *)
Record vec3 := mk_vec3 {
  vx : nat;
  vy : nat;
  vz : nat
}.

Instance vec3Norm : HasNorm vec3 := {
  norm := fun v => vx v + vy v + vz v
}.

(* Generic function using the typeclass *)
Definition double_norm {A : Type} `{HasNorm A} (x : A) : nat :=
  norm x + norm x.

(* Nested records with primitive projections *)
Record rect := mk_rect {
  top_left : point;
  bot_right : point
}.

Definition rect_width (r : rect) : nat :=
  px (bot_right r) - px (top_left r).

Definition rect_height (r : rect) : nat :=
  py (bot_right r) - py (top_left r).

Definition rect_perimeter (r : rect) : nat :=
  2 * (rect_width r + rect_height r).

(* === Test values === *)

Definition p1 := mk_point 3 4.
Definition p2 := mk_point 10 20.
Definition test_px : nat := px p1.
Definition test_py : nat := py p1.
Definition test_norm_point : nat := norm p1.
Definition test_double_norm : nat := double_norm p1.

Definition v1 := mk_vec3 1 2 3.
Definition test_norm_vec3 : nat := norm v1.

Definition r1 := mk_rect (mk_point 2 3) (mk_point 12 8).
Definition test_width : nat := rect_width r1.
Definition test_height : nat := rect_height r1.
Definition test_perimeter : nat := rect_perimeter r1.

End PrimitiveRecTypeclass.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "primitive_rec_typeclass" PrimitiveRecTypeclass.
