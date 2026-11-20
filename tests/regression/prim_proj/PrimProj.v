(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: primitive projections — Proj nodes instead of Case. *)

From Stdlib Require Import Nat.

Module PrimProj.

Set Primitive Projections.

Record point := mkPoint { px : nat; py : nat }.

Definition add_points (p1 p2 : point) : point :=
  mkPoint (p1.(px) + p2.(px)) (p1.(py) + p2.(py)).

Definition origin : point := mkPoint 0 0.

Definition translate (dx dy : nat) (p : point) : point :=
  mkPoint (p.(px) + dx) (p.(py) + dy).

End PrimProj.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "prim_proj" PrimProj.
