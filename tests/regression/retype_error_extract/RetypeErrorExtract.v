(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: extraction must not crash with Retyping.RetypeError when
   processing type-scheme constants whose bodies contain bound variables
   (e.g. definitions pulled in by Ascii or other stdlib modules). *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt.
From Stdlib Require Import Ascii.

From Crane Require Extraction.
From Crane Require Import Mapping.Std.

(* Regression: a type-scheme definition whose body is a lambda (e.g.,
   `myrel : Type -> Type := fun A => A -> A -> Prop`) causes
   Retyping.RetypeError(NotAType) when flag_of_type tries to compute
   its sort.  Extraction must not crash on such definitions. *)

Definition myrel (A : Type) : Type := A -> A -> Prop.

Definition value : nat := 42.

Crane Separate Extraction myrel value.
