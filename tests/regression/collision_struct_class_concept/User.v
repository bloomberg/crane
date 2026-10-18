(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import collision_struct_class_concept.Cls.
From CraneTestsRegression Require Import collision_struct_class_concept.AstLike.

Definition to_ident (n : nat) : ident := Global n.

Definition check : bool := same 3 3.

Crane Extraction "collision_struct_class_concept" to_ident check.
