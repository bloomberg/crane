(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import concept_prereq_in_collision.Cls.
From CraneTestsRegression Require Import concept_prereq_in_collision.AstLike.

Definition to_ident (n : nat) : ident := Global n.

Definition check : bool := same 3 3.

Definition first_key : key := 7.

Definition key_twice (k : key) : key := k + k.

Definition twice_first : bool := Nat.eqb (key_twice first_key) 14.

Crane Extraction "concept_prereq_in_collision" to_ident check first_key key_twice twice_first.
