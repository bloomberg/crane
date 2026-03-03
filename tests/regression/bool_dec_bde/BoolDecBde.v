(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 10b: BDE mapping for Bool.bool_dec must stay directly compilable. *)

From Stdlib Require Import Bool.

Module BoolDecBde.

Definition eqb_dec (a b : bool) : bool :=
  if Bool.bool_dec a b then true else false.

Definition t1 : bool := eqb_dec true true.
Definition t2 : bool := eqb_dec true false.

End BoolDecBde.

Require Crane.Extraction.
From Crane Require Mapping.BDE.
Crane Extraction "bool_dec_bde" BoolDecBde.