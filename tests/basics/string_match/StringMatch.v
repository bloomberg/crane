(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: PrimString operations. *)

From Stdlib Require Import Nat Bool PrimString PrimInt63.

Module StringMatch.

Definition str_empty : string := ""%pstring.
Definition str_hello : string := "hello"%pstring.
Definition str_world : string := "world"%pstring.

Definition str_cat : string := cat "hello " "world".

Definition str_len_empty : int := length ""%pstring.
Definition str_len_hello : int := length "hello"%pstring.

Definition is_empty (s : string) : bool :=
  PrimInt63.eqb (length s) 0.

Definition test_empty_true : bool := is_empty "".
Definition test_empty_false : bool := is_empty "x".
Definition test_cat : string := cat "foo" "bar".

End StringMatch.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extraction "string_match" StringMatch.
