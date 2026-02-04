(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test matching on empty types (absurd patterns) *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module EmptyMatch.

(* Empty type (no constructors) *)
Inductive empty : Type := .

(* Absurd - eliminate empty type to anything *)
Definition absurd {A : Type} (e : empty) : A :=
  match e with end.

(* Function that uses empty - can never be called *)
Definition from_empty (e : empty) : nat := absurd e.

(* Either type for testing *)
Inductive either (A B : Type) : Type :=
| Left : A -> either A B
| Right : B -> either A B.

Arguments Left {A B} _.
Arguments Right {A B} _.

(* Handle left side, absurd on right (if B = empty) *)
Definition handle_left {A : Type} (e : either A empty) : A :=
  match e with
  | Left a => a
  | Right v => absurd v
  end.

(* Create a Left value for testing *)
Definition test_either : either nat empty := Left five.
Definition test_handle := handle_left test_either.

(* Empty match in complex expression *)
Definition complex_absurd {A B : Type} (e : empty) : either A B :=
  match e with end.

End EmptyMatch.

Crane Extraction "empty_match" EmptyMatch.
