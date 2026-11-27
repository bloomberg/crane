(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Universe polymorphism. *)

From Stdlib Require Import Nat.

Module UniversePoly.

Set Universe Polymorphism.

(* === Polymorphic identity === *)

Polymorphic Definition poly_id {A : Type} (x : A) : A := x.

Definition test_id_nat : nat := poly_id 42.
Definition test_id_bool : bool := poly_id true.

(* === Polymorphic pair === *)

Polymorphic Record ppair (A B : Type) := mkppair {
  pfst : A;
  psnd : B
}.

Arguments mkppair {A B} _ _.
Arguments pfst {A B} _.
Arguments psnd {A B} _.

Definition test_pair : ppair nat bool := mkppair 5 true.
Definition test_pfst : nat := pfst test_pair.
Definition test_psnd : bool := psnd test_pair.

(* === Polymorphic option === *)

Polymorphic Inductive poption (A : Type) : Type :=
  | pnone : poption A
  | psome : A -> poption A.

Arguments pnone {A}.
Arguments psome {A} _.

Polymorphic Definition poption_map {A B : Type} (f : A -> B) (o : poption A) : poption B :=
  match o with
  | pnone => pnone
  | psome x => psome (f x)
  end.

Polymorphic Definition poption_bind {A B : Type} (o : poption A) (f : A -> poption B) : poption B :=
  match o with
  | pnone => pnone
  | psome x => f x
  end.

Definition test_map_some : poption nat :=
  poption_map (fun n => n + 1) (psome 5).

Definition test_map_none : poption nat :=
  poption_map (fun n => n + 1) pnone.

Definition test_bind : poption nat :=
  poption_bind (psome 3) (fun n => psome (n + n)).

(* === Polymorphic list === *)

Polymorphic Fixpoint poly_length {A : Type} (l : list A) : nat :=
  match l with
  | nil => 0
  | cons _ rest => S (poly_length rest)
  end.

Definition test_length : nat := poly_length (cons 1 (cons 2 (cons 3 nil))).

End UniversePoly.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "universe_poly" UniversePoly.
