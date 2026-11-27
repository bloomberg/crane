(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Constrained polymorphic universes. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module ConstrainedPoly.

Set Universe Polymorphism.

(* Identity with explicit polymorphism *)
Definition poly_id@{u} {A : Type@{u}} (x : A) : A := x.

(* Pair with two universe levels *)
Record UPair@{u v} (A : Type@{u}) (B : Type@{v}) : Type@{max(u,v)} := {
  ufst : A;
  usnd : B;
}.

Arguments Build_UPair {A B}.
Arguments ufst {A B}.
Arguments usnd {A B}.

Definition swap@{u v} {A : Type@{u}} {B : Type@{v}}
  (p : UPair A B) : UPair B A :=
  {| ufst := usnd p; usnd := ufst p |}.

(* Nested universe usage *)
Definition wrap_pair@{u v} {A : Type@{u}} {B : Type@{v}}
  (a : A) (b : B) : UPair A B :=
  {| ufst := a; usnd := b |}.

(* Polymorphic option *)
Inductive UOption@{u} (A : Type@{u}) : Type@{u} :=
  | USome : A -> UOption A
  | UNone : UOption A.

Arguments USome {A}.
Arguments UNone {A}.

Definition uoption_map@{u v} {A : Type@{u}} {B : Type@{v}}
  (f : A -> B) (o : UOption A) : UOption B :=
  match o with
  | USome x => USome (f x)
  | UNone => UNone
  end.

(* Test values *)
Definition test_id_nat : nat := poly_id 42.
Definition test_id_bool : bool := poly_id true.
Definition test_pair : UPair nat bool := wrap_pair 5 false.
Definition test_swap : UPair bool nat := swap test_pair.
Definition test_fst : nat := ufst test_pair.
Definition test_snd : bool := usnd test_pair.
Definition test_umap : UOption nat :=
  uoption_map (fun n => n + 1) (USome 9).

End ConstrainedPoly.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "constrained_poly" ConstrainedPoly.
