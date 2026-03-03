(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Polymorphic inductives with universe constraints. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PolyInductive.

Set Universe Polymorphism.

(* Polymorphic identity wrapper *)
Polymorphic Inductive pbox@{u} (A : Type@{u}) : Type@{u} :=
  | PBox : A -> pbox A.

Polymorphic Definition punbox@{u} {A : Type@{u}} (b : pbox A) : A :=
  match b with PBox _ x => x end.

(* Polymorphic pair — different from Stdlib prod *)
Polymorphic Inductive ppair@{u v} (A : Type@{u}) (B : Type@{v}) : Type@{max(u,v)} :=
  | PPair : A -> B -> ppair A B.

Polymorphic Definition pfst@{u v} {A : Type@{u}} {B : Type@{v}} (p : ppair A B) : A :=
  match p with PPair _ _ a _ => a end.

Polymorphic Definition psnd@{u v} {A : Type@{u}} {B : Type@{v}} (p : ppair A B) : B :=
  match p with PPair _ _ _ b => b end.

(* Polymorphic option *)
Polymorphic Inductive pmaybe@{u} (A : Type@{u}) : Type@{u} :=
  | PNothing : pmaybe A
  | PJust : A -> pmaybe A.

Polymorphic Definition pmaybe_map@{u v} {A : Type@{u}} {B : Type@{v}}
  (f : A -> B) (m : pmaybe A) : pmaybe B :=
  match m with
  | PNothing _ => PNothing B
  | PJust _ x => PJust B (f x)
  end.

Polymorphic Definition pmaybe_default@{u} {A : Type@{u}} (d : A) (m : pmaybe A) : A :=
  match m with
  | PNothing _ => d
  | PJust _ x => x
  end.

(* Polymorphic tree *)
Polymorphic Inductive ptree@{u} (A : Type@{u}) : Type@{u} :=
  | PLeaf : A -> ptree A
  | PNode : ptree A -> ptree A -> ptree A.

Polymorphic Fixpoint ptree_size@{u} {A : Type@{u}} (t : ptree A) : nat :=
  match t with
  | PLeaf _ _ => 1
  | PNode _ l r => S (ptree_size l + ptree_size r)
  end.

(* === Test values === *)

Definition test_pbox : nat := punbox (PBox nat 42).
Definition test_ppair_fst : nat := pfst (PPair nat bool 7 true).
Definition test_ppair_snd : bool := psnd (PPair nat bool 7 true).
Definition test_pjust : nat := pmaybe_default 0 (PJust nat 99).
Definition test_pnothing : nat := pmaybe_default 0 (PNothing nat).
Definition test_pmap : nat := pmaybe_default 0 (pmaybe_map S (PJust nat 5)).
Definition test_ptree : nat := ptree_size (PNode nat (PLeaf nat 1) (PNode nat (PLeaf nat 2) (PLeaf nat 3))).

End PolyInductive.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "poly_inductive" PolyInductive.
