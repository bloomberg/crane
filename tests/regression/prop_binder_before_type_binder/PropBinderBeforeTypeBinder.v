(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a [Prop]-sorted binder ahead of a [Type] binder shifts which of
    a function's parameters Crane thinks are erased, so the call boxes the
    arguments of the type the [Type] binder stands for.
    - [pick {P : Prop} {A : Type} (d : A) (l : list A)] is called
      [pick<uint64_t>(crane::obj(0), ...)] against [T1 pick(T1 d, ...)]:
      "no matching function for call to 'pick'".
    - [pick2 {P : Prop} {A : Type} (H : P) (d e : A)], called as
      [pick2 t 4 5], becomes [pick2<uint64_t>(crane::obj(5), crane::obj(4))]:
      boxed, and in the wrong order.
    - An inductive [guarded (P : Prop) (A : Type)] used through
      [gget {P A}] fails the same way.
    - So does a section's [Variable P : nat -> Prop] declared before its
      [Variable A : Type].
    [{A : Type} {P : Prop}], in that order, works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module PropBinderBeforeTypeBinder.

Definition pick {P : Prop} {A : Type} (d : A) (l : list A) : A :=
  match l with x :: _ => x | [] => d end.

Definition picked : nat := @pick True nat 0 [5].

Lemma t : 1 = 1. Proof. reflexivity. Qed.

Definition pick2 {P : Prop} {A : Type} (H : P) (d : A) (e : A) : A := e.

Definition second : nat := pick2 t 4 5.

Inductive guarded (P : Prop) (A : Type) := G : P -> A -> guarded P A | N : guarded P A.
Arguments G {P A}. Arguments N {P A}.

Definition gget {P A} (d : A) (g : guarded P A) : A := match g with G _ x => x | N => d end.

Definition guard_sum : nat := gget 0 (G t 5) + gget 7 (@N (2 = 2) nat).

Section S.
  Variable Q : nat -> Prop.
  Variable dec : forall n, {Q n} + {~ Q n}.
  Variable A : Type.
  Variable def : A.
  Definition sel (n : nat) (a : A) : A := if dec n then a else def.
End S.

Definition selected : nat := sel (fun n => n = 2) (fun n => Nat.eq_dec n 2) nat 0 2 6.

End PropBinderBeforeTypeBinder.

Crane Extraction "prop_binder_before_type_binder" PropBinderBeforeTypeBinder.
