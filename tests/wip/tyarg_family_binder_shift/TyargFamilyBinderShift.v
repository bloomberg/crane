(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A type-level binder that leaves no variable in the ML scheme -- a family
    over propositions, a proof -- still takes an argument position in the
    Rocq application.  Read by list position, such an argument shifts every
    later type argument onto the wrong scheme variable; read through the
    schema's binder map, it has no variable at all.
    - [after_family {A} (P : A -> Prop) {B}] has two scheme variables and
      three written type arguments.
    - [nil_after_family] mentions [B] only in its result, so a call cannot
      leave it to deduction and must name it at its own variable.
    - [Fix_F] and [eq_sig_rect] are the library shapes of the same thing. *)

From Stdlib Require Import List Arith PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TyargFamilyBinderShift.

Definition after_family {A : Type} (P : A -> Prop) {B : Type} (d : B) (l : list B) : B :=
  match l with x :: _ => x | [] => d end.

Definition picked : nat := @after_family nat (fun n => n = 0) nat 7 [3].

Definition nil_after_family {A : Type} (P : A -> Prop) {B : Type} (a : A) : list B := [].

Definition empty_len : nat := length (@nil_after_family nat (fun n => n = 0) bool 3).

Definition proof_then_type {P : Prop} (H : P) {A : Type} {B : Type} (a : A) (f : A -> B) : B := f a.

Definition applied : nat := @proof_then_type (1 = 1) eq_refl nat nat 4 S.

Definition count_down : nat -> nat :=
  Fix lt_wf (fun _ => nat)
    (fun n rec =>
       match n as m return (m = n -> nat) with
       | 0 => fun _ => 0
       | S k => fun e => S (rec k (eq_ind _ (fun x => k < x) (Nat.lt_succ_diag_r k) _ e))
       end eq_refl).

Definition counted : nat := count_down 5.

End TyargFamilyBinderShift.

Crane Extraction "tyarg_family_binder_shift" TyargFamilyBinderShift.
