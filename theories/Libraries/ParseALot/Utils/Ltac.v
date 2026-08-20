(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Nat.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.

(** Invert a hypothesis and substitute equalities, then clear it. *)
Ltac inv H := inversion H; subst; clear H.
(* destruct a match in a hypothesis *)
(** Destruct the first match expression found in a hypothesis. *)
Ltac dmh := match goal with | H : context[match ?x with | _ => _ end] |- _ => destruct x eqn:?E end.
(* destruct a match in the goal *)
(** Destruct the first match expression found in the goal. *)
Ltac dmg := match goal with | |- context[match ?x with | _ => _ end] => destruct x eqn:?E end.
(** Try [dmh] then [dmg], followed by [auto]. *)
Ltac dm := (first [dmh | dmg]); auto.

(** [b = false] iff [b ≠ true]; compatibility alias for [Bool.not_true_iff_false]. *)
Lemma false_not_true : forall(b : bool), b = false <-> not(b = true).
Proof. intros b. split; apply Bool.not_true_iff_false. Qed.

(** Inject through a pair or [Some] equality in a hypothesis, then substitute and clear. *)
Ltac inj_all :=
  match goal with
  | H:context [ (_, _) = (_, _) ] |- _
    => injection H; intros; subst; clear H
  | H:context [ Some _ = Some _ ] |- _
    => injection H; intros; subst; clear H
  end.

(** Rewrite a natural-number [=?] hypothesis using [Nat.eqb_eq], normalising via [false_not_true]. *)
Ltac eqb_eq_all :=
  match goal with
  | H:context [ (_ =? _) = _ ] |- _ => try(rewrite false_not_true in H); rewrite Nat.eqb_eq in H
  end.

(** Rewrite a natural-number [<?] hypothesis using [Nat.ltb_lt], normalising via [false_not_true]. *)
Ltac ltb_lt_all :=
  match goal with
  | H:context [ (_ <? _) = _ ] |- _ => try(rewrite false_not_true in H); rewrite Nat.ltb_lt in H
  end.

(** Shorthand for [try congruence]. *)
Ltac tc := try congruence.

(** Shorthand for [simpl in *]. *)
Ltac sis := simpl in *.
