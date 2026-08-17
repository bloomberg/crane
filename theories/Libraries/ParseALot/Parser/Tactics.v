(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

(** Simplify all hypotheses and the goal simultaneously. *)
Ltac sis := simpl in *.

(** Invert hypothesis [H], substitute equalities, and clear [H]. *)
Ltac inv H := inversion H; subst; clear H.

(** Attempt to close the goal by congruence. *)
Ltac tc := try congruence.

(** Destruct the scrutinee of a [match] expression appearing in a hypothesis. *)
(* destruct a match in a hypothesis *)
Ltac dmh := match goal with
             | H : context[match ?x with | _ => _ end] |- _ => destruct x
             end.

(** Destruct the scrutinee of a [match] expression appearing in the goal. *)
(* destruct a match in the goal *)
Ltac dmg := match goal with
             | |- context[match ?x with | _ => _ end] => destruct x
             end.

(** Destruct a match in either a hypothesis or the goal, then try [auto]. *)
Ltac dm  := (first [dmh | dmg]); auto.

(** Repeatedly apply [dm] until no match remains to destruct. *)
Ltac dms := repeat dm.

(** Destruct a [match] in a hypothesis and record the case equation under a fresh name derived from [s]. *)
(* destruct a match in a hypothesis, and save the equality in the context *)
Ltac dmheq s := let Heq := fresh s in
                match goal with
                | H : context[match ?x with | _ => _ end] |- _ =>
                  destruct x eqn:Heq
                end.

(** Destruct a [match] in the goal and record the case equation under a fresh name derived from [s]. *)
(* destruct a match in the goal, and save the equality in the context *)
Ltac dmgeq s := let Heq := fresh s in
                match goal with
                | |- context[match ?x with | _ => _ end] => destruct x eqn:Heq
                end.

(** Destruct a [match] in either a hypothesis or the goal, saving the equation, then try [auto]. *)
Ltac dmeq s := (first [dmheq s | dmgeq s]); auto.

(** Repeatedly apply [dmeq s] until no match remains to destruct. *)
Ltac dmeqs s := repeat dmeq s.

(** Try to close a list-append goal by reassociating with [app_assoc] or [app_nil_r]. *)
Ltac apps := try solve [ repeat rewrite app_assoc; auto
                       | repeat rewrite <- app_assoc; auto
                       | repeat rewrite app_nil_r; auto].

(** Rewrite [app_nil_r] everywhere to eliminate trailing empty-list appends. *)
Ltac rew_anr := repeat rewrite app_nil_r in *.

(** Invert a hypothesis equating two [existT]-headed cons cells, exploiting injectivity of the constructor. *)
Ltac inv_cons_tokens_eq :=
  match goal with
  | H : @existT _ _ _ _ :: _ = @existT _ _ _ _ :: _ |- _ =>
    inv H
  end.

(** From a hypothesis [xs ++ ys = []] (or its symmetric form), derive [xs = []] and [ys = []]. *)
Ltac aen :=
  match goal with
  | H : ?xs ++ ?ys = [] |- _ =>
    apply app_eq_nil in H; destruct H; subst
  | H : [] = ?xs ++ ?ys |- _ =>
    symmetry in H; apply app_eq_nil in H; destruct H; subst
  end.
