(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

From Crane.Libraries.ParseALot.Lexer Require Import Regex.

(** Functor providing the boolean matching function [exp_matchb] over a regex module [R]. *)
Module ImplFn (Import R : Regex.T).

  (** Boolean string matcher: decides [exp_match s r] by iterated differentiation. *)
  Fixpoint exp_matchb (s : String) (r : regex) :=
    match s, r with
    | [], _ => nullable r
    | x::xs, _ => exp_matchb xs (derivative x r)
    end.

End ImplFn.

(** Functor extending [ImplFn] with a lemma connecting [exp_matchb] and [derivative]. *)
Module LemmasFn (Import R : Regex.T).

  Include ImplFn R.
  Import R.Ty.

    (** [exp_matchb (a::s) r = true] iff [exp_matchb s (derivative a r) = true]; by [simpl]. *)
    Theorem der_matchb : forall(a : Sigma) (s : String) (r : regex),
        true = exp_matchb (a::s) r <-> true = exp_matchb s (derivative a r).
    Proof.
      intros a s r.
      split; generalize dependent r; induction s; intros r H; simpl; simpl in H; apply H.
    Qed.

End LemmasFn.

(** Functor proving correctness of [exp_matchb] with respect to [exp_match]. *)
Module CorrectFn (Import R : Regex.T).

  Include LemmasFn R.
  Import R.Ty.

    (** [exp_matchb (a::s) r = exp_matchb s (derivative a r)]; derived from [der_matchb]. *)
    Theorem der_matchb' : forall(a : Sigma) (s : String) (r : regex),
      exp_matchb (a::s) r = exp_matchb s (derivative a r).
    Proof.
      intros. destruct (exp_matchb (a :: s) r) eqn:E.
      - symmetry in E. rewrite der_matchb in E. auto.
      - symmetry. rewrite false_not_true in *.
        intros C. destruct E.
        symmetry in C. rewrite <- der_matchb in C. auto.
    Qed.

    (** [exp_matchb s r = true] iff [exp_match s r]; proven by induction using [der_match] and [nullable_bridge]. *)
    Theorem match_iff_matchb : forall(s : String) (r : regex),
        true = exp_matchb s r <-> exp_match s r.
    Proof.
      intros s r. split.
      {
        generalize dependent r. induction s; intros r H.
        - simpl in H. apply nullable_bridge. apply H.
        - apply der_match. apply der_matchb in H. apply IHs. apply H.
      }
      {
        generalize dependent r. induction s; intros r H.
        - simpl. apply nullable_bridge. apply H.
        - apply der_match in H. apply der_matchb. apply IHs in H. apply H.
      }
    Qed.

End CorrectFn.

(** Top-level matcher functor bundling implementation and correctness proofs. *)
Module MatcherFn (Import R : Regex.T).
  Include CorrectFn R.
End MatcherFn.
