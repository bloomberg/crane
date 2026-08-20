(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Utils Require Import AsciiFinite.
From Stdlib Require Import Ascii.
From Stdlib Require Import NArith.

(** Instantiates the [Sigma] module type with the ASCII alphabet, using [Ascii.compare] for the ordering. *)
Module Export Alphabet <: Sigma.

  Definition Sigma : Type := ascii.
  Definition SigmaEnum : list Sigma := asciiEnum.

  (** Comparison via [N_of_ascii] and [N.compare]; equals [Ascii.compare] by definition. *)
  Definition compareT := Ascii.compare.

  (** [compareT x y = Eq] iff [x = y]; [->] is [Ascii.compare_eq_iff], [<-] uses [N.compare_eq_iff]. *)
  Lemma compareT_eq : forall x y : Sigma, compareT x y = Eq <-> x = y.
  Proof.
    intros x y. split.
    - apply Ascii.compare_eq_iff.
    - intros ->. unfold compareT, Ascii.compare. apply N.compare_eq_iff. reflexivity.
  Qed.

  (** [compareT] is transitive; reduces to [N.lt_trans] for [Lt] and [N.compare_antisym] for [Gt]. *)
  Lemma compareT_trans : forall c x y z,
      compareT x y = c -> compareT y z = c -> compareT x z = c.
  Proof.
    intros c x y z H1 H2. unfold compareT, Ascii.compare in *.
    destruct c.
    - apply N.compare_eq_iff in H1, H2. apply N.compare_eq_iff. congruence.
    - rewrite N.compare_lt_iff in *. exact (N.lt_trans _ _ _ H1 H2).
    - pose proof (N.compare_antisym (N_of_ascii x) (N_of_ascii y)) as Axy.
      pose proof (N.compare_antisym (N_of_ascii y) (N_of_ascii z)) as Ayz.
      rewrite H1 in Axy. rewrite H2 in Ayz. simpl in Axy, Ayz.
      rewrite N.compare_lt_iff in Axy, Ayz.
      pose proof (N.lt_trans _ _ _ Ayz Axy) as Axz.
      rewrite <- N.compare_lt_iff in Axz.
      rewrite (N.compare_antisym (N_of_ascii z) (N_of_ascii x)). rewrite Axz. reflexivity.
  Qed.

  (** Every ASCII character belongs to [SigmaEnum]; delegates to [ascii_finite]. *)
  Lemma Sigma_finite : forall a : Sigma, In a SigmaEnum.
  Proof. apply ascii_finite. Qed.

  (** Decidable equality on ASCII characters; delegates to [ascii_dec]. *)
  Lemma Sigma_dec : forall a a' : Sigma, {a = a'} + {a <> a'}.
  Proof. apply ascii_dec. Qed.

  (** Identity coercion from [ascii] to [Sigma]. *)
  Definition ascii2Sigma (a : ascii) : Sigma := a.

End Alphabet.
