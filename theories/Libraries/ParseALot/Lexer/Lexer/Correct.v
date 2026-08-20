(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia Wf_nat.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Lemmas.

(** Soundness and completeness proofs for the concrete lexer implementation. *)
Module CorrectFn (Import ST : State.T).

  Import ST.Defs.
  Import ST.Ty.
  (** Local alias for the full-lexer lemmas functor instantiated at [ST]. *)
  Module Lem := LemmasFn ST.
  Import Lem.
  Import Lem.Impl.
  Import Lem.Impl.Lem.
  Import Lem.Impl.Lem.Impl.

  (** Soundness of [lex']: the token stream it returns satisfies [tokenized], by well-founded induction on code length. *)
  Theorem lex'_sound : forall (x : nat) (Ha_x : Acc lt x) code i Hindex
                         (Ha : Acc lt (length code)) ts rest rus,
      x = length code
      -> lex' (map Lem.Impl.init_srule rus) code i Hindex Ha = (ts, rest)
      -> rules_is_function rus
      -> tokenized rus code ts rest.
  Proof.
    intros x Ha_x. induction Ha_x. intros.
    subst.
    destruct ts.
    {
      assert(Aeq : code = rest).
      { apply lex'_cases in H2. destruct H2. auto. }
      subst rest.
      apply Tkd0. intros t C. inv C.
      apply no_tokens_no_pref with (l := l) (r := r) in H2; auto.
      destruct H2; inv Hmpref; inv H1.
      - apply H8 in H2. destruct H2.
        + destruct p eqn:E.
          * contradiction.
          * simpl in H1. lia.
        + contradiction.
      - apply H6 in H2. contradiction.
    }
    {
      apply lex'_cases in H2.
      destruct t.
      destruct H2 as (h & t & s & i' & Heq' & H2). destruct H2.
      subst.
      assert(A0 : s = concat (map snd ts) ++ rest).
      { apply lex'_splits in H1. auto. }
      assert(A : code = (h :: t) ++ concat (map snd ts) ++ rest).
      {
        clear H1.
        apply exists_rus_of_mpref in Heq'.
        destruct Heq'. destruct H1.
        symmetry in H2. apply max_pref_fn_splits in H2.
        subst. auto.
      }
      rewrite A.
      apply Tkd1.
      - assert(i' = init_index (length s)).
        { eapply index_closure_mprefs. eauto. }
        clear H1. rewrite H2 in *.
        rewrite <- A. eapply first_token_mpref; eauto.
      - apply H0 with (y := length s) in H1; auto.
        + subst. auto.
        + subst. simpl. clear. induction t; simpl; lia.
    }
  Qed.

  (** Soundness of [lex]: the token stream satisfies [tokenized], instantiating [lex'_sound] with [lt_wf]. *)
  Theorem lex_sound : forall ts code rest rus,
      lex rus code = (ts, rest)
      -> rules_is_function rus
      -> tokenized rus code ts rest.
  Proof.
    intros. unfold lex in H.
    apply lex'_sound with (x := length code) in H; auto.
    apply lt_wf.
  Qed.

  (** Uniqueness of tokenization: any two [tokenized] witnesses for the same input must be equal; by induction on token list. *)
  Lemma tokenization_unique : forall ts ts' rest rest' code rus,
      tokenized rus code ts rest
      -> tokenized rus code ts' rest'
      -> (ts, rest) = (ts', rest').
  Proof.
    induction ts; intros.
    {
      inv H; inv H0; auto.
      assert(A : p <> []).
      { inv H2. auto. }
      apply H1 in H2. simpl in H2. contradiction.
    }
    {
      destruct ts'.
      - inv H0. inv H.
        assert(A : p <> []).
        { inv H5. auto. }
        apply H1 in H5. simpl in H5. contradiction.
      - inversion H. inversion H0. subst. rewrite H7 in *.
        clear H H0.
        apply first_token_unique with (t := (l0,p0)) in H5; auto.
        inv H5.
        apply app_inv_head in H7. rewrite H7 in *. clear H7.
        apply IHts with (rest := rest) in IH0; auto.
        inv IH0. auto.
    }
  Qed.

  (** Completeness of [lex]: if [tokenized] holds then [lex] returns exactly that result; follows from soundness and uniqueness. *)
  Theorem lex_complete : forall ts code rest rus,
      tokenized rus code ts rest
      -> rules_is_function rus
      -> lex rus code = (ts, rest).
  Proof.
    intros.
    destruct (lex rus code) eqn:E. apply lex_sound in E; auto.
    eapply tokenization_unique; eauto.
  Qed.

End CorrectFn.
