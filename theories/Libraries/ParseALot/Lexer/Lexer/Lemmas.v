(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.NatInt.NZOrder.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Impl.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import LemmasPref.

(** Lemmas about the full lexer loop [lex'], including case analysis, splitting, and first-token extraction. *)
Module LemmasFn (Import ST : State.T).

  Import ST.Defs.
  Import ST.Ty.
  (** Local alias for the concrete lexer implementation functor instantiated at [ST]. *)
  Module Impl := Impl.ImplFn ST.
  Import Impl.
  Import MatchSpec.
  (** Local alias for the prefix-level lemmas functor instantiated at [ST]. *)
  Module Lemmas := LemmasPref.LemmasFn ST.
  Import Lemmas.
  Import Lemmas.Impl.

  (** Unfolds one step of [lex'] to expose its match body; follows by unfolding the [Acc] destructor. *)
  Lemma lex'_eq_body :
    forall rules code i (Hindex : i = init_index (length code)) (Ha : Acc lt (length code)),
      (lex' rules code i Hindex Ha =
       (match max_of_prefs (max_prefs code i rules) as mpref'
              return max_of_prefs (max_prefs code i rules) = mpref' -> _
        with
        | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
        | (_, Some ([], _, _)) => fun _ => ([], code) (* Code cannot be processed further *)
        | (label, Some (ph :: pt, suffix, i')) =>
          fun Heq =>
            match (lex' rules suffix i'
                        (index_rec_call _ _ _ _ _ _ _ _ Hindex Heq)
                        (acc_recursive_call _ _ _ _ _ _ _ _ Ha Heq))
            with
            | (lexemes, rest) => (((label, ph :: pt) :: lexemes), rest)
            end
        end eq_refl)).
  Proof.
    intros rules code i Hindex Ha. unfold lex'. destruct Ha. auto.
  Qed.

  (** Backward direction of case analysis: given a concrete [max_of_prefs] result, characterises the output of [lex']. *)
  Lemma lex'_cases_backward :
    forall (rules : list sRule)
      (code : String)
      (i : index)
      (Hindex : i = init_index (length code))
      (Ha : Acc lt (length code))
      (pr : Label * option (Prefix * Suffix * index))
      (res : list Token * String)
      (Heq : max_of_prefs (max_prefs code i rules) = pr),
      match pr as mpref' return max_of_prefs (max_prefs code i rules) = mpref' -> _ with
      | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
      | (_, Some ([], _, _)) => fun _ => ([], code) (* Code cannot be processed further *)
      | (label, Some (h :: t, suffix, i')) =>
        fun Heq =>
          match (lex' rules suffix i'
                      (index_rec_call _ _ _ _ _ _ _ _ Hindex Heq)
                      (acc_recursive_call _ _ _ _ _ _ _ _ Ha Heq))
          with
          | (lexemes, rest) => (((label, h :: t) :: lexemes), rest)
          end
      end Heq = res
      -> match res with
        | ([], code') =>
          code' = code
          /\ (snd pr = None
             \/ exists suf i', snd pr = Some ([], suf, i'))
        | ((label, prefix) :: lexemes, rest) =>
          exists h t suffix i' (Heq' : max_of_prefs (max_prefs code i rules)
                               = (label, Some (h :: t, suffix, i'))),
          lex' rules suffix i'
               (index_rec_call _ _ _ _ _ _ _ _ Hindex Heq')
               (acc_recursive_call _ _ _ _ _ _ _ _ Ha Heq') = (lexemes, rest)
          /\ h :: t = prefix
        end.
  Proof.
    intros.
    repeat dm; intros; subst; simpl in *; try congruence.
    - split; inv H; eauto.
    - inv H. exists s0. exists p2. exists s. exists i0. exists Heq. split; auto.
    - split; inv H; eauto.
  Qed.

  (** Forward case analysis on [lex']: the result is either the empty-token stop case or a token-cons step. *)
  Lemma lex'_cases :
    forall rules code i Hindex Ha res,
      lex' rules code i Hindex Ha = res
      -> match res with
        | ([], code') =>
          code' = code
          /\ (snd (max_of_prefs (max_prefs code i rules)) = None
             \/ exists suf i', snd (max_of_prefs (max_prefs code i rules)) = Some ([], suf, i'))
        | ((label, prefix) :: lexemes, rest) =>
          exists h t suffix i' (Heq' : max_of_prefs (max_prefs code i rules)
                               = (label, Some (h :: t, suffix, i'))),
          lex' rules suffix i'
               (index_rec_call _ _ _ _ _ _ _ _ Hindex Heq')
               (acc_recursive_call _ _ _ _ _ _ _ _ Ha Heq') = (lexemes, rest)
          /\ h :: t = prefix
        end.
  Proof.
    intros; subst.
    rewrite lex'_eq_body.
    eapply lex'_cases_backward; eauto.
  Qed.

  (** If [lex'] produces no tokens then the remaining code equals the input; by [lex'_cases]. *)
  Lemma no_tokens_suffix_self : forall rus code rest i Hindex Ha,
      lex' rus code i Hindex Ha = ([], rest) -> code = rest.
  Proof.
    intros rus code rest i Hindex Ha H.
    apply lex'_cases in H. destruct H.
    symmetry. apply H.
  Qed.

  (** If [lex'] produces no tokens then each rule either has the empty max-prefix or no max-prefix; by case analysis on [max_of_prefs]. *)
  Lemma no_tokens_no_pref : forall code rest rus l r i Hindex Ha,
      lex' (map init_srule rus) code i Hindex Ha = ([], rest)
      -> In (l, r) rus
      -> re_max_pref code r [] \/ re_no_max_pref code r.
  Proof.
    intros code rest rus l r i Hindex Ha Hlex Hin.
    apply lex'_cases in Hlex. destruct Hlex.
    destruct H0; destruct (max_of_prefs (max_prefs code i (map init_srule rus))) eqn:E0;
      simpl in H0; [| destruct H0 as (suf & H0)].
    - rewrite H0 in E0. rewrite Hindex in *.
      apply no_mpref_no_pref with (l := l) (r := r) in E0.
      + right. apply E0.
      + apply Hin.
    - destruct H0. rewrite H0 in E0. rewrite Hindex in *.
      assert(x = init_index (length suf)).
      { eapply index_closure_mprefs; eauto. }
      rewrite H1 in *. clear H1.
      apply nil_mpref_nil_or_no_pref with (l := l) (r := r) in E0.
      + apply E0.
      + apply Hin.
  Qed.

  (** The max-prefix for a given regex is unique; by antisymmetry of the length ordering on prefixes. *)
  Lemma max_pref_unique : forall code r p p',
      re_max_pref code r p
      -> re_max_pref code r p'
      -> p = p'.
  Proof.
    intros code r p p' Hp Hp'.
    inv Hp. inv Hp'.
    assert(Hp := H1). assert(Hp' := H0).
    apply H5 in H1. apply H3 in H0. clear H3 H5.
    assert(A : length p <= length p' /\ length p' <= length p).
    { split; [destruct H1 | destruct H0]; try (apply H); try (contradiction). }
    assert (Aeq : length p' = length p).
    { lia. }
    apply eq_len_eq_pref with (x := code) in Aeq.
    apply Aeq. apply Hp. apply Hp'.
  Qed.

  (** The winner of [max_of_prefs] dominates every other entry; by extracting the list decomposition around the in-element. *)
  Lemma max_pref_longer : forall xs l p s i l' p' s' i' code,
      max_of_prefs xs = (l, Some(p, s, i))
      -> In (l', Some(p', s', i')) xs
      -> (l', Some(p', s', i')) <> (l, Some(p, s, i))
      -> p ++_= code
      -> p' ++_= code
      -> longer_pref (l, Some(p, s, i)) (l', Some(p', s', i')) = (l, Some(p, s, i)).
  Proof.
    intros xs l p s i l' p' s' i' code Hmax Hin Hneq Hpref Hpref'.
    assert(Apart : exists xs1 xs2, xs = xs1 ++ ((l', Some(p', s', i')) :: xs2)).
    { apply part_around_in. apply Hin.  }
    destruct Apart as (xs1 & xs2 & Apart).
    rewrite Apart in *.
    rewrite mpref_app_dist in Hmax. rewrite mpref_cons_longer in Hmax.
    destruct (max_of_prefs xs1); destruct (max_of_prefs xs2).
    unfold longer_pref in Hmax. unfold longer_pref.
    repeat dm; subst;
      try(rewrite <- E0 in Hmax; injection Hmax; intros; subst);
      repeat inj_all;
      repeat ltb_lt_all;
      repeat eqb_eq_all;
      try(lia);
      try(discriminate).
  Qed.

  (** If [p1] is shorter than [p2] and both are prefixes of [rus] at the same list, extracts the segment between them. *)
  Lemma app_smaller_pref : forall {T : Type} (rus p1 p2 s1 s2 : list T) a1 a2,
      length p1 < length p2
      -> rus = p1 ++ a1 :: s1
      -> rus = p2 ++ a2 :: s2
      -> exists x y, (x ++ a2 :: y = s1
                /\ p1 ++ a1 :: x = p2
                /\ rus = p1 ++ (a1 :: x) ++ (a2 :: y) ).
  Proof.
    intros T. induction rus; intros.
    - exfalso. assert(L := app_cons_not_nil p1 s1 a1). contradiction.
    - destruct p1; destruct p2; try(simpl in H; lia).
      + simpl in H0. injection H0. injection H1. intros. subst.
        exists p2. exists s2. split; [|split]; reflexivity.
      + injection H0. injection H1. intros.
        assert(H' : length p1 < length p2).
        { simpl in H. lia. }
        apply IHrus with (s1 := s1) (s2 := s2) (a1 := a1) (a2 := a2) in H'.
        2:{ apply H4. }
        2:{ apply H2. }
        subst.
        destruct H' as (x & y & H'). destruct H'. destruct H3.
        exists x. exists y. split; [|split].
        * auto.
        * simpl. rewrite H3. auto.
        * simpl. simpl in H5. rewrite H5. auto.
  Qed.


  (** If [max_of_prefs] returns a non-empty prefix then that prefix is the first token; by inverting the max-pref correctness lemma and priority ordering. *)
  Lemma first_token_mpref : forall rus code l ph pt suffix,
      max_of_prefs (max_prefs code (init_index (length code)) (map init_srule rus))
      = (l, Some (ph :: pt, suffix, init_index (length suffix)))
      -> rules_is_function rus
      -> first_token code rus (l, ph :: pt).
  Proof.
    intros rus code l ph pt suffix H Hfunc.
    assert(Aex := exists_rus_of_mpref rus code l (ph :: pt) suffix _  H).
    destruct Aex as [r]. destruct H0 as (Hin & Hmpref_fn).
    assert(Hmpref : re_max_pref code r (ph :: pt)).
    {
      symmetry in Hmpref_fn.
      assert(exists q, Some (ph :: pt, q, init_index (length q))
                  = max_pref_fn code (init_index (length code)) (init_state r)).
      { eexists; eauto. }
      apply re_max_pref_correct__Some in H0. auto.
    }
    apply FT1 with (r := r).
    - intros C. discriminate.
    - apply Hin.
    - apply Hmpref.
    - intros l0 r0 p0 Hlen Hmpref'. intros C.
      apply re_max_pref_correct__Some with (e := r0) in Hmpref'. destruct Hmpref'.
      assert(Ain : In (l0, max_pref_fn code (init_index (length code)) (init_state r0))
                      (max_prefs code (init_index (length code)) (map init_srule rus))).
      {
        apply part_around_in in C. destruct C as (rus1 & rus2 & C). rewrite C.
        unfold max_prefs. repeat rewrite map_app. repeat rewrite map_cons. simpl.
        apply in_or_app. right. simpl. left. reflexivity.
      }
      assert(Aneq : (l0, max_pref_fn code (init_index (length code)) (init_state r0))
                    <> (l, Some (ph :: pt, suffix, init_index (length suffix)))).
      { rewrite <- H0. intros C1. injection C1; intros; subst. lia. }
      apply max_pref_longer
        with (l' := l0) (p' := p0) (s' := x) (code := code) (i' := init_index (length x))
        in H.
      + rewrite <- H0 in *. unfold longer_pref in H. repeat dmh.
        * eqb_eq_all. lia.
        * contradiction.
        * ltb_lt_all. lia.
      + rewrite <- H0 in Ain. apply Ain.
      + rewrite <- H0 in Aneq. apply Aneq.
      + inv Hmpref. apply H1.
      + assert(A : exists q, Some (p0, q, init_index (length q))
                        = max_pref_fn code (init_index (length code)) (init_state r0)).
        { exists x. apply H0. }
        apply re_max_pref_correct__Some in A. inv A. apply H1.
    - intros r0 l0 Hearly Hin0 Hmpref0.
      assert(Hmpref_fn0 : max_pref_fn code (init_index (length code)) (init_state r0)
                          = Some (ph :: pt, suffix, init_index (length suffix))).
      {
        apply re_max_pref_correct__Some with (e := r0) in Hmpref0.
        destruct Hmpref0 as (x & Hmpref_fn0).
        assert(Asuff : x = suffix).
        {
          symmetry in Hmpref_fn. apply max_pref_fn_splits in Hmpref_fn.
          apply max_pref_fn_splits in Hmpref_fn0.
          rewrite Hmpref_fn in Hmpref_fn0. apply app_inv_head in Hmpref_fn0.
          symmetry. apply Hmpref_fn0.
        }
        subst. auto.
      }
      assert(Aneq : l <> l0).
      {
        intros C. subst. unfold rules_is_function in Hfunc.
        apply Hfunc with (r := r0) in Hin.
        2:{ apply Hin0. }
        subst. inv Hearly. apply In_least_index in Hin0.
        destruct Hin0. apply H0 with (n1 := x) in H1.
        2:{ apply H1. }
        lia.
      }
      inv Hearly. apply In_least_index in Hin. apply In_least_index in Hin0.
      assert(Hin' := Hin).
      destruct Hin as (n2 & Hleast). destruct Hin0 as (n1 & Hleast').
      assert(Alt : n1 < n2).
      { auto. }
      apply part_around_least_index in Hleast.
      destruct Hleast as (rus1 & rus2 & Hleast). destruct Hleast as (Heq & Hlen & Hnin).
      apply part_around_least_index in Hleast'.
      destruct Hleast' as (rus1' & rus2' & Hleast'). destruct Hleast' as (Heq' & Hlen' & Hnin').
      rewrite <- Hlen in Alt. rewrite <- Hlen' in Alt.
      clear Hlen Hlen'.
      apply app_smaller_pref with (rus := rus)
                                  (s1 := rus2')
                                  (s2 := rus2)
                                  (a2 := (l,r))
                                  (a1 := (l0, r0)) in Alt.
      2:{ apply Heq'. }
      2:{ apply Heq. }
      destruct Alt as (x & y & H1). destruct H1. destruct H2.
      clear H0 Heq Heq'.
      rewrite H3 in *.
      assert(A0 : max_of_prefs (map (extract_fsm_for_max code (init_index (length code)))
                                    (map init_srule rus1'))
                                <>  (l, Some (ph :: pt, suffix, init_index (length suffix)))).
      {
        intros C. apply exists_rus_of_mpref in C.
        destruct C as (r' & C). destruct C as (C1 & C2).
        destruct (regex_eq r r') eqn:E.
        - destruct Hnin.  apply regex_eq_correct in E. subst. apply in_or_app. left. apply C1.
        - subst. apply In_least_index in Hin'.
          assert(C1' : In (l, r') (rus1' ++ ((l0, r0) :: x) ++ (l, r) :: y)).
          { apply in_or_app. left. apply C1. }
          apply false_not_true in E. destruct E. apply regex_eq_correct.
          unfold rules_is_function in Hfunc. apply Hfunc with (l := l).
          + apply Hin'.
          + apply C1'.
      }
      unfold max_prefs in H.
      repeat first [rewrite map_cons in H | rewrite map_app in H].
      repeat first [rewrite mpref_cons_longer in H | rewrite mpref_app_dist in H].
      unfold longer_pref in H.
      repeat dmh; repeat simpl in *; rewrite Hmpref_fn in *; rewrite Hmpref_fn0 in *;
        repeat inj_all; subst; repeat ltb_lt_all; repeat eqb_eq_all; subst;
          try(lia); try(contradiction); try(discriminate).
  Qed.

  (** [lex'] output satisfies the split invariant: the input equals the concatenation of token payloads followed by the rest; by induction on [ts]. *)
  Lemma lex'_splits : forall ts code rest rus i Hindex Ha,
      lex' (map init_srule rus) code i Hindex Ha = (ts, rest)
      -> code = (concat (map snd ts)) ++ rest.
  Proof.
    induction ts; intros code rest rus i Hindex Ha H.
    {
      simpl. apply no_tokens_suffix_self in H. auto.
    }
    {
      destruct a. apply lex'_cases in H.
      destruct H as (h & t & H). destruct H as (s & i' & Heq & H).
      destruct H. apply IHts in H. rewrite Hindex in *.
      apply exists_rus_of_mpref in Heq. destruct Heq. destruct H1.
      symmetry in H2. apply max_pref_fn_splits in H2.
      subst. simpl.
      replace ((t ++ concat (map snd ts)) ++ rest)
        with (t ++ concat (map snd ts) ++ rest).
      2:{ apply app_assoc. }
      reflexivity.
    }
  Qed.

End LemmasFn.
