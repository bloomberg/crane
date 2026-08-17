(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Wf_nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.NatInt.NZOrder.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import Memo.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Impl.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Lemmas.

(** Memoized lexer implementation and supporting lemmas, parameterized over a [Memo.T]. *)
Module ImplFn (Import MEM : Memo.T).

  Module Import Memo := MEM.MemTy.
  Module Import Defs := MEM.Defs.
  Import Defs.Invariants.
  Import Defs.NaiveLexer.
  Import Defs.NaiveLexer.Lem.Impl.
  Import MEM.STT.Defs.
  Import MEM.STT.Ty.
  Module Import Lem := LemmasFn MEM.STT.
  Import Lem.Lemmas.

  (** General list utility lemmas and pairing functions. *)
  Module Export Utils.

    (** Rearranges [xs ++ y :: ys] to [(xs ++ [y]) ++ ys]. *)
    Lemma app_cons_comm2 : forall {A : Type} ys xs (y : A),
      xs ++ y :: ys = (xs ++ [y]) ++ ys.
    Proof.
      intros. rewrite <- app_assoc. sis. auto.
    Qed.


    (** Zips two lists pairwise, stopping at the shorter one. *)
    Fixpoint zip {A B : Type} (a : list A) (b: list B) : list (A * B) :=
      match a, b with
      | ha :: ta, hb :: tb => (ha,hb) :: (zip ta tb)
      | _, _ => []
      end.

    (** Unzips a list of pairs into a pair of lists. *)
    Fixpoint unzip {A B : Type} (ab : list (A * B)) : (list A) * (list B) :=
      match ab with
      | [] => ([], [])
      | (ha, hb) :: t =>
        match unzip t with
        | (ta, tb) => (ha :: ta, hb :: tb)
        end
      end.

    (** The length of [zip xs ys] equals [length xs] when the lists have equal length; by induction. *)
    Lemma len_zip_L : forall {X Y : Type} (xs : list X) (ys : list Y),
        length xs = length ys
        -> length (zip xs ys) = length xs.
    Proof.
      induction xs; intros; auto.
      destruct ys.
      - sis. lia.
      - sis. apply f_equal. apply IHxs. lia.
    Qed.

    (** The length of [zip xs ys] equals [length ys] when the lists have equal length; by induction. *)
    Lemma len_zip_R : forall {X Y : Type} (xs : list X) (ys : list Y),
        length xs = length ys
        -> length (zip xs ys) = length ys.
    Proof.
      induction xs; intros; auto.
      destruct ys.
      - sis. lia.
      - sis. apply f_equal. apply IHxs. lia.
    Qed.

    (** The [n]-th element of [zip xs ys] equals the pair of [n]-th elements; by induction on [n]. *)
    Lemma nth_zip : forall n {X Y : Type} (xs : list X) (ys : list Y) dx dy,
        length xs = length ys
        -> n < length xs
        -> nth n (zip xs ys) (dx, dy) = (nth n xs dx, nth n ys dy).
    Proof.
      induction n; intros.
      - destruct xs; destruct ys; try(sis; auto; lia).
      - destruct xs; destruct ys; try(sis; auto; lia).
        sis. apply IHn; lia.
    Qed.

    (** Projects the second component of the second component of a nested triple. *)
    Definition ssnd {A B C : Type} (x : A * (B * C)) := snd (snd x).

  End Utils.

  (** Memoized single- and multi-rule prefix functions. *)
  Module Export MPref.

    (** Single-rule Prefixer **)
    Fixpoint max_pref_fn_M (M : Memo) (s : String) (i : index) (state : State)
    : Memo * option (String * String * index) :=
      match s with
      (* in a regex approach, accepting := nullable *)
      | [] => if accepting state then (M, Some ([],[],i))
             else ((set_Memo M (fst state) i None), None)
      | a :: s' =>
        let
          (* in a regex approach, transition := derivative *)
          state' := transition a state in
        let
          lookup := get_Memo M (fst state') (decr i) in
        let
          mpxs :=
          match lookup with
          | None => max_pref_fn_M M s' (decr i) state'
          | Some o => (M, o)
          end
        in

        match mpxs with
        | (M', None) => if (accepting state') then (M' , Some ([a], s', (decr i))) else
                         if (accepting state) then (M', Some ([], s, i)) else
                           ((set_Memo M' (fst state) i None), None)
        | (M', Some (p, q, qi)) => (M', Some (a :: p, q, qi))
        end
      end.

    (** Runs [max_pref_fn_M] for every rule in parallel, threading memos through each.
        Uses a direct fixpoint rather than [zip]/[map]/[unzip] to avoid closure capture
        of [code] in the extracted C++. *)
    Fixpoint max_prefs_M (Ms : list Memo) (code : String)
               (i : index) (erules : list (Label * State))
      : (list Memo) * list (Label * option (Prefix * Suffix * index)) :=
      match Ms, erules with
      | [], _ | _, [] => ([], [])
      | M :: Ms', (lbl, st) :: erules' =>
        match max_pref_fn_M M code i st with
        | (M', o) =>
          match max_prefs_M Ms' code i erules' with
          | (Ms'', rest) => (M' :: Ms'', (lbl, o) :: rest)
          end
        end
      end.

    (** Selects the best (longest) prefix from memoized multi-rule results, propagating the memo list. *)
    Definition max_of_prefs_M (mprefs : list Memo
                                     * list (Label * (option (Prefix * Suffix * index))))
      : list Memo * Label * option (Prefix * Suffix * index) :=
      match mprefs with
        (Ms, prefs) =>
        match max_of_prefs prefs with
          (l, o) => (Ms, l, o)
        end
      end.

  End MPref.

  (** Lemmas establishing that memoized computations match the naive lexer. *)
  Module Export TypeCheckLemmas.

    (** Lemmas about memo lookup correctness relative to [lexy]. *)
    Module Export MemoEq.

      (** A suffix at position [decr i] is the tail of a suffix at [i]; by unfolding [ith_suffix]. *)
      Lemma ith_suffix_cons : forall z code a i,
        ith_suffix code (a :: z) i -> ith_suffix code z (decr i).
      Proof.
        intros.
        unfold ith_suffix in *. destruct H. split.
        - sis. rewrite <- H. rewrite decr_inv_S. auto.
        - destruct H0. exists (x ++ [a]). rewrite <- app_cons_comm2. auto.
      Qed.

      (** A cached hit in a [lexy] memo agrees with [max_pref_fn]; directly from the [lexy] definition. *)
      Lemma lexy_correct : forall M pnt z o d code i,
        lexy code M d
        -> ith_suffix code z i
        -> get_Memo M pnt i = Some (o)
        -> max_pref_fn z i (pnt, d) = o.
      Proof.
        intros. unfold lexy in H. eapply H in H0; eauto.
      Qed.

      (** If [M] is [lexy] and [max_pref_fn_M] runs on a valid suffix, its result equals [max_pref_fn]; by induction on the string. *)
      Theorem mpref_memo_eq_lexy_F : forall z pnt o M M' d code i,
          lexy code M d
          -> ith_suffix code z i
          -> max_pref_fn_M M z i (pnt, d) = (M', o)
          -> max_pref_fn z i (pnt, d) = o.
      Proof.
        induction z; intros.
        - simpl in *. repeat dm; repeat inj_all; auto.
        - simpl in *.
          repeat dm;
          try( repeat inj_all; unfold lexy in H; apply ith_suffix_cons in H0;
            eapply H in E3; eauto; unfold fst in E3; dm; apply transition_Delta in E; subst;
            rewrite E3 in *; repeat inj_all; auto; discriminate );
          try( repeat inj_all; apply ith_suffix_cons in H0;
               destruct (transition a (pnt, d)) eqn:E7; apply transition_Delta in E7;
               rewrite E7 in *; eapply IHz in E; eauto; rewrite E in *; repeat inj_all;
               auto; discriminate ).
          + repeat inj_all. unfold lexy in H. apply ith_suffix_cons in H0. eapply H in E2; eauto.
            unfold fst in E2. dm. apply transition_Delta in E. rewrite E in *. rewrite E2 in *.
            discriminate.
          + repeat inj_all. unfold lexy in H. apply ith_suffix_cons in H0. eapply H in E2; eauto.
      Qed.

      (** Splits the head memo off a [max_prefs_M] computation over a cons-list. *)
      Lemma cons_mprefs__M : forall m Ms z a rules m' Ms' p lst i,
          max_prefs_M (m :: Ms) z i (a :: rules) = (m' :: Ms', p :: lst)
          -> max_prefs_M [m] z i [a] = ([m'], [p]) /\ max_prefs_M Ms z i rules = (Ms', lst).
      Proof.
        intros. unfold max_prefs_M in *. simpl in *. repeat dm; repeat inj_all; subst. auto.
      Qed.

      (** [max_prefs_M] produces the same labeled results as [max_prefs] under a [lexy_list] invariant; by induction on rules. *)
      Theorem mprefs_memo_F : forall z rules Ms Ms' lst i code,
          lexy_list code (zip Ms (map ssnd rules))
          -> length Ms = length rules
          -> max_prefs_M Ms z i rules = (Ms', lst)
          -> ith_suffix code z i
          -> max_prefs z i rules = lst.
      Proof.
        induction rules; intros.
        - destruct Ms;
            unfold max_prefs_M in H1; simpl in H1; repeat inj_all; subst; auto.
        - destruct Ms; try(discriminate).
          assert(A0 : lexy_list code (zip Ms (map ssnd rules))).
          { unfold lexy_list in *. intros. apply H. simpl. right. auto. }
          assert(A1 : length Ms = length rules).
          { simpl in H0. inv H0. auto. }
          destruct lst.
          + unfold max_prefs_M in H1. simpl in H1. repeat dm. discriminate.
          + destruct Ms'.
            * unfold max_prefs_M in H1. simpl in H1. repeat dm. discriminate.
            * simpl. unfold extract_fsm_for_max. dm. subst.
              apply cons_mprefs__M in H1. eapply IHrules in A0; destruct H1; eauto.
              unfold max_prefs_M in e. simpl in e. repeat dm. repeat inj_all; subst.
              destruct p0.
              assert(A2 : lexy code m d).
              { unfold lexy_list in *. apply H. simpl. left. auto. }
              eapply mpref_memo_eq_lexy_F in A2; eauto. subst. auto.
      Qed.

    End MemoEq.

    (** Lemmas about well-foundedness of the memoized recursion. *)
    Module Export Accessible.

      (** [max_of_prefs_M] yields the same winner as [max_of_prefs] under the invariant; follows from [mprefs_memo_F]. *)
      Lemma acc_helper__M : forall Ms code rules Ms' label o i orig,
        lexy_list orig (zip Ms (map ssnd rules))
        -> length Ms = length rules
        -> max_of_prefs_M (max_prefs_M Ms code i rules) = (Ms', label, o)
        -> ith_suffix orig code i
        -> max_of_prefs (max_prefs code i rules) = (label, o).
      Proof.
        intros. destruct (max_prefs code i rules) eqn:E;
                  destruct (max_prefs_M Ms code i rules) eqn:E1.
        - simpl in *. repeat dm; repeat inj_all; subst. eapply mprefs_memo_F in H; eauto.
          + rewrite E in H. subst. simpl in E0. auto.
        - simpl in *. repeat dm; repeat inj_all; subst. eapply mprefs_memo_F in H; eauto.
          rewrite E in H. subst. simpl in E0. auto.
      Qed.

      (** The suffix produced by a memoized recursive call is accessible; follows from [acc_helper__M] and [acc_recursive_call]. *)
      Lemma acc_recursive_call__M :
        forall code rules label s l suffix Ms Ms' i i' orig,
          Acc lt (length code)
          -> lexy_list orig (zip Ms (map ssnd rules))
          -> length Ms = length rules
          -> max_of_prefs_M (max_prefs_M Ms code i rules)
            = (Ms', label, Some (s :: l, suffix, i'))
          -> ith_suffix orig code i
          -> ith_suffix orig suffix i'
          -> Acc lt (length suffix).
      Proof.
        intros. eapply acc_helper__M in H0; eauto; eapply acc_recursive_call; eauto.
      Defined.


    End Accessible.

    (** Lemmas showing that [max_prefs_M] preserves memo-list lengths. *)
    Module Export Lengths.

      (** [max_prefs_M] returns as many memos as it received; by induction on [n]. *)
      Lemma memo_len_const : forall n Ms rules code Ms' l0 i,
        n = length Ms'
        -> length Ms = length rules
        -> max_prefs_M Ms code i rules = (Ms', l0)
        -> length Ms' = length Ms.
      Proof.
        induction n; intros; destruct rules; destruct Ms; destruct Ms'; destruct l0;
          try(simpl in *; auto; discriminate);
          try(unfold max_prefs_M in *; simpl in *; repeat dm; repeat inj_all; subst; discriminate).
        + simpl in *. injection H; intros; clear H. injection H0; intros; clear H0.
          apply cons_mprefs__M in H1. destruct H1. eapply IHn in H2; eauto.
      Qed.

      (** The labeled output list has the same length as the memo list; by induction on [n]. *)
      Lemma labeled_len_const : forall n Ms rules code Ms' l0 i,
          n = length Ms'
          -> length Ms = length rules
          -> max_prefs_M Ms code i rules = (Ms', l0)
          -> length Ms' = length l0.
      Proof.
        induction n; intros; destruct rules; destruct Ms; destruct Ms'; destruct l0;
          try(simpl in *; auto; discriminate);
          try(unfold max_prefs_M in *; simpl in *; repeat dm; repeat inj_all; subst; discriminate).
        + simpl in *. injection H; intros; clear H. injection H0; intros; clear H0.
          apply cons_mprefs__M in H1. destruct H1. eapply IHn in H2; eauto.
      Qed.

      (** Both length equalities hold simultaneously; combines [memo_len_const] and [labeled_len_const]. *)
      Lemma all_lens_const' : forall n Ms rules code Ms' l0 i,
          n = length Ms'
          -> length Ms = length rules
          -> max_prefs_M Ms code i rules = (Ms', l0)
          -> length Ms' = length Ms /\ length Ms' = length l0.
      Proof.
        intros. split.
        - eapply memo_len_const; eauto.
        - eapply labeled_len_const; eauto.
      Qed.

      (** Wrapper for [all_lens_const'] that does not require an explicit length witness. *)
      Lemma all_lens_const : forall Ms rules code Ms' l0 i,
          length Ms = length rules
          -> max_prefs_M Ms code i rules = (Ms', l0)
          -> length Ms' = length Ms /\ length Ms' = length l0.
      Proof.
        intros. eapply all_lens_const'; eauto.
      Qed.

      (** The output memo list has the same length as [rules] after a recursive call; by [all_lens_const]. *)
      Lemma len_recursive_call :
        forall code rules label s l suffix Ms Ms' i i',
          length Ms = length rules
          -> max_of_prefs_M (max_prefs_M Ms code i rules)
            = (Ms', label, Some (s :: l, suffix, i'))
          -> length Ms' = length rules.
      Proof.
        intros. destruct (max_prefs_M Ms code i rules) eqn:E.
        assert(l0 = Ms').
        {
          simpl in H0. repeat dm. injection H0; auto.
        }
        subst. clear H0.
        assert(L := all_lens_const Ms rules code Ms' l1 i H E). destruct L. lia.
      Qed.

    End Lengths.

    (** Lemmas showing that [lexy_list] is preserved across memoized computations. *)
    Module Export LexyClosure.

      (** Labels in the output of [max_prefs_M] match the input rule labels; by induction on [m]. *)
      Lemma nth_labels_match'' : forall m n rules Ms code Ms' l0 o ru label label' i,
        m = length rules
        -> length Ms = length rules
        -> length rules = length l0
        -> length Ms' = length Ms
        -> n < length Ms'
        -> max_prefs_M Ms code i rules = (Ms', l0)
        -> nth n l0 (defLabel, None) = (label, o)
        -> nth n rules (defLabel, defState) = (label', ru)
        -> label = label'.
      Proof.
        induction m; intros; destruct Ms; destruct rules; destruct Ms'; destruct l0; destruct n;
          try(simpl in *; lia).
        - apply cons_mprefs__M in H4. destruct H4. clear H7. simpl in *.
          unfold max_prefs_M in H4. simpl in *. repeat dm; repeat inj_all. auto.
        - simpl in *.
          apply Nat.succ_inj in H.  apply Nat.succ_inj in H0.
          apply Nat.succ_inj in H1. apply Nat.succ_inj in H2.
          apply PeanoNat.lt_S_n in H3.
          apply cons_mprefs__M in H4. destruct H4.
          eapply IHm; eauto.
      Qed.

      (** Wrapper for [nth_labels_match''] that derives length hypotheses from [all_lens_const]. *)
      Lemma nth_labels_match' : forall m n rules Ms code Ms' l0 o ru label label' i,
          m = length rules
          -> length Ms = length rules
          -> n < length Ms'
          -> max_prefs_M Ms code i rules = (Ms', l0)
          -> nth n l0 (defLabel, None) = (label, o)
          -> nth n rules (defLabel, defState) = (label', ru)
          -> label = label'.
      Proof.
        intros.
        assert(L := all_lens_const Ms rules code Ms' l0 i H0 H2). destruct L.
        eapply nth_labels_match''; eauto. lia.
      Qed.

      (** Label matching at a given index; drops the explicit length witness from [nth_labels_match']. *)
      Lemma nth_labels_match : forall n rules Ms code Ms' l0 o ru label label' i,
          max_prefs_M Ms code i rules = (Ms', l0)
          -> length Ms = length rules
          -> n < length Ms'
          -> nth n l0 (defLabel, None) = (label, o)
          -> nth n rules (defLabel, defState) = (label', ru)
          -> label = label'.
      Proof.
        intros. eapply nth_labels_match'; eauto.
      Qed.

      (** Identifies which [max_pref_fn_M] call produced the [n]-th output entry; by induction on [n]. *)
      Lemma mprefs__M_associates :
        forall n rules Ms Ms' code (l0 : list (Label * option (Prefix * Suffix * index)))
          M M' o label ru i,
          length Ms = length rules
          -> max_prefs_M Ms code i rules =
            (Ms', l0)
          -> n < length Ms'
          -> nth n Ms emptyMemo = M
          -> nth n Ms' emptyMemo = M'
          -> nth n l0 (defLabel, None) = (label, o)
          -> nth n rules (defLabel, defState) = (label, ru)
          -> max_pref_fn_M M code i ru = (M', o).
      Proof.
        induction n; intros; destruct Ms; destruct Ms'; destruct l0; destruct rules;
          try(simpl in *; lia);
          try(rewrite nil_mprefs__M in *; repeat inj_all; discriminate);
          try(simpl in *; repeat inj_all; unfold max_prefs_M in *; simpl in *;
              repeat dm; repeat inj_all; discriminate).
        + simpl in *. subst. unfold max_prefs_M in *. simpl in *.
          repeat dm. repeat inj_all. auto.
        + simpl in *. injection H; intros; clear H.
          apply PeanoNat.lt_S_n in H1. eapply IHn; eauto. eapply cons_mprefs__M; eauto.
      Qed.


      (** Equal-length suffixes of the same string starting at equal positions are identical; by induction. *)
      Lemma eq_len_suffix : forall {A : Type} (z0 z x0 x : list A),
          x0 ++ z0 = x ++ z
          -> length z = length z0
          -> x0 = x /\  z0 = z.
      Proof.
        induction z0; destruct z; intros; sis; auto; try(discriminate).
        - split; auto. do 2 rewrite app_nil_r in *. auto.
        - do 2 (rewrite app_cons_comm2 in H; symmetry in H).
          apply IHz0 in H; auto. destruct H. subst.
          assert(rev (x0 ++ [a]) = rev (x ++ [a0])).
          { apply f_equal. auto. }
          do 2 rewrite rev_unit in *. inv H1.
          assert(rev (rev x0) = rev (rev x)).
          { apply f_equal. auto. }
          do 2 rewrite rev_involutive in *. subst. auto.
      Qed.

      (** A memo extended with a new entry preserves [lexy] for any existing lookup; by case analysis on pointer equality and index equality. *)
      Lemma set_Memo_lexy : forall z z0 o o' p p0 d m code i i0,
          max_pref_fn z i (p, d) = o'
          -> lexy code m d
          -> get_Memo (set_Memo m p i o') p0 i0 = Some o
          -> ith_suffix code z i
          -> ith_suffix code z0 i0
          -> max_pref_fn z0 i0 (p0, d) = o.
      Proof.
        intros. destruct (String_dec z z0).
        (* originally tried to find an ordering on State *)
        (* realized that was too much, tried to find decidable equality *)
        (* seems like even that is too much, considering that
           the Table and final states doesn't change, only the state-pointer *)
        - rewrite e in *. clear e.
          assert(i = i0).
          { unfold ith_suffix in *. destruct H2. destruct H3. destruct H4. destruct H5.
            subst. auto. }
          rewrite H4 in *. clear H4. clear i.
          subst. destruct (pointer_compare p p0) eqn:E.
          + apply pointer_compare_eq in E. subst. rewrite correct_Memo in H1. inv H1. auto.
          + assert(p <> p0).
            { intros C. apply pointer_compare_eq in C. rewrite C in *. discriminate. }
            clear E.
            assert(p0 <> p \/ i0 <> i0); auto.
            eapply correct_Memo_moot in H4; eauto. rewrite H4 in H1.
            eapply lexy_correct; eauto.
          + assert(p <> p0).
            { intros C. apply pointer_compare_eq in C. rewrite C in *. discriminate. }
            clear E.
            assert(p0 <> p \/ i0 <> i0); auto.
            eapply correct_Memo_moot in H4; eauto. rewrite H4 in H1.
            eapply lexy_correct; eauto.
        - assert(i <> i0).
          { intros C. destruct n. unfold ith_suffix in *.
            destruct H2. destruct H3. destruct H4. destruct H5.
            subst. apply n_det_index in C. apply eq_len_suffix in H5; auto. destruct H5. auto. }
           assert(p0 <> p \/ i0 <> i); auto.
          clear n. eapply correct_Memo_moot in H5; eauto. rewrite H5 in H1.
          eapply lexy_correct; eauto.
      Qed.

      (** Two suffixes of the same original string at the same position are equal; by induction on length. *)
      Lemma ith_suffix_unique : forall z z' i orig,
          ith_suffix orig z i
          -> ith_suffix orig z' i
          -> z = z'.
      Proof.
        induction z; destruct z'; intros.
        - auto.
        - unfold ith_suffix in *. destruct H. destruct H0. rewrite <- H in *. sis.
          apply n_det_index in H0. discriminate.
        - unfold ith_suffix in *. destruct H. destruct H0. rewrite <- H in *. sis.
          apply n_det_index in H0. discriminate.
        - assert(z = z').
          {
            apply ith_suffix_cons in H. apply ith_suffix_cons in H0.
            eapply IHz; eauto.
          }
          subst z'.
          assert(a = s).
          {
            unfold ith_suffix in *. destruct H. destruct H0.
            destruct H1. destruct H2. rewrite <- H1 in *.
            apply f_equal with (f := @rev Sigma) in H2. repeat rewrite rev_app_distr in H2.
            sis. repeat rewrite <- app_assoc in *. apply app_inv_head in H2. sis.
            injection H2; intros; subst; auto.
          }
          subst a. auto.
      Qed.

      (** Running [max_pref_fn_M] on a [lexy] memo produces a [lexy] updated memo; by induction on the string. *)
      Lemma lexy_closure :
        forall code p d M o M' i orig,
          lexy orig M d
          -> max_pref_fn_M M code i (p,d) = (M', o)
          -> ith_suffix orig code i
          -> lexy orig M' d.
      Proof.
        induction code; intros.
        {
          assert(max_pref_fn [] i (p,d) = o).
          { eapply mpref_memo_eq_lexy_F; eauto. }
          simpl in H0. repeat dm.
          - inv H0. auto.
          - inv H0. rewrite H5. clear H5 E. unfold lexy. intros.
            destruct (Pointer_as_UCT.Pointer_eq_dec p stt).
            + destruct (index_eq_dec i i0).
              * subst.
                assert(z = []).
                { unfold ith_suffix in *. destruct H1. destruct H2.
                  rewrite <- H1 in *. apply n_det_index in H2.
                  sis. rewrite length_zero_iff_nil in H2. auto.
                }
                subst z.
                rewrite correct_Memo in H0. injection H0. sis. auto.
              * rewrite correct_Memo_moot in H0; auto.
            + rewrite correct_Memo_moot in H0; auto.
        }
        {
          destruct o;
            assert (H0' := H0);
            simpl in H0;
            repeat dm;
            try(repeat inj_all; auto; discriminate);
            try(repeat inj_all; assert(H1' := H1); inv H1; sis; rewrite decr_inv_S in *;
                destruct (transition a (p, d)) eqn:E0;
                apply transition_Delta in E0; subst;
                eapply IHcode in E; eauto; apply ith_suffix_cons in H1';
                rewrite decr_inv_S in *; auto; discriminate).
          - repeat inj_all. destruct (transition a (p,d)) eqn:E.
            apply transition_Delta in E. subst.
            clear IHcode. eapply mpref_memo_eq_lexy_F in H0'; eauto.
            rewrite <- H0'. clear H0' E1 E2 E3. unfold lexy. intros.
            destruct (Pointer_as_UCT.Pointer_eq_dec p stt).
            + destruct (index_eq_dec i i0).
              * subst.
                rewrite correct_Memo in H0.
                assert(z = (a :: code)).
                {
                  eapply ith_suffix_unique; eauto.
                }
                subst z. injection H0. auto.
              * rewrite correct_Memo_moot in H0; auto.
            + rewrite correct_Memo_moot in H0; auto.
          - repeat inj_all.
            assert(lexy orig m d).
            {
              clear H0' E1 E2. apply ith_suffix_cons in H1.
              destruct (transition a (p,d)) eqn:E1. apply transition_Delta in E1. subst d.
              eapply IHcode; eauto.
            }
            eapply mpref_memo_eq_lexy_F in H0'; eauto.
            clear E1 E2 E2 IHcode E E3 H M.
            unfold lexy. intros.
            destruct (Pointer_as_UCT.Pointer_eq_dec p stt).
            + destruct (index_eq_dec i i0).
              * subst.
                rewrite correct_Memo in H.
                assert(z = (a :: code)).
                {
                  eapply ith_suffix_unique; eauto.
                }
                subst z. injection H. intros. subst. auto.
              * rewrite correct_Memo_moot in H; auto.
            + rewrite correct_Memo_moot in H; auto.
        }
      Qed.



      (** [lexy_list] is preserved by [max_prefs_M] across all rules; by [mprefs__M_associates] and [lexy_closure]. *)
      Lemma lexy_list_closure :
        forall code rules Ms l0 Ms' i orig,
          lexy_list orig (zip Ms (map ssnd rules))
          -> length Ms = length rules
          -> max_prefs_M Ms code i rules = (Ms', l0)
          -> ith_suffix orig code i
          -> lexy_list orig (zip Ms' (map ssnd rules)).
      Proof.
        intros. unfold lexy_list in *. intros M' d H3.
        apply In_nth with (d := (emptyMemo, defDelta)) in H3. destruct H3 as [n]. destruct H3.
        assert(L := all_lens_const Ms rules code Ms' l0 i H0 H1). destruct L.
        assert(exists M, nth n Ms emptyMemo = M).
        { eexists; eauto. }
        destruct H7 as [M].
        assert(exists label o, nth n l0 (defLabel, None) = (label, o)).
        { destruct (nth n l0 (defLabel, None)). eexists; eauto. }
        destruct H8 as [label]. destruct H8 as [o].
        assert(exists label' ru, nth n rules (defLabel, defState) = (label', ru)).
        { destruct (nth n rules (defLabel, defState)). eexists; eauto. }
        destruct H9 as [label']. destruct H9 as [ru].
        assert(label = label').
        {
          eapply nth_labels_match; eauto. rewrite len_zip_L in H3; auto.
          rewrite length_map. lia.
        }
        rewrite H10 in *. clear H10.
        rewrite nth_zip in *.
        assert(nth n (zip Ms (map (fun x : Label * (Pointer * Delta) => snd (snd x)) rules))
                   (emptyMemo, defDelta) = (M, d)).
        {
          rewrite nth_zip.
          - inv H4. auto.
          - rewrite length_map. lia.
          - rewrite len_zip_L in H3; try lia. rewrite length_map. lia.
        }
        assert(n < length (zip Ms (map (fun x : Label * (Pointer * Delta) => snd (snd x)) rules))).
        {
          rewrite len_zip_L; [ rewrite len_zip_L in H3 | ]; try rewrite length_map; lia.
        }
        eapply mprefs__M_associates in H0; eauto.
        - destruct ru.
          assert(d = d0).
          {
            injection H4; intros.
            clear H H1 H2 H3 H4 H5 H6 H7 H8 H10 H11 H13 H0 code Ms l0.
            unfold defState.
            assert(exists x, nth n rules (x, (defPointer, defDelta)) = (label', (p, d0))).
            { eexists; eauto. }
            clear H9. destruct H as (x & H).
            assert(defDelta = ssnd (x, (defPointer, defDelta))).
            { auto. }
            rewrite H0 in H12. rewrite map_nth in H12. rewrite H in H12.
            unfold ssnd in *. sis. auto.
          }
          subst.
          assert(In (nth n Ms emptyMemo, d0)
                    (zip Ms (map (fun x : Label * (Pointer * Delta) => snd (snd x)) rules))).
          {
            eapply nth_In in H11. rewrite H10 in H11. auto.
          }
          inv H4. eapply lexy_closure; eauto.
        - rewrite len_zip_L in H3; auto. rewrite length_map. lia.
        - rewrite length_map. lia.
        - rewrite len_zip_L in H3; try lia. rewrite length_map. lia.
      Qed.

      (** [lexy_list] is preserved across a full [max_of_prefs_M] step; by [lexy_list_closure]. *)
      Lemma lexy_recursive_call_gen :
        forall code rules Ms label o Ms' i orig,
          lexy_list orig (zip Ms (map (fun x => snd (snd x)) rules))
          -> length Ms = length rules
          -> max_of_prefs_M (max_prefs_M Ms code i rules) = (Ms', label, o)
          -> ith_suffix orig code i
          -> lexy_list orig (zip Ms' (map (fun x => snd (snd x)) rules)).
      Proof.
        intros. destruct (max_prefs_M Ms code i rules) eqn:E.
        assert(l = Ms').
        {
          simpl in H1. repeat dm. injection H1; auto.
        }
        subst. clear H1.
        eapply lexy_list_closure in H; eauto.
      Qed.

      (** Specialisation of [lexy_recursive_call_gen] to the non-empty-prefix case. *)
      Lemma lexy_recursive_call :
        forall code rules Ms label s l suffix Ms' i i' orig,
          lexy_list orig (zip Ms (map (fun x => snd (snd x)) rules))
          -> length Ms = length rules
          -> max_of_prefs_M (max_prefs_M Ms code i rules)
            = (Ms', label, Some (s :: l, suffix, i'))
          -> ith_suffix orig code i
          -> ith_suffix orig suffix i'
          -> lexy_list orig (zip Ms' (map (fun x => snd (snd x)) rules)).
      Proof.
        intros. eapply lexy_recursive_call_gen in H; eauto.
      Qed.

    End LexyClosure.

    (** Lemmas propagating the [ith_suffix] invariant across recursive calls. *)
    Module Export IndexClosure.

      (** The suffix index in a memoized recursive call satisfies [ith_suffix orig]; by [mprefs_memo_F] and index arithmetic. *)
      Lemma index_rec_call__M_gen : forall code rules Ms label z suffix Ms' i i' orig,
           lexy_list orig (zip Ms (map ssnd rules))
           -> length Ms = length rules
           -> max_of_prefs_M (max_prefs_M Ms code i rules) = (Ms', label, Some (z, suffix, i'))
           -> ith_suffix orig code i
           -> ith_suffix orig suffix i'.
      Proof.
        intros.
        destruct (max_prefs_M Ms code i rules) eqn:E. eapply mprefs_memo_F in E; eauto.
        rewrite <- E in H1. unfold max_of_prefs_M in *. dm. inv H1.
        unfold ith_suffix in *. destruct H2. destruct H2.
        split.
        - apply index_rec_call_gen in E0; auto.
        - exists (x ++ z). rewrite <- app_assoc. rewrite <- H1 in *.
          apply exists_rus_of_mpref_gen in E0. destruct E0 as (r & HIn & E0).
          symmetry in E0. apply max_pref_fn_splits in E0. rewrite <- E0. auto.
      Qed.

      (** Specialisation of [index_rec_call__M_gen] to non-empty prefixes; [ith_suffix orig suffix i']. *)
      Lemma index_rec_call__M : forall code rules Ms label s l suffix Ms' i i' orig,
           lexy_list orig (zip Ms (map ssnd rules))
           -> length Ms = length rules
           -> max_of_prefs_M (max_prefs_M Ms code i rules) = (Ms', label, Some (s :: l, suffix, i'))
           -> ith_suffix orig code i
           -> ith_suffix orig suffix i'.
      Proof.

        intros.
        destruct (max_prefs_M Ms code i rules) eqn:E. eapply mprefs_memo_F in E; eauto.
        rewrite <- E in H1. unfold max_of_prefs_M in *. dm. inv H1.
        unfold ith_suffix in *. destruct H2. destruct H2.
        split.
        - apply index_rec_call in E0; auto.
        - exists (x ++ (s :: l)). rewrite <- app_assoc. rewrite <- H1 in *.
          apply exists_rus_of_mpref_gen in E0. destruct E0 as (r & HIn & E0).
          symmetry in E0. apply max_pref_fn_splits in E0. rewrite <- E0. auto.
      Defined.


    End IndexClosure.

  End TypeCheckLemmas.

  (** Top-level memoized lexer and its initialisation lemmas. *)
  Module Export Lex.

    (** Memoized lexing loop; structurally recursive on a well-foundedness proof for the suffix length. *)
    Fixpoint lex'_M
             (orig : String)
             (Ms : list Memo)
             (rules : list (sRule))
             (code : String)
             (i : index)
             (Hindex : ith_suffix orig code i)
             (Ha : Acc lt (length code))
             (Hlexy : lexy_list orig (zip Ms (map ssnd rules)))
             (Hlen : length Ms = length rules)
             {struct Ha} : (list Memo) * (list Token) * String :=
      match max_of_prefs_M (max_prefs_M Ms code i rules) as mpref'
            return max_of_prefs_M (max_prefs_M Ms code i rules) = mpref' -> _
      with
      | (Ms', _, None) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
      | (Ms', _, Some ([], _, _)) => fun _ => (Ms', [], code) (* Code cannot be processed further *)
      | (Ms', label, Some (ph :: pt, suffix, i')) =>
        fun Heq =>
          let Hindex' := (index_rec_call__M _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq Hindex) in
          match (lex'_M orig Ms' rules suffix i'
                       Hindex'
                       (acc_recursive_call__M _ _ _ _ _ _ _ _ _ _ _ Ha Hlexy Hlen Heq Hindex Hindex')
                       (lexy_recursive_call _ _ _ _ _ _ _ _ _ _ _ Hlexy Hlen Heq Hindex Hindex')
                       (len_recursive_call _ _ _ _ _ _ _ _ _ _ Hlen Heq)
                )
          with
          | (Ms'', lexemes, rest) => (Ms'', ((label, ph :: pt) :: lexemes), rest)
          end
      end eq_refl.

    (** Converts a labelled regex rule into a labelled initial DFA state. *)
    Definition init_srule (rule : Rule) : sRule :=
      match rule with
      | (label, re) => (label, init_state re)
      end.

    (** Produces an initial list of empty memos, one per rule. *)
    Definition init_Memos (srules : list sRule) : list Memo :=
      (map (fun x => emptyMemo) srules).

    (** Prepending a [lexy] entry to a [lexy_list] gives a [lexy_list]; by unfolding definitions. *)
    Lemma lexy_list_cons : forall M Ms d code,
        lexy code M d -> lexy_list code Ms -> lexy_list code ((M, d) :: Ms).
    Proof.
      intros. unfold lexy_list in *. intros. sis. destruct H1.
      - inv H1. auto.
      - apply H0; auto.
    Qed.

    (** Empty memos trivially satisfy [lexy_list] because [correct_emptyMemo] gives no hits. *)
    Lemma init_Memos_lexy : forall srules code,
        lexy_list code (zip (init_Memos srules) (map ssnd srules)).
    Proof.
      intros. induction srules.
      - simpl. unfold lexy_list. intros. contradiction.
      - simpl. apply lexy_list_cons; auto. unfold lexy. intros.
        rewrite correct_emptyMemo in H. discriminate.
    Qed.

    (** [init_Memos srules] has the same length as [srules]; by induction. *)
    Lemma init_Memos_parallel : forall srules,
        length (init_Memos srules) = length srules.
    Proof.
      intros. induction srules; auto. sis. lia.
    Qed.

    (** The full string is an [ith_suffix] of itself at [init_index (length code)]. *)
    Lemma init_index_self : forall code,
        ith_suffix code code (init_index (length code)).
    Proof.
      intros. split; auto. exists []. auto.
    Qed.

    (** Top-level memoized lexer: initialises memos and invokes [lex'_M], discarding the final memo list. *)
    Definition lex_M (rules : list Rule) (code : String) : list Token * String :=
      let
        srules := map init_srule rules
      in
      match
        lex'_M code (init_Memos srules) srules code (init_index (length code))
              (init_index_self _) (lt_wf _) (init_Memos_lexy _ _) (init_Memos_parallel _)
       with
       | (_, ts, rest) => (ts, rest)
       end.

  End Lex.

End ImplFn.
