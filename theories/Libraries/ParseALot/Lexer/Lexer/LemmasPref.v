(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.NatInt.NZOrder.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import ImplPref.

(** Lemmas about prefixes, [max_pref_fn], index invariants, rule ordering, and [re_max_pref] correctness. *)
Module LemmasFn (Import ST : State.T).

  Import ST.Defs.
  Import ST.Ty.
  (** Local alias for the prefix-implementation functor instantiated at [ST]. *)
  Module Impl := ImplPref.ImplFn ST.
  Import Impl.
  Import MatchSpec.



  (** The empty list is a prefix of every string; by [pref_def] with the string itself as witness. *)
  Lemma nil_is_prefix : forall(xs : String),
      [] ++_= xs.
  Proof.
    intros xs. apply pref_def. exists xs. reflexivity.
  Qed.

  (** [xs] is a prefix of [xs ++ ys]; by [pref_def] with [ys] as witness. *)
  Lemma app_head_prefix : forall(xs ys : String),
      xs ++_= xs ++ ys.
  Proof.
    intros xs ys. apply pref_def. exists ys. reflexivity.
  Qed.

  (** Cons-prefix equivalence: [x::xs] is a prefix of [y::ys] iff [x=y] and [xs] is a prefix of [ys]. *)
  Lemma cons_prefix : forall(x y : Sigma) (xs ys : String),
      x :: xs ++_= y :: ys <-> x = y /\ xs ++_= ys.
  Proof.
    intros x y xs ys. split; intros H.
    {
      inv H. destruct H1.
      injection H. intros I1 I2. split; subst.
      - reflexivity.
      - apply app_head_prefix.
    }
    {
      destruct H. inv H0. destruct H1.
      apply pref_def. exists x. rewrite <- H. reflexivity.
    }
  Qed.

  (** Every string is a prefix of itself; by [pref_def] with [[]]. *)
  Lemma self_prefix : forall(p : String), p ++_= p.
  Proof.
    intros p. apply pref_def. exists []. apply app_nil_r.
  Qed.

  (** Two prefixes of equal length into the same string are equal; by induction on [x]. *)
  Lemma eq_len_eq_pref : forall(x s p : String),
      length p = length s
      -> s ++_= x
      -> p ++_= x
      -> s = p.
  Proof.
    induction x; intros s p Heq Hs Hp .
    - inv Hs. inv Hp. destruct H0. destruct H1.
      apply app_eq_nil in H. destruct H.
      apply app_eq_nil in H0. destruct H0.
      subst. reflexivity.
    - destruct s; destruct p.
      + reflexivity.
      + simpl in Heq. discriminate.
      + simpl in Heq. discriminate.
      + apply cons_prefix in Hs. apply cons_prefix in Hp.
        destruct Hs. destruct Hp. subst.
        assert (length p = length s0).
        { simpl in Heq. lia. }
        apply IHx in H.
        * rewrite H. reflexivity.
        * apply H0.
        * apply H2.
  Qed.



  (** [max_pref_fn] is a splitting function: the code equals the returned prefix concatenated with the suffix; by induction on [code]. *)
  Lemma max_pref_fn_splits : forall code prefix suffix (fsm : State) i i',
      Some (prefix, suffix, i') = max_pref_fn code i fsm -> code = prefix ++ suffix.
  Proof.
    induction code as [| a s']; intros; simpl in H;
      repeat dm; repeat inj_all; auto; try(discriminate).
    symmetry in E. apply IHs' in E. rewrite E. auto.
  Qed.

  (** A non-empty prefix witness from [max_pref_fn] implies the suffix is strictly shorter than the input; by [max_pref_fn_splits] and length arithmetic. *)
  Lemma proper_suffix_shorter : forall code prefix suffix (fsm : State) i i',
      prefix <> []
      -> Some (prefix, suffix, i') = max_pref_fn code i fsm
      -> length suffix < length code.
  Proof.
    intros code prefix suffix fsm i i'. intros Hneq Heq.
    apply max_pref_fn_splits in Heq. rewrite Heq.
    replace (length (prefix ++ suffix)) with ((length prefix) + (length suffix)).
    - apply Nat.lt_add_pos_l. destruct prefix.
      + contradiction.
      + simpl. lia.
    - symmetry. apply length_app.
  Qed.

  (** The result of [max_of_prefs] on a cons list is either the head or the result for the tail; by [longer_pref] case analysis. *)
  Lemma max_first_or_rest : forall ys x y,
      x = max_of_prefs (y :: ys) -> x = y \/ x = max_of_prefs ys.
  Proof.
    intros. simpl in H. unfold longer_pref in H. repeat dm.
  Qed.

  (** [transition] commutes with [transition_list] extension by one character; by induction on [bs]. *)
  Lemma transition_list_hop : forall bs a fsm,
      transition a (transition_list bs fsm)
      = transition_list (bs ++ [a]) fsm.
  Proof.
    induction bs; intros; auto.
    - sis. rewrite transition_list_cons. repeat rewrite transition_list_nil. auto.
    - sis. rewrite transition_list_cons. rewrite IHbs. sis. rewrite transition_list_cons. auto.
  Qed.


  (** [derivative] commutes with [derivative_list] extension by one character; by induction on [bs]. *)
  Lemma deriv_list_hop : forall bs a fsm,
      derivative a (derivative_list bs fsm)
      = derivative_list (bs ++ [a]) fsm.
  Proof.
    induction bs; intros; auto.
    simpl. apply IHbs.
  Qed.


  (** [max_pref_fn] on [a::code] with [transition a fsm] corresponds to [max_pref_fn] on [code] with [fsm], with prefix extended by [a]. *)
  Lemma mpref_cons : forall code px sx fsm a i i',
      max_pref_fn code i (transition a fsm) = Some (px, sx, i')
      <-> max_pref_fn (a :: code) (incr i) fsm = Some (a :: px, sx, i').
  Proof.
    intros. simpl.
    repeat dm; split; intros;
      try( rewrite decr_inv_incr in *; rewrite E in *; repeat inj_all; auto; discriminate ).
    destruct code; sis; repeat dm; discriminate.
  Qed.


  (** The [accepting] predicate commutes with [transition] and [init_state] via the derivative; follows from the accepts/matches correspondence. *)
  Lemma accepting_dt : forall b e,
      accepting (transition b (init_state e)) =
      accepting (init_state (derivative b e)).
  Proof.
    intros. destruct (accepting (transition b (init_state e))) eqn:E.
    - rewrite accepts_nil in E. rewrite accepts_transition in E.
      symmetry in E. rewrite accepts_matches in E. apply der_match in E.
      rewrite <- accepts_matches in E. rewrite <- accepts_nil in E. auto.
    - symmetry. rewrite false_not_true in *. intros C. destruct E.
      rewrite accepts_nil. rewrite accepts_transition.
      symmetry. rewrite accepts_matches. apply der_match.
      rewrite <- accepts_matches. rewrite <- accepts_nil. auto.
  Qed.

  (** Two consecutive transitions equal [transition_list [b;a]]; by unfolding [transition_list]. *)
  Lemma dbl_trans_lst : forall a b e,
    transition a (transition b (init_state e))
    = transition_list [b; a] (init_state e).
  Proof.
    intros. repeat rewrite transition_list_cons. rewrite transition_list_nil. auto.
  Qed.

  (** Two consecutive derivatives equal [derivative_list [a0;s0]]; by reflexivity. *)
  Lemma dbl_deriv_lst : forall s0 a0 e,
      derivative s0 (derivative a0 e)
      = derivative_list [a0; s0] e.
  Proof. auto. Qed.

  (* ow *)
  (** [max_pref_fn] is invariant under replacing [transition]/[transition_list] applied to [init_state e] with [init_state (derivative/derivative_list)]; by mutual induction on [code] and [bs]. *)
  Lemma mpref_dt_list : forall code bs e a i,
      max_pref_fn code i (transition a (init_state e))
      = max_pref_fn code i (init_state (derivative a e))
      /\
      max_pref_fn code i (transition_list bs (init_state e)) =
      max_pref_fn code i (init_state (derivative_list bs e)).
  Proof.
    induction code; induction bs; intros.
    - split; auto; simpl; repeat dm.
      + rewrite accepting_dt in *. rewrite E in E0. discriminate.
      + rewrite accepting_dt in *. rewrite E in E0. discriminate.
      + rewrite transition_list_nil in *. rewrite E in E0. discriminate.
      + rewrite transition_list_nil in *. rewrite E in E0. discriminate.
    - split.
      + simpl. repeat dm.
        * rewrite accepting_dt in *. rewrite E in E0. discriminate.
        * rewrite accepting_dt in *. rewrite E in E0. discriminate.
      + simpl. repeat dm.
        * rewrite transition_list_cons in E.
          rewrite <- derivative_list_cons in *.
          rewrite <- accepting_dt_list in *. rewrite transition_list_cons in *.
          rewrite E in *. discriminate.
        * rewrite transition_list_cons in E.
          rewrite <- derivative_list_cons in *.
          rewrite <- accepting_dt_list in *. rewrite transition_list_cons in *.
          rewrite E in *. discriminate.
    - assert(IHcode0 : forall (e : regex) (a : Sigma) i,
           max_pref_fn code i (transition a (init_state e)) =
           max_pref_fn code i (init_state (derivative a e))).
      { intros. specialize (IHcode []). apply IHcode. }
      assert(IHcode1 : forall (bs : list Sigma) (e : regex) i,
           max_pref_fn code i (transition_list bs (init_state e)) =
           max_pref_fn code i (init_state (derivative_list bs e))).
      { intros. specialize (IHcode bs e0 a). apply IHcode. }
      clear IHcode.
      split.
      + destruct (max_pref_fn (a :: code) i (transition a0 (init_state e))) eqn:E.
        * destruct p. symmetry.
          destruct p.
          simpl in *.
          repeat dm; try(discriminate); repeat inj_all;
            try( rewrite IHcode0 in *;
                 rewrite dbl_trans_lst in *;
                 rewrite dbl_deriv_lst in *;
                 rewrite IHcode1 in *);
                 try(rewrite E3 in *; repeat inj_all; auto; discriminate);
                 try(rewrite E0 in *; repeat inj_all; auto; discriminate);
                 try(rewrite accepting_dt in *; rewrite accepting_dt_list in *; sis; auto);
                 try(rewrite E1 in *; discriminate).
                 rewrite E2 in *. discriminate.
        * simpl in *. repeat dm; try(discriminate).
          -- clear E. rewrite IHcode0 in E3.
             rewrite dbl_trans_lst in E0.
             rewrite dbl_deriv_lst in E3.
             rewrite IHcode1 in *. rewrite E3 in *. discriminate.
          -- rewrite accepting_dt in E4.
             rewrite dbl_trans_lst in *.
             rewrite dbl_deriv_lst in *.
             rewrite accepting_dt_list in *.
             rewrite E4 in *. discriminate.
          -- rewrite accepting_dt in *. rewrite E5 in *. discriminate.
      + rewrite transition_list_nil. unfold derivative_list. auto.
    - assert(IHcode0 : forall (e : regex) (a : Sigma) i,
           max_pref_fn code i (transition a (init_state e)) =
           max_pref_fn code i (init_state (derivative a e))).
      { intros. specialize (IHcode []). apply IHcode. }
      assert(IHcode1 : forall (bs : list Sigma) (e : regex) i,
           max_pref_fn code i (transition_list bs (init_state e)) =
           max_pref_fn code i (init_state (derivative_list bs e))).
      { intros. specialize (IHcode bs0 e0 a). apply IHcode. }
      clear IHcode.
      assert(IHbs0 : forall (e : regex) (a0 : Sigma) i,
         max_pref_fn (a :: code) i (transition a0 (init_state e)) =
         max_pref_fn (a :: code) i (init_state (derivative a0 e))).
      { intros. apply IHbs. }
      assert(IHbs1 : forall (e : regex) (a0 : Sigma) i,
         max_pref_fn (a :: code) i (transition_list bs (init_state e)) =
         max_pref_fn (a :: code) i (init_state (derivative_list bs e))).
      { intros. apply IHbs. apply a. }
      clear IHbs.
      split.
      + auto.
      + destruct (max_pref_fn (a :: code) i (transition_list (a0 :: bs) (init_state e))) eqn:E.
        * destruct p. destruct p.
          simpl in E. simpl. repeat dm; try(discriminate);
          try(rewrite IHcode0 in *;
             rewrite transition_list_cons in *;
             rewrite <- derivative_list_cons in *;
             rewrite transition_list_hop in *;
             rewrite deriv_list_hop in *;
             rewrite <- IHcode1 in *; rewrite <- transition_list_cons in *; sis;
             rewrite E3 in *; repeat inj_all; auto; discriminate);
            try(rewrite IHcode0 in *; rewrite <- derivative_list_cons in *;
             rewrite deriv_list_hop in *; rewrite <- IHcode1 in *;
             rewrite transition_list_hop in *; rewrite E0 in *; discriminate);
          try(rewrite accepting_dt in *; rewrite <- derivative_list_cons in *;
             rewrite deriv_list_hop in *; rewrite <- accepting_dt_list in *;
             rewrite transition_list_hop in *; rewrite E1 in *; discriminate).
          rewrite accepting_dt_list in *. sis. rewrite E2 in *. discriminate.
        * simpl in E. simpl. repeat dm; try(discriminate).
          -- rewrite IHcode0 in E3.
             rewrite transition_list_hop in *.
             rewrite deriv_list_hop in *.
             subst. inv E. rewrite IHcode1 in *. sis. rewrite E0 in *. inv E3.
          -- rewrite accepting_dt in *. rewrite transition_list_hop in *.
             rewrite accepting_dt_list in *. rewrite <- app_comm_cons in *.
             rewrite deriv_list_hop in *. sis. rewrite E1 in *. discriminate.
          -- rewrite accepting_dt in *. rewrite transition_list_hop in *.
             rewrite accepting_dt_list in *. rewrite <- app_comm_cons in *.
             rewrite deriv_list_hop in *. sis. rewrite E2 in *. discriminate.
  Qed.


  (** Single-character specialisation of [mpref_dt_list]: [transition a] on [init_state e] equals [init_state (derivative a e)]. *)
  Lemma mpref_dt : forall code a e i,
      max_pref_fn code i (transition a (init_state e))
      = max_pref_fn code i (init_state (derivative a e)).
  Proof.
    assert(L := mpref_dt_list).
    intros. specialize(L code [] e a i). destruct L. auto.
  Qed.

  (** [init_index (length (a::code))] equals [incr (init_index (length code))]; by [incr_is_S]. *)
  Lemma index_incr_cons : forall (code : String) a,
      init_index (length (a :: code)) = incr (init_index (length code)).
  Proof.
    intros. sis. apply incr_is_S.
  Qed.

  (** If [max_pref_fn] returns [Some (p, x, i)] then [p] is matched by [e]; by induction on [code] using [der_match] and [accepts_matches]. *)
  Lemma max_pref_matches : forall(code p x : String) (e : regex) i,
      Some (p, x, i) = max_pref_fn code (init_index (length code)) (init_state e)
      -> exp_match p e.
  Proof.
    induction code; intros.
    - simpl in H. dm; try(discriminate).
      injection H; intros; subst.
      rewrite accepts_nil in E. symmetry in E. rewrite accepts_matches in E. auto.
    - symmetry in H. destruct p.
      + simpl in H. repeat dm.
        * destruct p. injection H; intros; discriminate.
        * injection H; intros; discriminate.
        * rewrite accepts_nil in E1. symmetry in E1. rewrite accepts_matches in E1. auto.
        * discriminate.
      + destruct (Sigma_dec a s).
        * subst. rewrite index_incr_cons in *. apply mpref_cons in H.
          symmetry in H. rewrite mpref_dt in H. apply IHcode in H.
          apply der_match. auto.
        * symmetry in H. apply max_pref_fn_splits in H. injection H. intros. contradiction.
  Qed.


  (** [re_no_max_pref code e] iff [max_pref_fn] returns [None]; by induction on [code] using [accepts_matches] and [der_match]. *)
   Theorem re_max_pref_correct__None : forall(code : String) (e : regex),
      re_no_max_pref code e
      <-> None = max_pref_fn code (init_index (length code)) (init_state e).
   Proof.

     induction code.
     {
       split; intros.
       - simpl. inv H. dm. specialize (H1 []). destruct H1.
         + apply self_prefix.
         + rewrite accepts_nil in E. symmetry in E. rewrite accepts_matches in E. auto.
       - simpl in H. dm; try(discriminate).
         + apply re_MP0. intros. intros C. apply false_not_true in E.
           destruct E.
           symmetry. rewrite accepts_nil. apply accepts_matches.
           destruct cand; auto.
           inv H0. destruct H1. discriminate.
     }
     {
       split; intros.
       - simpl. repeat dm.
         + rewrite mpref_cons in E.
           symmetry in E.
           assert(E2 := E).
           apply max_pref_fn_splits in E. injection E. intros. clear E.
           rewrite incr_inv_decr in *. apply max_pref_matches in E2.
           inv H. specialize (H1 (a :: p1)). destruct H1; auto.
           apply pref_def. exists s. auto.
         + clear H. symmetry in E. rewrite mpref_dt in E.
           rewrite decr_inv_S in *. apply IHcode in E.
           inv E. specialize (H1 []). destruct H1. apply nil_is_prefix.
           rewrite accepts_nil in E0. rewrite accepts_transition in E0.
           symmetry in E0. apply accepts_matches in E0. apply der_match. auto.
         + symmetry in E. rewrite mpref_dt in E.
           rewrite decr_inv_S in *. apply IHcode in E.
           inv E. specialize (H1 []). destruct H1. apply nil_is_prefix.
           inv H. specialize (H1 []). destruct H1.
           * apply nil_is_prefix.
           * rewrite accepts_nil in E1. symmetry in E1. apply accepts_matches in E1.
             auto.
       - simpl in H. repeat dm; try(discriminate).
         clear H. rewrite mpref_dt in E. symmetry in E.
         rewrite decr_inv_S in *. apply IHcode in E.
         inv E. apply re_MP0. intros. intros C. inv H. destruct H0.
         destruct cand.
         + rewrite false_not_true in E1. destruct E1.
           rewrite accepts_nil. symmetry. rewrite accepts_matches. auto.
         + injection H. intros. rewrite H2 in *. clear H H2.
           specialize (H1 cand). destruct H1.
           * apply pref_def. eexists. eauto.
           * apply der_match. auto.
     }
   Qed.

   (** The index component of a [max_pref_fn] result equals [init_index (length q)] for any FSM state; by induction on [code]. *)
   Theorem index_closure_gen : forall code p q qi r,
       Some (p, q, qi)
       = max_pref_fn code (init_index (length code)) r
       ->  qi = (init_index (length q)).
   Proof.
     induction code; intros.
     - sis. repeat dm.
       + repeat inj_all. sis. auto.
       + discriminate.
     - sis. repeat dm.
       + rewrite decr_inv_S in *. symmetry in E. apply IHcode in E.
         repeat inj_all. auto.
       + repeat inj_all. apply decr_inv_S.
       + repeat inj_all. sis. auto.
       + discriminate.
   Qed.

   (** Specialisation of [index_closure_gen] to [init_state e]; the index tracks the suffix length throughout the computation. *)
   Theorem index_closure : forall code p q qi e,
       Some (p, q, qi)
       = max_pref_fn code (init_index (length code)) (init_state e)
       ->  qi = (init_index (length q)).
   Proof.
     induction code; intros.
     - sis. repeat dm.
       + repeat inj_all. sis. auto.
       + discriminate.
     - sis. repeat dm.
       + rewrite decr_inv_S in *. symmetry in E. rewrite mpref_dt in *. apply IHcode in E.
         repeat inj_all. auto.
       + repeat inj_all. apply decr_inv_S.
       + repeat inj_all. sis. auto.
       + discriminate.
   Qed.

  (** [re_max_pref code e p] iff [max_pref_fn] returns [Some (p, q, init_index (length q))] for some [q]; by induction on [code] using the derivative correspondence. *)
  Theorem re_max_pref_correct__Some : forall(code p : String) (e : regex),
      re_max_pref code e p
      <-> exists(q : String), Some (p, q, (init_index (length q)))
                       = max_pref_fn code (init_index (length code)) (init_state e).
  Proof.
    induction code.
    {
      intros p e. split; intros H.
      - exists []. simpl. assert (A0 : p = []).
        {
          inv H. inv H1. destruct H0. destruct x.
          - rewrite app_nil_r in H. apply H.
          - destruct p.
            + reflexivity.
            + discriminate.
        }
        dm.
        + rewrite A0. reflexivity.
        + inv H. rewrite accepts_nil in E. apply accepts_matches in H2.
          rewrite E in H2. discriminate.
      - destruct H. apply re_MP1.
        + apply max_pref_fn_splits in H. symmetry in H.
          apply pref_def. exists x. apply H.
        + apply max_pref_matches in H. apply H.
        + intros cand H0. inv H0. destruct H1.
          assert (A0 : cand = []).
          {
            destruct cand.
            - reflexivity.
            - discriminate.
          }
          assert (A1 : p = []).
          {
            simpl in H. dm.
            - injection H. intros. auto.
            - discriminate.
          }
          rewrite A0. rewrite A1. left. lia.
    }
    {
      intros p e. split; intros H.
      - destruct p.
        + exists (a :: code). inv H. simpl.
          dm.
          * destruct p. destruct p. symmetry in E.
            rewrite mpref_dt in E.
            rewrite decr_inv_S in *.
            assert( i = init_index (length s)).
            { eapply index_closure in E. auto. }
            rewrite H in *. clear H.
            assert (Ae : exists q, Some (p, q, init_index (length q))
                              = max_pref_fn code (init_index (length code))
                                            (init_state (derivative a e))).
            { exists s. apply E. }
            apply IHcode in Ae. inv Ae.
            assert (Ap : a :: p ++_= a :: code).
            { apply cons_prefix. split. reflexivity. apply H0. }
            apply H3 in Ap. destruct Ap.
            -- simpl in H. lia.
            -- exfalso. destruct H. apply der_match. auto.
          * assert (A0 : accepting (transition a (init_state e)) = false).
            {
              destruct code.
              - simpl in E. dm.
                + discriminate.
              - simpl in E. dm.
                + destruct p. dm. discriminate.
                + dm.
                  * discriminate.
                  * dm.
                    -- discriminate.
            }
            rewrite A0. apply accepts_matches in H2. rewrite <- accepts_nil in H2.
            rewrite <- H2. reflexivity.
        + inv H. inv H1. destruct H0. injection H.
          intros I1 I2. clear H. exists x. subst s.
          assert (Ap : p ++_= code).
          { apply pref_def. exists x. apply I1. }
          simpl. dm; symmetry in E.
          * destruct p0. destruct p0.
            rewrite decr_inv_S in *.
            assert(i = init_index (length s)). symmetry in E. rewrite mpref_cons in E.
            { symmetry in E. erewrite <- index_incr_cons in *. apply index_closure in E. auto. }
            rewrite H in *. clear H.
            assert (Ae : exists q, Some (p0, q, init_index (length q))
                              = max_pref_fn code (init_index (length code))
                                           (init_state (derivative a e))).
            { exists s. symmetry in E. rewrite mpref_dt in E. auto. }
            apply IHcode in Ae. inv Ae. inv H1. destruct H5. apply max_pref_fn_splits in E.
            (* Want to show p = p0 *)
            assert (A0 : p ++_= p ++ x).
            { apply pref_def. exists x. reflexivity. }
            assert (A1 : a :: p0 ++_= a :: p ++ x).
            { apply pref_def. exists x0. rewrite <- H. reflexivity. }
            apply H3 in A1. apply H4 in A0.
            (* should follow that p and p0 are prefixes of the same length and thus equal *)
            assert (A0' : length p <= length p0).
            {
              destruct A0.
              - apply H1.
              - exfalso. destruct H1. apply der_match. auto.
            }
            assert (A1' : length p0 <= length p).
            {
              destruct A1.
              - simpl in H1. lia.
              - exfalso. destruct H1. apply der_match; auto.
            }
            assert (A : length p = length p0).
            { lia. }
            assert (As : p0 ++_= p ++ x).
            { apply pref_def. exists x0. apply H. }
            apply eq_len_eq_pref with (x := p ++ x) in A.
            -- rewrite A. rewrite A in E. apply app_inv_head in E. rewrite E. reflexivity.
            -- apply As.
            -- apply Ap.
          * rewrite mpref_dt in E. rewrite decr_inv_S in *.
            apply re_max_pref_correct__None in E. inv E.
            assert (A0 : p = []).
            {
              assert (A1 : p ++_= p ++ x).
              { apply pref_def. exists x. reflexivity. }
              apply H1 in A1. destruct A1. apply der_match. auto.
            }
            assert (A1 : accepting (transition a (init_state e)) = true).
            {
              rewrite A0 in H2. symmetry. rewrite accepts_nil. rewrite accepts_transition.
              apply accepts_matches. auto.
            }
            rewrite A1. rewrite A0. reflexivity.
      - destruct H. apply re_MP1.
        + apply max_pref_fn_splits in H. apply pref_def. exists x. symmetry. apply H.
        + apply max_pref_matches in H. apply H.
        + intros cand Hpref. destruct p.
          * simpl in H.
            dm.
            -- destruct p. destruct p. discriminate.
            -- dm.
               ++ discriminate.
               ++ dm.
                  ** symmetry in E. rewrite mpref_dt in E. rewrite decr_inv_S in *.
                     apply re_max_pref_correct__None in E. inv E. destruct cand.
                     { left. lia. }
                     {
                       right. inv Hpref. destruct H0. injection H0. intros I1 I2.
                       intros C. assert (A : cand ++_= code).
                       { apply pref_def. exists x0. apply I1. }

                       apply H1 in A. destruct A. subst.
                       apply der_match; auto.
                     }
                  ** discriminate.
          * simpl in H.
            dmh; symmetry in E.
            -- destruct p0. destruct p0. injection H. intros I1 I2 I3 I4.
               rewrite decr_inv_S in *. rewrite mpref_dt in E.
               assert(i = init_index (length s0)).
               { repeat inj_all. auto. }
               rewrite H0 in *. clear H0.
               assert (Ae : exists q, Some (p0, q, init_index (length q))
                                 = max_pref_fn code (init_index (length code))
                                               (init_state (derivative a e))).
               { exists s0. apply E. }
               apply IHcode in Ae. inv Ae. destruct cand.
               ++ left. simpl. lia.
               ++ inv Hpref. destruct H0. injection H0. intros. subst s.
                  assert (Apref : cand ++_= code).
                  { apply pref_def. exists x. auto. }
                  apply H3 in Apref. destruct Apref.
                  ** left. simpl. lia.
                  ** right. intros C. destruct H5. apply der_match. auto.
            -- rewrite mpref_dt in E. rewrite decr_inv_S in *.
               apply re_max_pref_correct__None in E. inv E.
               assert (A0 : accepting (transition a (init_state e)) = true).
               {
                 repeat dm;
                   try(reflexivity); try(discriminate).
               }
               assert (A1 : [] ++_= code).
               { apply nil_is_prefix. }
               apply H1 in A1. destruct A1. apply accepts_matches. rewrite <- accepts_nil.
               symmetry. rewrite accepts_nil in *. rewrite accepts_transition in A0.
               symmetry in A0. symmetry.
               rewrite accepts_matches in *.
               apply der_match. apply A0.
    }
  Qed.


  (** If [re_max_pref] holds then [re_no_max_pref] does not; by unfolding both and applying the maximality witness. *)
  Lemma pref_not_no_pref : forall code p r,
      re_max_pref code r p
      -> ~(re_no_max_pref code r).
  Proof.
    intros code p r H C. inv H. inv C.
    apply H0 in H1. contradiction.
  Qed.

  (** [max_pref_fn] always returns either [Some] (with a well-formed index) or [None]; by case analysis and [index_closure]. *)
  Lemma max_pref_fn_Some_or_None : forall code e,
      (exists p q, Some (p, q, init_index (length q))
      = max_pref_fn code (init_index (length code)) (init_state e))
      \/ None = max_pref_fn code (init_index (length code)) (init_state e).
  Proof.
    intros code e.
    destruct (max_pref_fn code (init_index (length code)) (init_state e)) eqn:E.
    - left. destruct p. destruct p. exists p. exists s. symmetry in E. apply index_closure in E.
      subst. reflexivity.
    - right. reflexivity.
  Qed.


  (** Every regex either has a max-prefix or has no max-prefix; by [max_pref_fn_Some_or_None] and the correctness theorems. *)
  Lemma re_pref_or_no_pref : forall code r,
      (exists p, re_max_pref code r p) \/ re_no_max_pref code r.
  Proof.
    intros code r.
    assert(L := max_pref_fn_Some_or_None).
    specialize (L code). specialize (L r). destruct L.
    - left. destruct H as [p]. apply re_max_pref_correct__Some in H.
      eexists; eauto.
    - right. apply re_max_pref_correct__None in H. auto.
  Qed.

  (** Any element of a list can be surrounded by two sublists; by induction on [xs]. *)
  Lemma part_around_in : forall (T : Type) (xs : list T) (x : T),
      In x xs -> exists xs1 xs2, xs = xs1 ++ (x :: xs2).
  Proof.
    intros T. induction xs; intros x Hin. contradiction.
    simpl in Hin. destruct Hin.
    - exists []. exists xs. rewrite H. reflexivity.
    - apply IHxs in H. destruct H as (xs1 & xs2 & H).
      rewrite H. exists (a :: xs1). exists xs2. reflexivity.
  Qed.

  (** [at_index ru n rus] characterises list membership; equivalence proved by induction on [rus]. *)
  Lemma at_index_In : forall rus ru,
      (exists n, at_index ru n rus) <-> In ru rus.
  Proof.
    induction rus; intros ru; split; intros H.
    - inv H. inv H0.
    - contradiction.
    - inv H.
      simpl. destruct x.
      + inv H0. left. reflexivity.
      + inv H0. right. apply IHrus. exists x. apply IH.
    - simpl in H. destruct H.
      + exists 0. apply AI0. auto.
      + apply IHrus in H. inv H. exists (S x).
        apply AI1. apply H0.
  Qed.

  (** [In ru rus] iff [ru] has a least index in [rus]; proved by induction on [rus] using [ru_dec]. *)
  Lemma In_least_index : forall rus ru,
      In ru rus <-> (exists n, least_index ru n rus).
  Proof.
    intros rus ru. split.
    {
      generalize dependent ru. induction rus; intros ru H. contradiction.
      destruct (ru_dec a ru).
      {
        subst. exists 0. apply LI1.
        - apply AI0. auto.
        - intros n' Hlt. lia.
      }
      {
        destruct H.
        - contradiction.
        - apply IHrus in H. destruct H. exists (S x). inv H. apply LI1.
          + apply AI1. apply Hat.
          + intros n' Hlt. intros C. destruct n'.
            * inv C. contradiction.
            * assert(Hlt' : n' < x). lia.
              apply Hnot in Hlt'. inv C. contradiction.
      }
    }
    {
      generalize dependent ru. induction rus; intros ru H.
      - inv H. inv H0. inv Hat.
      - destruct (ru_dec a ru); subst.
        + simpl. auto.
        + inv H. destruct x.
          * inv H0. inv Hat. contradiction.
          * simpl. right. apply IHrus. exists x. inv H0. apply LI1.
            -- inv Hat. apply IH.
            -- intros n' Hlt. specialize (Hnot (S n')).
               assert(A : S n' < S x). lia.
               apply Hnot in A. intros C. destruct A.
               apply AI1. apply C.
    }
  Qed.

  (** The element at position [length rus1] in [rus1 ++ ru :: rus2] is [ru]; by induction on [rus1]. *)
  Lemma at_index_num_prev : forall rus1 ru rus2,
      at_index ru (length rus1) (rus1 ++ ru :: rus2).
  Proof.
    induction rus1; intros ru rus2.
    - simpl. apply AI0. reflexivity.
    - simpl. apply AI1. apply IHrus1.
  Qed.

  (** A least-index witness can be decomposed into a prefix, the element, and a suffix; by induction on [rus]. *)
  Lemma part_around_least_index : forall rus n ru,
      least_index ru n rus -> (exists rus1 rus2,
                                 rus = rus1 ++ (ru :: rus2)
                                 /\ length rus1 = n
                                 /\ ~(In ru rus1)).
  Proof.
    induction rus; intros n ru H.
    {
      inv H. inv Hat.
    }
    {
      inv H. inv Hat.
      - exists []. exists rus. split; [| split]; try(auto).
      - assert(least_index ru n0 rus).
        {
          apply LI1.
          - apply IH.
          - intros n' H C.
            assert(A0 : S n' < S n0).
            { lia. }
            apply Hnot in A0. destruct A0.
            apply AI1. apply C.
        }
        apply IHrus in H.
        destruct H as (rus1 & rus2 & IH').
        destruct IH' as (Heq & Hlen & Hnin).
        exists (a :: rus1). exists rus2. split; [| split].
        + rewrite Heq. reflexivity.
        + simpl. lia.
        + intros C. destruct Hnin. simpl in C. destruct C.
          * specialize (Hnot 0). rewrite H in Hnot. destruct Hnot.
            -- lia.
            -- apply AI0. reflexivity.
          * apply H.
    }
  Qed.

  (* Ah so this is what proof automation can do... *)
  (** [longer_pref] is associative; by exhaustive case analysis via decision procedures. *)
  Lemma lgr_pref_assoc : forall a b c,
      longer_pref (longer_pref a b) c = longer_pref a (longer_pref b c).
  Proof.
    intros a b c. unfold longer_pref.
    repeat dm; repeat inj_all; subst; repeat eqb_eq_all; repeat ltb_lt_all;
      try(discriminate);
      try(lia);
      try(auto).
  Qed.

  (** [max_of_prefs] on a non-empty rule list with empty code never returns a non-empty prefix; by induction on [rs]. *)
  Lemma all_mprefs_nil : forall label p ps suffix i i' rs r,
      max_of_prefs (max_prefs [] i (r :: rs)) <> (label, Some (p :: ps, suffix, i')).
  Proof.
    intros label p ps suffix. induction rs; intros.
    - intro C. simpl in *. unfold extract_fsm_for_max in *. unfold longer_pref in *. simpl.
      repeat dm; repeat inj_all; dm; try(discriminate).
    - specialize (IHrs a). intros C. destruct IHrs.
      simpl in *. unfold extract_fsm_for_max in *. unfold longer_pref in *. simpl.
      repeat dm;
        repeat inj_all; subst; repeat ltb_lt_all; repeat eqb_eq_all;
          subst; simpl in *; try(lia); repeat dm; try(discriminate).
  Qed.

  (** [max_of_prefs] distributes over list concatenation via [longer_pref]; by induction on [ps1]. *)
  Lemma mpref_app_dist : forall ps1 ps2,
      max_of_prefs (ps1 ++ ps2) = longer_pref (max_of_prefs ps1) (max_of_prefs ps2).
  Proof.
    induction ps1; intros ps2.
    - simpl. destruct (max_of_prefs ps2). reflexivity.
    - simpl. rewrite IHps1. symmetry. apply lgr_pref_assoc.
  Qed.

  (** [max_of_prefs (p::ps)] equals [longer_pref p (max_of_prefs ps)]; by [simpl]. *)
  Lemma mpref_cons_longer : forall ps p,
      max_of_prefs (p :: ps) = longer_pref p (max_of_prefs ps).
  Proof.
    intros ps p. simpl. reflexivity.
  Qed.

  (** If [max_of_prefs] returns a [Some] result then some rule in the list achieves it; by induction on [rus] and [max_first_or_rest]. *)
  Lemma exists_rus_of_mpref_gen : forall rus code l px suffix i,
      max_of_prefs (max_prefs code (init_index (length code)) rus)
      = (l, Some (px, suffix, i))
      -> (exists r, In (l, r) rus
              /\ max_pref_fn code (init_index (length code)) r
                = Some (px, suffix, i)).
  Proof.
    induction rus; intros.
    {
      simpl in H. discriminate.
    }
    {
      unfold max_prefs in H.
      repeat first [rewrite map_cons in H | rewrite map_app in H].
      symmetry in H. apply max_first_or_rest in H. destruct H.
      - destruct a. simpl in H. injection H; intros; subst.
        exists s. split.
        * left. auto.
        * auto.
      - symmetry in H. apply IHrus in H. destruct H as [r]. destruct H.
        exists r. split.
        + right. apply H.
        + apply H0.
    }
  Qed.

  (** Specialisation of [exists_rus_of_mpref_gen] to rules initialised via [init_srule]. *)
  Lemma exists_rus_of_mpref : forall rus code l px suffix i,
      max_of_prefs (max_prefs code (init_index (length code)) (map init_srule rus))
      = (l, Some (px, suffix, i))
      -> (exists r, In (l, r) rus
              /\ max_pref_fn code (init_index (length code)) (init_state r)
                                  = Some (px, suffix, i)).
  Proof.
    induction rus; intros.
    {
      simpl in H. discriminate.
    }
    {
      unfold max_prefs in H.
      repeat first [rewrite map_cons in H | rewrite map_app in H].
      symmetry in H. apply max_first_or_rest in H. destruct H.
      - destruct a. simpl in H. injection H; intros; subst.
        exists r. split.
        * left. auto.
        * auto.
      - symmetry in H. apply IHrus in H. destruct H as [r]. destruct H.
        exists r. split.
        + right. apply H.
        + apply H0.
    }
  Qed.

  (** If the overall maximum prefix is empty then each individual rule has either an empty or no max-prefix; by [re_pref_or_no_pref] and [max_pref_longer]. *)
  Lemma nil_mpref_nil_or_no_pref : forall rus code s l l1 r,
      max_of_prefs (max_prefs code (init_index (length code)) (map init_srule rus))
                    = (l1, Some ([], s, init_index (length s)))
      -> In (l, r) rus
      -> re_max_pref code r [] \/ re_no_max_pref code r.
  Proof.
    intros rus code s l l1 r Hmax Hin. assert(L := re_pref_or_no_pref code r).
    destruct L.
    - destruct H. destruct x.
      + left. apply H.
      (* This was a fun one *)
      + exfalso.
        apply re_max_pref_correct__Some in H. destruct H as [q]. symmetry in H.
        assert(L := (part_around_in _ rus (l, r)) Hin).
        destruct L as (rus1 & rus2 & L). subst rus. clear Hin.
        rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
        unfold max_prefs in Hmax. rewrite map_app in Hmax. rewrite map_cons in Hmax.
        simpl in Hmax.
        rewrite H in Hmax. rewrite mpref_app_dist in Hmax. rewrite mpref_cons_longer in Hmax.
        simpl in Hmax. unfold longer_pref in Hmax.
        (* 32 subgoals, 7 subproofs ! *)
        repeat dmh; subst;
          try (repeat inj_all; discriminate).
        * repeat inj_all. rewrite Nat.eqb_eq in *. sis. lia.
        * repeat inj_all. rewrite false_not_true in *. destruct E8.
          rewrite Nat.ltb_lt. sis. lia.

    - right. apply H.
  Qed.

  (** If [max_of_prefs] returns [None] then every rule in the list has no max-prefix; by [re_pref_or_no_pref] and contradiction. *)
  Lemma no_mpref_no_pref : forall rus code l l1 r,
      max_of_prefs (max_prefs code (init_index (length code)) (map init_srule rus))
      = (l1, None)
      -> In (l, r) rus
      -> re_no_max_pref code r.
  Proof.
    intros rus code l l1 r Hmax Hin. assert(L := re_pref_or_no_pref code r).
    destruct L.
    - exfalso. destruct H.
      (*apply invert_init_correct_max in H.*)
      apply re_max_pref_correct__Some in H. destruct H as [q]. symmetry in H.
      assert(L := (part_around_in _ rus (l, r)) Hin).
      destruct L as (rus1 & rus2 & L). subst rus. clear Hin.
      rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
      unfold max_prefs in Hmax. rewrite map_app in Hmax. rewrite map_cons in Hmax. simpl in Hmax.
      rewrite H in Hmax. rewrite mpref_app_dist in Hmax. rewrite mpref_cons_longer in Hmax.
      simpl in Hmax. unfold longer_pref in Hmax.
      repeat dmh; repeat inj_all; subst;
        try(discriminate);
        try(rewrite Hmax in E1; discriminate).
    - apply H.
  Qed.

  (** The index carried in [max_of_prefs] result equals [init_index (length suf)]; by [exists_rus_of_mpref] and [index_closure]. *)
  Lemma index_closure_mprefs : forall code rus l0 px suf x,
    max_of_prefs (max_prefs code (init_index (length code)) (map init_srule rus))
    = (l0, Some (px, suf, x))
    -> x = init_index (length suf).
  Proof.
    intros. apply exists_rus_of_mpref in H. destruct H. destruct H.
    eapply index_closure; eauto.
  Qed.



  (** Two elements at the same index in the same list are equal; by induction on [n]. *)
  Lemma eq_index_eq_ru : forall n rus ru1 ru2,
      at_index ru1 n rus
      -> at_index ru2 n rus
      -> ru1 = ru2.
  Proof.
    induction n; intros.
    - inv H. inv H0. auto.
    - inv H. inv H0. eapply IHn; eauto.
  Qed.

  (** Two elements with the same least index in the same list are equal; by [eq_index_eq_ru]. *)
  Lemma eq_LI_eq_ru : forall n rus ru1 ru2,
      least_index ru1 n rus
      -> least_index ru2 n rus
      -> ru1 = ru2.
  Proof.
    intros. inv H. inv H0. eapply eq_index_eq_ru; eauto.
  Qed.

  (** The least index of a rule in a list is unique; by trichotomy and the minimality condition. *)
  Lemma least_index_unique : forall rus ru n1 n2,
      least_index ru n1 rus
      -> least_index ru n2 rus
      -> n1 = n2.
  Proof.
    intros. inv H. inv H0.
    destruct (Nat.lt_trichotomy n1 n2); [| destruct H].
    - apply Hnot0 in H. contradiction.
    - auto.
    - apply Hnot in H. contradiction.
  Qed.

  (** Any two elements of [rus] are either equal or one is earlier than the other; by [In_least_index] and trichotomy. *)
  Lemma earlier_rule_split : forall rus ru1 ru2,
      In ru1 rus
      -> In ru2 rus
      -> ru1 = ru2 \/
        earlier_rule ru1 ru2 rus \/
        earlier_rule ru2 ru1 rus.
  Proof.
    intros.
    apply In_least_index in H. destruct H as [n1].
    apply In_least_index in H0. destruct H0 as [n2].
    assert(L := Nat.lt_trichotomy n1 n2). destruct L as [| L]; [|destruct L].
    - right. left. apply ERu1. intros.
      apply least_index_unique with (n1 := n0) in H; auto; subst.
      apply least_index_unique with (n1 := n3) in H0; auto; subst.
      auto.
    - left. subst. apply eq_LI_eq_ru with (ru1 := ru1) in H0; auto.
    - right. right. apply ERu1. intros.
      apply least_index_unique with (n1 := n3) in H; auto; subst.
      apply least_index_unique with (n1 := n0) in H0; auto; subst.
      auto.
  Qed.

  (** [n > m] is equivalent to [m < n]; by [lia]. *)
  Lemma flip_gt : forall n m,
      n > m <-> m < n.
  Proof.
    intros. lia.
  Qed.

  (** The first token is unique: any two [first_token] witnesses for the same code and rules yield the same token; by [eq_len_eq_pref] and [earlier_rule_split]. *)
  Lemma first_token_unique : forall t t' code rus,
      first_token code rus t
      -> first_token code rus t'
      -> t = t'.
  Proof.
    intros. inv H; inv H0.
    (* show p and p0 are prefixes of equal length and thus equal *)
    assert(Alen : length p = length p0).
    {
      destruct (Nat.lt_trichotomy (length p) (length p0)); [|destruct H].
      - apply flip_gt in H. eapply Hout in H; destruct H; eauto.
      - auto.
      - apply flip_gt in H. apply Hout0 with (l' := l) (r' := r) in H; destruct H; auto.
    }
    assert(Aeq : p = p0).
    {
      inv Hmpref. inv Hmpref0.
      eapply eq_len_eq_pref in Alen; eauto.
    }
    subst.
    (* show neither rule can be earlier than the other and thus they are equal *)
    specialize (Hlater r0 l0).
    specialize (Hlater0 r l).
    clear Hout Hout0 Hnempt Hnempt0.
    assert(L := earlier_rule_split rus (l,r) (l0,r0) Hex Hex0). destruct L; [| destruct H].
    - inv H. auto.
    - apply Hlater0 in H; auto. contradiction.
    - apply Hlater in H; auto. contradiction.
  Qed.

End LemmasFn.
