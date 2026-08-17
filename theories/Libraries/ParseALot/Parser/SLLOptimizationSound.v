(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List Relation_Operators Operators_Properties.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import SLLPrediction.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module SllOptimizationSoundFn (Import D : Defs.T).

  Module Export SLLP := SllPredictionFn D.

  (* Definitions to capture the fact that SLL prediction overapproximates 
     LL prediction. For each LL subparser in play, there exists a corresponding
     SLL subparser that carries the same prediction and has a stack that matches
     the stack top of the LL subparser. There might also be SLL subparsers in 
     play that don't correspond to any of the LL subparsers, but prediction will
     fail over to LL mode if SLL mode finds more than one viable right-hand side.
     That's why SLL prediction is a _sound_ overapproximation of LL prediction. *)

  (** Converts a list of LL parser frames into the corresponding list of SLL frames. *)
  Fixpoint sllify (frs : list parser_frame) : list sll_frame :=
    match frs with
    | [] => []
    | Fr _ _ suf :: frs' =>
      match frs' with
      | [] => [sll_fr None suf]
      | Fr _ _ (NT x :: _) :: _ =>
        sll_fr (Some x) suf :: sllify frs'
      (* impossible for a well-formed parser stack *)
      | _ => []
      end
    end.

  (** sllify_head applied to the full stack is consistent with prepending to sllify of the frame list. *)
  Lemma sllify_head_cons__sllify_cons : forall g fr frs,
      stack_wf g (fr, frs)
      -> sllify_head (fr, frs) :: sllify frs = sllify (fr :: frs).
  Proof.
    intros g [pre vs suf] frs hw.
    sis.
    destruct frs as [| [pre_cr vs_cr suf_cr] frs].
    - auto.
    - destruct suf_cr as [| [a|x] suf_cr]; inv hw; auto.
  Qed.

  (** sp' approximates sp if they share the same prediction and the SLL stack is a prefix of the LL stack's sllify. *)
  Definition approx (sp' : sll_subparser) (sp : subparser) : Prop :=
    match sp', sp with
    | sll_sp pred' (fr', frs'), Sp pred (fr, frs) =>
      pred' = pred
      /\ exists ctx, fr' :: frs' ++ ctx = sllify (fr :: frs)
    end.

  (** Inverts the approx relation, extracting the equality of predictions and stack correspondence. *)
  Lemma approx_inv :
    forall pred pre vs suf frs pred' o' suf' frs',
      approx (sll_sp pred' (sll_fr o' suf', frs')) (Sp pred (Fr pre vs suf, frs))
      -> pred' = pred
         /\ suf' = suf
         /\ ((frs = [] /\ frs' = [] /\ o' = None)
             \/ (exists pre_cr vs_cr x suf_cr frs'' ctx,
                    frs = Fr pre_cr vs_cr (NT x :: suf_cr) :: frs''
                    /\ o' = Some x
                    /\ frs' ++ ctx = sllify (Fr pre_cr vs_cr (NT x :: suf_cr) :: frs''))).
  Proof.
    intros pred pre vs suf frs pred' o' suf' frs' ha.
    red in ha.
    destruct ha as [heq [ctx heq']]; subst.
    split; auto.
    eauto 20.
    destruct frs as [| [pre_cr vs_cr [| [a|x] suf_cr]] frs'']; inv heq'; eauto 12.
    match goal with
    | H : ?xs ++ ?ys = [] |- _ =>
      apply app_eq_nil in H; destruct H; subst
    end; auto.
  Qed.

  (** If an LL subparser is in final config and sp' approximates it, then sp' is also in SLL final config. *)
  Lemma approx_final_config_true :
    forall sp sp',
      approx sp' sp
      -> final_config sp  = true
      -> sll_final_config sp' = true.
  Proof.
    intros [pred stk] [pred' (fr', frs')] ha hf.
    eapply final_config_empty_stack in hf; eauto.
    destruct hf as (pre & vs & heq); subst.
    unfold approx in ha. destruct ha as [? [ctx heq]]; subst; sis.
    injection heq; intros heq' ?; subst.
    apply app_eq_nil in heq'; destruct heq'; subst; auto.
  Qed.

  (** The SLL prediction of an approximating subparser equals the LL prediction of the original. *)
  Lemma approx_predictions_eq :
    forall sp sp',
      approx sp' sp
      -> sll_pred sp' = prediction sp.
  Proof.
    unfold approx; intros sp sp' ha; dms; destruct ha; auto.
  Qed.

  (** If y approximates x and x moves to x', then y can also move to some y' that approximates x'. *)
  Lemma approx_move_sp :
    forall a l x x' y,
      approx y x
      -> move_sp (@existT _ _ a l) x = move_succ x'
      -> exists y',
          sll_move_sp a y = move_succ y'
          /\ approx y' x'.
  Proof.
    intros a l [pred ([pre vs suf], frs)] x' [pred' ([o' suf'], frs')] hx hm; unfold move_sp in hm; dms; tc; inv hm.
    apply approx_inv in hx.
    destruct hx as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); subst.
      unfold sll_move_sp; dm; tc.
      eexists; split; eauto.
      split; auto.
      exists []; auto.
    - destruct hr as (pre_cr & vs_cr & x & suf_cr & frs'' & ctx & ? & ? & heq); subst. 
      unfold sll_move_sp; dm; tc.
      eexists; split; eauto.
      split; auto.
      exists ctx; rewrite heq; auto.
  Qed.

(*  Lemma approx_head_frames_eq :
    forall pred pred' fr fr' frs frs',
      approx (Sp pred' (fr', frs')) (Sp pred (fr, frs))
      -> fr' = fr.
  Proof.
    intros pred pred' fr fr' frs frs' ha.
    destruct ha as [? [? heq]]; inv heq; auto.
  Qed.
 *)

  (** When the LL subparser is done, the SLL counterpart cannot trigger sim_return. *)
  Lemma approx_ll_done_sim_return_contra :
    forall gr hw rm cm vi sp sp' sps'',
      stack_wf gr (stack sp)
      -> approx sp' sp
      -> cstep gr hw rm vi sp = cstep_done
      -> sim_return cm sp' <> Some sps''.
  Proof.
    intros gr hw rm cm av [pred (fr, frs)] [pred' (fr', frs')] sps'' hw' ha hs hr.
    eapply cstep_done_stable_config in hs; eauto.
    apply sim_return_stack_shape in hr.
    destruct hr as [x heq]; simpl in heq.
    inv heq.
    destruct fr as [pre vs suf].
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); tc.
    - destruct hr as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst; sis. 
      inv hs.
  Qed.

  (** When the LL subparser is done, the SLL counterpart cannot take a further sll_cstep. *)
  Lemma approx_ll_done_sll_step_contra :
    forall gr hw rm vi vi' vi'' sp sp' sps'',
      stack_wf gr (stack sp)
      -> approx sp' sp
      -> cstep gr hw rm vi sp = cstep_done
      -> sll_cstep rm vi' sp' <> cstep_k vi'' sps''.
  Proof.
    intros gr hw rm vi vi' vi'' [pr ([pre vs suf], frs)] [pr' ([o' suf'], frs')] sps'' hw' ha hs hs'.
    eapply cstep_done_stable_config in hs; eauto.
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); subst.
      sis; dms; tc; inv hs; inv hs'.
    - destruct hr as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst.
      sis; dms; tc; inv hs; inv hs'.
  Qed.

  (** When the LL subparser steps and sim_return is absent, the SLL counterpart cannot be done. *)
  Lemma approx_ll_step_sll_done_contra :
    forall gr hw rm cm vi vi' vi'' x y xs',
      stack_wf gr (stack x)
      -> approx y x
      -> sim_return cm y = None
      -> cstep gr hw rm vi x = cstep_k vi' xs'
      -> sll_cstep rm vi'' y <> cstep_done.
  Proof.
    intros gr hw rm cm ? ? ? [pr (fr, frs)] [pr' (fr', frs')] xs' hw' ha hr hs hs'.
    sis; dms; tc; inv hs; inv hs'; destruct ha as [? [? heq]]; inv heq; inv hw.
  Qed.

  (* to do -- refactor *)
  (** When both LL and SLL subparsers step, every LL successor has a corresponding SLL successor that approximates it. *)
  Lemma approx_cstep :
    forall gr hw rm ax ax' ay ay' x x' y xs' ys',
      rhs_map_correct rm gr
      -> approx y x
      -> cstep gr hw rm ax x = cstep_k ax' xs'
      -> sll_cstep rm ay y = cstep_k ay' ys'
      -> In x' xs'
      -> exists y', In y' ys' /\ approx y' x'.
  Proof.
    intros gr hw rm ax ax' ay ay' [pr ([pre vs suf], frs)] x' [pr' ([o' suf'], frs')] xs' ys'
           hc ha hs hs' hi.
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); subst.
      unfold cstep in *; unfold sll_cstep in *; dmeqs H; tc; inv hs; inv hs'; try solve [inv hi].
      + exfalso.
        eapply NMF.in_find_iff; eauto.
        apply in_map_iff in hi; destruct hi as [ys [heq hi]]; subst.
        eapply rhss_for_in_iff in hi; eauto.
        red in hc.
        destruct hc as [hk [hs hc]].
        red in hk.
        red in hs.
        red in hc.
        apply hc in hi.
        destruct hi as [yss [hm hi]].
        eapply nm_mapsto_in; eauto.
      + apply in_map_iff in hi.
        destruct hi as [ys [heq hi]]; subst.
        eexists; split.
        * apply in_map_iff; eauto.
        * split; auto.
          exists []; auto.
    - destruct hr as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst.
      unfold cstep in *; unfold sll_cstep in *; dmeqs H; tc; inv hs; inv hs'; try solve [inv hi].
      + apply in_singleton_eq in hi; subst.
        eexists; split.
        * apply in_eq.
        * split; auto.
          destruct x3 as [| [pre_cr vs_cr [| [a'|x'] suf_cr]] frs'']; sis; inv H1; eauto.
      + exfalso.
        eapply NMF.in_find_iff; eauto.
        apply in_map_iff in hi; destruct hi as [ys [heq hi]]; subst.
        eapply rhss_for_in_iff in hi; eauto.
        red in hc.
        destruct hc as [hk [hs hc]].
        red in hk.
        red in hs.
        red in hc.
        apply hc in hi.
        destruct hi as [yss [hm hi]].
        eapply nm_mapsto_in; eauto.
      + apply in_map_iff in hi.
        destruct hi as [ys [heq hi]]; subst.
        eexists; split.
        * apply in_map_iff; eauto.
        * split; auto.
          eexists; auto.
          sis.
          rewrite H1; auto.
  Qed.

  (** If the LL stack is stable, then its sllify head frame is stable in the SLL sense. *)
  Lemma stable_config__stable_sllify_head :
    forall fr frs,
      stable_config (fr, frs) -> stable (sllify_head (fr, frs)) = true.
  Proof.
    intros fr frs hs; inv hs; auto.
    destruct frs as [| [pre_cr vs_cr [| [a'|x'] suf_cr]] frs]; auto.
  Qed.

  (* refactor -- this should probably be several lemmas *)
  (** When sim_return fires on y (approximating x), the returned SLL subparsers approximate the LL closure destination x''. *)
  Lemma sim_return_approx :
    forall g cm av av' av'' x x' x'' y ys'',
      closure_map_complete g cm
      -> stack_wf g (stack x)
      -> approx y x
      -> closure_step g av x av' x'
      -> closure_multistep g av' x' av'' x''
      -> sim_return cm y = Some ys''
      -> exists y'', In y'' ys'' /\ approx y'' x''.
  Proof.
    intros g cm av av' av'' [pr ([pre vs suf], frs)] [pr' (fr', frs')] [pr'' (fr'', frs'')]
           [pr''' ([o''' suf'''], frs''')] ys'' hcm hw ha hs hm hr; simpl in hw.
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr']); subst.
    - exfalso.
      destruct hl as (? & ? & ?); subst.
      apply sim_return_stack_shape in hr.
      destruct hr as [x heq]; inv heq.
    - destruct hr' as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst.
      pose proof hr as hr'.
      apply sim_return_stack_shape in hr'.
      destruct hr' as [x' heq].
      simpl in heq.
      inv heq.
      simpl in H1. subst.
    assert (heq : pr'' = pr).
    { apply closure_step_preserves_label in hs; sis; subst.
      apply closure_multistep_preserves_label in hm; sis; subst; auto. } subst.
    assert (hw' : stack_wf g (fr', frs')).
    { apply closure_step_preserves_stack_wf_invar in hs; sis; auto. }
    assert (hw'' : stack_wf g (fr'', frs'')).
    { apply closure_multistep_preserves_stack_wf_invar in hm; auto. }
    assert (hst : stable_config (fr'', frs'')).
    { apply stable_config_after_closure_multistep in hm; sis; auto. }
    eapply closure_step__frame_step in hs; eauto.
    eapply closure_multistep__frame_step_trc in hm; eauto.
    assert (sllify_head (Fr pre vs [], Fr x x0 (NT x' :: x2) :: x3) = sll_fr (Some x') []).
    { simpl; auto. }
    rewrite H in hs.
    assert (hfm : frame_multistep g (sll_fr (Some x') []) (sllify_head (fr'', frs''))).
    { eapply clos_t_rt; eauto.
      apply clos_rt_rt1n_iff; auto. }
    exists (sll_sp pr (sllify_head (fr'', frs''), [])); split.
      + simpl in hr.
        inv hr.
        apply in_map_iff.
        eexists; split; eauto.
        unfold dest_frames.
        pose proof hfm as hfm'.
        apply hcm in hfm'.
        destruct hfm' as [v [hf hi]].
        * apply stable_config__stable_sllify_head; auto. 
        * apply FMF.find_mapsto_iff in hf.
          rewrite hf; auto.
      + red.
        split; auto.
        exists (sllify frs'').
        rewrite app_nil_l.
        eapply sllify_head_cons__sllify_cons; eauto.
  Qed.

  (** The SLL list sps' over-approximates the LL list sps: for every LL subparser, some SLL subparser approximates it. *)
  Definition overapprox (sps' : list sll_subparser) (sps : list subparser) : Prop :=
    forall sp, In sp sps -> exists sp', In sp' sps' /\ approx sp' sp.
  
  (** Restricting overapprox to final configurations preserves the overapprox relation. *)
  Lemma overapprox_final_config :
    forall sps sps' sps'' sps''',
      overapprox sps''' sps''
      -> filter final_config sps''  = sps
      -> filter sll_final_config sps''' = sps'
      -> overapprox sps' sps.
  Proof.
    intros sps sps' sps'' sps''' ho hf hf' sp'' hi; subst.
    apply filter_In in hi; destruct hi as [hi hf].
    apply ho in hi; destruct hi as [sp''' [hi ha]].
    eexists; split; eauto.
    eapply approx_final_config_true in hf; eauto; apply filter_In; auto.
  Qed.

  (** When SLL predictions all agree, each LL subparser's prediction matches the common SLL prediction. *)
  Lemma overapprox_ape_pointwise :
    forall x y xs ys,
      overapprox (y :: ys) xs
      -> all_predictions_equal_b beq_gamma sll_pred y ys = true
      -> In x xs
      ->  sll_pred y = prediction x.
  Proof.
    intros x y xs ys ho ha hi.
    apply ho in hi; destruct hi as [y' [hi he]].
    apply eq_trans with (y := sll_pred y').
    - inv hi; auto.
      eapply all_predictions_equal_prop in ha.
      + firstorder.
      + apply beq_gamma_eq_iff.
    - apply approx_predictions_eq; auto.
  Qed.

  (** SLL unanimous agreement implies LL unanimous agreement on the approximated subparsers. *)
  Lemma overapprox_all_predictions_equal_big_small :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> all_predictions_equal_b beq_gamma sll_pred y ys = true
      -> all_predictions_equal_b beq_gamma prediction x xs = true.
  Proof.
    intros x y xs ys ho ha; unfold all_predictions_equal; unfold all_equal.
    apply forallb_forall; intros pred hi.
    apply beq_gamma_eq_iff.
    apply in_map_iff in hi; destruct hi as [x' [? hi]]; subst.
    apply eq_trans with (y := sll_pred y).
    - symmetry; eapply overapprox_ape_pointwise; eauto; apply in_eq.
    - eapply overapprox_ape_pointwise; eauto; apply in_cons; auto.
  Qed.

  (** When both LL and SLL report pred_succ at end-of-input, the predicted rhs values coincide. *)
  Lemma overapprox_final_subparsers_succ_eq :
    forall sps sps' rhs rhs',
      overapprox sps' sps
      -> handle_final_subparsers sps     = pred_succ rhs
      -> sll_handle_final_subparsers sps' = pred_succ rhs'
      -> rhs' = rhs.
  Proof.
    intros sps sps' rhs rhs' ho hl hs;
      unfold handle_final_subparsers in *; unfold sll_handle_final_subparsers in *.
    destruct (filter _ sps ) as [| x xs] eqn:hf  ; tc.
    destruct (filter _ sps') as [| y ys] eqn:hf' ; tc.
    destruct (all_predictions_equal_b _ _ x xs)  eqn:ha  ; tc; inv hl.
    destruct (all_predictions_equal_b _ _ y ys)  eqn:ha' ; tc; inv hs.
    eapply overapprox_final_config in ho; eauto.
    eapply overapprox_ape_pointwise; eauto; apply in_eq.
  Qed.
  
  (** LL disagreement implies SLL disagreement when the SLL list over-approximates the LL list. *)
  Lemma overapprox_all_predictions_equal_false :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> all_predictions_equal_b beq_gamma prediction x xs = false
      -> all_predictions_equal_b beq_gamma sll_pred y ys = false.
  Proof.
    intros x y xs ys ho ha.
    apply ape_false__all_predictions_equal_false; intros ha'.
    - apply beq_gamma_eq_iff.
    - apply all_predictions_equal_b_false_exists_diff_rhs in ha.
      destruct ha as [x' [hi hneq]]; apply hneq; clear hneq.
      apply eq_trans with (y := sll_pred y).
      (* These could probably be lemmas *)
      + apply in_cons with (a := x) in hi.
        apply ho in hi; destruct hi as [y' [hi hx]].
        apply approx_predictions_eq in hx.
        apply ape_cons_head_eq in ha'; apply ha' in hi; tc.
      + assert (hh : In x (x :: xs)) by apply in_eq.
        apply ho in hh; destruct hh as [y' [hh hx]].
        apply approx_predictions_eq in hx.
        apply ape_cons_head_eq in ha'; apply ha' in hh; tc.
      + apply beq_gamma_eq_iff.
  Qed.

  (** If SLL reports pred_succ, LL cannot report pred_ambig: SLL success rules out LL ambiguity. *)
  Lemma overapprox_handle_final_subparsers_contra :
    forall xs ys rhs rhs',
      overapprox ys xs
      -> sll_handle_final_subparsers ys = pred_succ rhs'
      -> handle_final_subparsers xs <> pred_ambig rhs.
  Proof.
    intros xs ys rhs rhs' ho hh' hh;
      unfold handle_final_subparsers in *; unfold sll_handle_final_subparsers in *.
    destruct (filter _ ys) as [| y' ys'] eqn:hf'; tc.
    destruct (filter _ xs) as [| x' xs'] eqn:hf ; tc.
    eapply overapprox_final_config in ho; eauto.
    destruct (all_predictions_equal_b _ _ x' xs') eqn:ha; tc; inv hh.
    eapply overapprox_all_predictions_equal_false in ha; eauto.
    rewrite ha in hh'; tc.
  Qed.
  
  (** The move operation preserves the overapprox relation: if ys over-approximates xs before moving, it does so after. *)
  Lemma move_preserves_overapprox :
    forall a l xs xs' ys ys',
      overapprox ys xs
      -> move (@existT _ _ a l) xs = inr xs'
      -> sll_move a ys = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros a l xs xs' ys ys' ho hm hm' x' hi.
    eapply aggr_move_results_map_backwards in hi; eauto.
    destruct hi as [x [hi hm'']].
    apply ho in hi; destruct hi as [y [hi hx]].
    eapply approx_move_sp in hm''; eauto.
    destruct hm'' as [y' [hm'' hx']].
    eapply aggr_move_results_succ_all_sll_sps_step in hm''; eauto.
  Qed.

  (** A singleton approximation implies singleton overapprox. *)
  Lemma approx_overapprox_singleton :
    forall x y,
      approx y x
      -> overapprox [y] [x].
  Proof.
    intros x y ha ? hi; apply in_singleton_eq in hi; subst.
    eexists; split; [apply in_eq | auto].
  Qed.

  (* Interesting and complicated lemma -- make sure to write
     a note about it *)
  (** Core bisimulation: if y approximates x and both closures succeed, the SLL results over-approximate the LL results. *)
  Lemma llc_sllc_approx_overapprox' :
    forall gr hw rm cm pr (a : Acc lex_nat_pair pr) vi vi' x y hk hk' xs' ys' a' a'',
      pr = ll_meas rm vi x
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (stack x)
      -> approx y x
      -> llc gr hw rm vi x hk a' = inr xs'
      -> sllc rm cm vi' y hk' a'' = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros gr hw rm cm pr a''; induction a'' as [pr hlt IH].
    intros vix viy x y hk hk' xs''' ys''' a a'
           ? hp hm hw' hx hll hsll; subst.
    apply llc_success_cases in hll.
    destruct hll as [[hs ?] | [xs' [vix' [hs [? [? ha]]]]]]; subst.
    - (* the LL subparser is done *)
      apply sllc_success_cases in hsll.
      destruct hsll as [hr | [hr [[hs' ?] | [ys' [viy' [hs' [? [? ha']]]]]]]]; subst.
      + (* SLL subparser simulates a return -- contradiction *)
        exfalso; eapply approx_ll_done_sim_return_contra; eauto.
      + (* both subparsers are done -- easy *)
        apply approx_overapprox_singleton; auto.
      + (* SLL subparser steps -- contradiction *)
        exfalso; eapply approx_ll_done_sll_step_contra; eauto.
    - (* the LL subparser steps *)
      apply sllc_success_cases in hsll.
      destruct hsll as [hr | [hr [[hs' ?] | [ys' [viy' [hs' [? [? ha']]]]]]]]; subst.
      + (* INTERESTING CASE 
           SLL subparser simulates a return
           Prove a lemma about a correspondence between 
           sim_return and a cstep/llc operation *)
        intros x''' hi'''.
        eapply aggr_closure_results_succ_in_input in ha; eauto.
        destruct ha as [xs'' [hd hi'']].
        eapply dmap_in in hd; eauto.
        destruct hd as [x' [hi' [? hll]]].
        assert (Hcm : exists vix''',
                   closure_step gr vix x vix' x'
                   /\ closure_multistep gr vix' x' vix''' x''').
        { pose proof hs as hs''.
          eapply cstep_sound in hs''; eauto.
          eapply llc_sound_wrt_closure_multistep in hll; eauto.
          - destruct hll as [vix''' hcm]; eauto.
          - eapply closure_step_preserves_stack_wf_invar; eauto. }
        destruct Hcm as [vi''' [Hcs Hcm]].
        eapply sim_return_approx; eauto.
      + (* SLL subparser is done -- contradiction *)
        exfalso; eapply approx_ll_step_sll_done_contra; eauto.
      + (* both subparsers step -- IH *)
        intros x''' hi'''.
        eapply aggr_closure_results_succ_in_input in ha; eauto.
        destruct ha as [xs'' [hd hi'']].
        eapply dmap_in in hd; eauto.
        destruct hd as [x' [? [hi' hll]]].
        eapply approx_cstep in hi'; eauto.
        destruct hi' as [y' [hiy' hx']].
        eapply aggr_closure_results_dmap_succ_elt_succ in ha'; eauto.
        destruct ha' as [? [ys'' [hsll ha']]].
        eapply IH with (ys' := ys'') in hll; eauto.
        * apply hll in hi''; destruct hi'' as [y'' [hiy'' hx'']]; eauto.
        * eapply cstep_meas_lt; eauto.
        * eapply cstep_preserves_stack_wf_invar; eauto.
  Qed.

  (** Wrapper for llc_sllc_approx_overapprox' without the measure argument. *)
  Lemma llc_sllc_approx_overapprox :
    forall gr hw rm cm vi vi' x y hk hk' xs' ys' a a',
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (stack x)
      -> approx y x
      -> llc gr hw rm vi x hk a = inr xs'
      -> sllc rm cm vi' y hk' a' = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros; eapply llc_sllc_approx_overapprox' with (pr := ll_meas _ _ _); eauto.
  Qed.
  
  (** LL and SLL closure operations preserve overapprox: if ys over-approximates xs before, it does so after. *)
  Lemma closure_preserves_overapprox :
    forall gr hw rm cm xs xs' ys ys' hk hk',
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr xs
      -> overapprox ys xs
      -> ll_closure gr hw rm xs hk = inr xs'
      -> sll_closure rm cm ys hk' = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros gr hw rm cm xs xs'' ys ys'' hk hk' hp hm hw' ho hl hc x'' hi.
    unfold ll_closure in hl.
    unfold sll_closure in hc.
    eapply aggr_closure_results_dmap_backwards in hi; eauto.
    destruct hi as [x [hi [xs' [_ [hc' hi']]]]].
    pose proof hi as hw''; apply hw' in hw''.
    pose proof hi as hi''.
    apply ho in hi''; destruct hi'' as [y [hi'' hyx]].
    eapply aggr_closure_results_dmap_succ_elt_succ in hc; eauto.
    destruct hc as [hi''' [ys' [hs' ha]]].
    eapply llc_sllc_approx_overapprox in hs'; eauto.
    apply hs' in hi'; destruct hi' as [? [? ? ]]; eauto.
  Qed.
  
  (** The target (move + closure) operation preserves overapprox across a token step. *)
  Lemma target_preserves_overapprox :
    forall gr hw rm cm sps sps' hk hk' sps'' sps''' a l,
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr sps
      -> overapprox sps' sps
      -> ll_target gr hw rm (@existT _ _ a l) sps hk = inr sps''
      -> sll_target rm cm a sps' hk' = inr sps'''
      -> overapprox sps''' sps''.
  Proof.
    intros gr hw rm cm xs ys hk hk' xs'' ys'' a l hp hf hw' ho hl hs.
    apply ll_target_cases in hl; destruct hl as [xs' [hk'' [hm hc]]].
    apply sll_target_cases in hs; destruct hs as [ys' [hk''' [hm' hc']]].
    eapply move_preserves_overapprox in hm'; eauto.
    eapply move_preserves_stack_wf_invar in hw'; eauto.
    eapply closure_preserves_overapprox; eauto.
  Qed.

  (** The SLL initial subparsers over-approximate the LL initial subparsers for the same nonterminal. *)
  Lemma overapprox_init_sps :
    forall rm pre vs x suf frs sps sps',
      ll_init_sps rm pre vs x suf frs = sps
      -> sll_init_sps rm x = sps'
      -> overapprox sps' sps.
  Proof.
    intros rm pre vs x suf frs sps sps' hl hs sp hi; subst.
    apply in_map_iff in hi; destruct hi as [ys [? hi]]; subst.
    eexists; split.
    - apply in_map_iff; eauto.
    - sis; eauto.
  Qed.
  
  (** The SLL start state over-approximates the LL start state for the same nonterminal and stack context. *)
  Lemma overapprox_start_state :
    forall gr hw rm cm fr pre vs x suf frs hk sps sps',
      fr = Fr pre vs (NT x :: suf)
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (fr, frs)
      -> ll_start_state gr hw rm pre vs x suf frs hk = inr sps
      -> sll_start_state rm cm x = inr sps'
      -> overapprox sps' sps.
  Proof.
    intros gr hw rm cm fr pre vs x suf frs hk sps sps' ? hp hc hw' hl hs; subst.
    eapply closure_preserves_overapprox; eauto.
    - eapply ll_init_sps_preserves_stack_wf_invar; eauto.
    - eapply overapprox_init_sps; eauto.
  Qed.

  (* The main results in this module: correspondences
     between LL and SLL prediction *)

  (** When LL predicts ys and SLL predicts ys', and SLL over-approximates LL, the predictions agree. *)
  Lemma sll_predict'_ll_predict'_succ_eq :
    forall gr hw rm cm ts sps' sps ca hk hk' hc ys ca' ys',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps ts
      -> overapprox sps' sps
      -> ll_predict' gr hw rm sps ts hk = pred_succ ys
      -> sll_predict' rm cm sps' ts ca hk' hc = (pred_succ ys', ca')
      -> ys' = ys.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a,l) ts IH];
      intros sps' sps ca hk hk' hc ys ca' ys' hn hp hm hw' hs he ho hll hsll;
      pose proof hll as hll'; simpl in hll, hsll.
    - inv hsll; eapply overapprox_final_subparsers_succ_eq; eauto.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps  as [| sp  sps ]; tc.
      destruct (all_predictions_equal_b _ _ sp' sps') eqn:ha'.
      + inv hsll.
        assert (ha : all_predictions_equal_b beq_gamma prediction sp sps = true).
        { eapply overapprox_all_predictions_equal_big_small; eauto. }
        rewrite ha in hll; inv hll.
        eapply overapprox_ape_pointwise; eauto.
        apply in_eq.
      + eapply esp_ll_predict'_succ__exists_target in hll'; eauto.
        destruct hll' as [sps'' [ht hll']].
        apply sll_predict'_cont_cases in hsll.
        destruct hsll as [[sps''' [hf hsll]] | [sps''' [ht' hsll]]].
        * pose proof hf as hf'; apply hc in hf'.
          destruct hf' as [hk'' ht'].
          eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply ll_target_preserves_stacks_wf_invar; eauto.
          -- eapply ll_target_preserves_stacks_stable_invar; eauto.
          -- eapply ll_target_preserves_successful_sp_invar; eauto.
          -- eapply target_preserves_overapprox; eauto.
        * eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply ll_target_preserves_stacks_wf_invar; eauto.
          -- eapply ll_target_preserves_stacks_stable_invar; eauto.
          -- eapply ll_target_preserves_successful_sp_invar; eauto.
          -- eapply target_preserves_overapprox; eauto. 
  Qed.

  (** When both ll_predict and sll_predict return pred_succ, their predicted rhs values are equal. *)
  Lemma sll_predict_ll_predict_succ_eq :
    forall gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs rhs' ca',
      cr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> stack_accepts_suffix gr (cr, frs) ts
      -> ll_predict gr hw rm pre vs x suf frs ts hk = pred_succ rhs
      -> sll_predict rm cm x ts ca hc = (pred_succ rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs rhs' ca' ? hn hp hc' hw' hg hl hs; subst.
    apply ll_predict_cases in hl; destruct hl as [sps [hss hl]].
    apply sll_predict_cases in hs; destruct hs as [sps' [hss' hs]].
    eapply sll_predict'_ll_predict'_succ_eq; eauto.
    - eapply ll_start_state_preserves_stacks_wf_invar; eauto.
    - eapply ll_start_state_all_stacks_stable; eauto.
    - eapply ll_start_state_preserves_esp_invar; eauto. 
    - eapply overapprox_start_state; eauto. 
  Qed.

  (** If SLL predicts a unique rhs (pred_succ), then LL cannot predict pred_ambig. *)
  Lemma sll_predict'_succ__ll_predict'_neq_ambig :
    forall gr hw rm cm ts sps sps' ca hk hk' hc ca' ys ys',
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr sps
      -> overapprox sps' sps
      -> sll_predict' rm cm sps' ts ca hk' hc = (pred_succ ys, ca')
      -> ll_predict' gr hw rm sps ts hk <> pred_ambig ys'.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca hk hk' hc ca' ys ys' hp hm hw' ho hs hl; sis.
    - inv hs; eapply overapprox_handle_final_subparsers_contra; eauto.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps as [| sp sps]; tc.
      destruct (all_predictions_equal_b _ _ sp sps) eqn:ha; tc.
      eapply overapprox_all_predictions_equal_false in ha; eauto.
      rewrite ha in hs.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      apply sll_predict'_cont_cases in hs.
      destruct hs as [[sps''' [hf hs]] | [sps''' [ht' hs]]].
      + pose proof hf as hf'; apply hc in hf'.
        destruct hf' as [hk'' ht'].
        eapply IH in hs; eauto.
        * eapply ll_target_preserves_stacks_wf_invar; eauto.
        * eapply target_preserves_overapprox; eauto.
      + eapply IH in hs; eauto.
        * eapply ll_target_preserves_stacks_wf_invar; eauto.
        * eapply target_preserves_overapprox; eauto. 
  Qed.

  (** Top-level wrapper: sll_predict success rules out ll_predict ambiguity. *)
  Lemma sll_predict_succ__ll_predict_neq_ambig :
    forall gr hw rm cm fr pre vs x suf frs ts ca hk hc ys ca' ys',
      fr = Fr pre vs (NT x :: suf)
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (fr, frs)
      -> sll_predict rm cm x ts ca hc = (pred_succ ys, ca')
      -> ll_predict gr hw rm pre vs x suf frs ts hk <> pred_ambig ys'.
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hk hc ys ca' ys' ? hp hc' hw' hs hl; subst.
    apply sll_predict_cases in hs; destruct hs as [sps' [hss' hs]].
    apply ll_predict_cases in hl; destruct hl as [sps [hss hl]].
    eapply sll_predict'_succ__ll_predict'_neq_ambig; eauto.
    - eapply ll_start_state_preserves_stacks_wf_invar; eauto.
    - eapply overapprox_start_state; eauto. 
  Qed.
  
  (** The soundness theorem for SLL: if SLL predicts rhs, then LL also predicts rhs. *)
  Lemma sll_predict_succ_eq_ll_predict_succ :
    forall gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs ca',
      cr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> stack_accepts_suffix gr (cr, frs) ts
      -> sll_predict rm cm x ts ca hc = (pred_succ rhs, ca')
      -> ll_predict gr hw rm pre vs x suf frs ts hk = pred_succ rhs.
  Proof.
    intros gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs' ca' ?
           hn hp hc' hw' hg hs; subst. 
    destruct (ll_predict _ _ _ _) as [rhs | rhs | | e] eqn:hl.
    - symmetry; f_equal; eapply sll_predict_ll_predict_succ_eq; eauto.
    - exfalso; eapply sll_predict_succ__ll_predict_neq_ambig; eauto.
    - exfalso; eapply ussr_ll_predict_neq_reject; eauto.
    - exfalso; eapply ll_predict_never_returns_error; eauto.
  Qed.

  (** If adaptive_predict returns pred_succ rhs, then LL also returns pred_succ rhs for the same inputs. *)
  Lemma adaptive_predict_succ_eq_ll_predict_succ :
    forall gr hw rm cm cr pre vs x suf frs ts ca hc hk rhs ca',
      cr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> stack_accepts_suffix gr (cr, frs) ts
      -> adaptive_predict gr hw rm cm pre vs x suf frs ts ca hc hk = (pred_succ rhs, ca')
      -> ll_predict gr hw rm pre vs x suf frs ts hk = pred_succ rhs.
  Proof.
    intros gr hw rm cm cr pre vs x suf frs ts ca hc hk rhs ca' ? hn hp hc' hw' hg ha; subst. 
    unfold adaptive_predict in ha.
    destruct (sll_predict _ _ _ _ _) as ([? | ? | | ?], ?) eqn:hs; tc; inv ha.
    eapply sll_predict_succ_eq_ll_predict_succ; eauto.
  Qed.

  (** Uniqueness: if adaptive_predict returns pred_succ rhs' and (x, rhs) is in the grammar with the stack accepting ts, then rhs' = rhs. *)
  Theorem adaptive_predict_succ_at_most_one_rhs_applies :
    forall gr hw rm cm cr ce pre vs x suf frs ts ca hc hk rhs rhs' ca',
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> PM.In (x, rhs) gr
      -> stack_accepts_suffix gr (ce, cr :: frs) ts
      -> adaptive_predict gr hw rm cm pre vs x suf frs ts ca hc hk = (pred_succ rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros gr hw rm cm cr ce pre vs x suf frs ts ca hc hk rhs rhs' ca' ? ? hn hr hc' hw' hi hg ha; subst.
    eapply adaptive_predict_succ_eq_ll_predict_succ in ha; eauto.
    - eapply ll_predict_succ_at_most_one_rhs_applies; eauto.
    - (* lemma *)
      destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
      destruct hl as (wsuf' & wsuf'' & vs_suf' & p & f & heq & hd' & hm & hp & hl); subst; sis.
      exists (wpre ++ wsuf'); exists wsuf''; eexists;
        repeat split; eauto; apps; econstructor; eauto.
  Qed.

  (** An adaptive_predict ambiguity is directly an LL ambiguity, because the ambig path falls through to LL. *)
  Lemma adaptive_predict_ambig_ll_predict_ambig :
    forall gr hw rm cm pre vs x suf frs ts ca hc hk rhs ca',
      adaptive_predict gr hw rm cm pre vs x suf frs ts ca hc hk = (pred_ambig rhs, ca')
      -> ll_predict gr hw rm pre vs x suf frs ts hk = pred_ambig rhs.
  Proof.
    unfold adaptive_predict; intros; dms; tc. 
  Qed.

  (** An adaptive_predict ambiguity implies the stack accepts the token suffix, mirroring the LL ambiguity theorem. *)
  Theorem adaptive_predict_ambig_rhs_unproc_stack_syms:
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (cm  : closure_map)
           (rm  : rhs_map)
           (cr  : parser_frame)
           (ce  : parser_frame)
           (pre : list symbol)
           (vs  : symbols_semty pre)
           (x   : nonterminal)
           (suf : list symbol)
           (frs : list parser_frame)
           (ts  : list token)
           (ca  : cache)
           (hc  : cache_stores_target_results rm cm ca)
           (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs))
           (rhs : list symbol)
           (ca' : cache),
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> adaptive_predict gr hw rm cm pre vs x suf frs ts ca hc hk = (pred_ambig rhs, ca')
      -> stack_accepts_suffix gr (ce, cr :: frs) ts. 
  Proof.
    intros gr hw rm cm cr ce pre vs x suf frs ts ca hc hk rhs ca' ? ? hn hp hw' ha; subst.
    eapply ll_predict_ambig_rhs_unproc_stack_syms; eauto.
    eapply adaptive_predict_ambig_ll_predict_ambig; eauto.
  Qed. 
    
End SllOptimizationSoundFn.
