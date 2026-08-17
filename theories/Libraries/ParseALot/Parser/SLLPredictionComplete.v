(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
From Crane.Libraries.ParseALot.Parser Require Import SLLPredictionErrorFree.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
Import ListNotations.

Module SllPredictionCompleteFn (Import D : Defs.T).

  Module Export SLLPEF := SllPredictionErrorFreeFn D.

  (** An empty SLL set cannot over-approximate a non-empty LL set — every LL subparser needs at least one SLL counterpart. *)
  Lemma overapprox_nil_cons_contra :
    forall sp sps,
      ~ overapprox [] (sp :: sps).
  Proof.
    intros sp sps ho.
    assert (hi : In sp (sp :: sps)) by apply in_eq.
    apply ho in hi; destruct hi as [? [hi ?]]; inv hi.
  Qed.

  (** If SLL final subparser handling rejects and SLL over-approximates LL, then LL final subparser handling also rejects. *)
  Lemma handle_final_subparsers_overapprox_reject :
    forall xs ys,
      overapprox ys xs
      -> sll_handle_final_subparsers ys = pred_reject
      -> handle_final_subparsers xs = pred_reject.
  Proof.
    intros xs ys ho hh.
    unfold handle_final_subparsers in *; unfold sll_handle_final_subparsers in *.
    destruct (filter _ ys) eqn:hf'; [.. | exfalso; dms; tc].
    destruct (filter _ xs) as [| x' xs'] eqn:hf; auto.
    eapply overapprox_final_config in ho; eauto.
    exfalso; eapply overapprox_nil_cons_contra; eauto.
  Qed.

  (* to do : it might be possible to remove some assumptions here *)
  (** If the SLL prediction loop rejects, the LL loop cannot succeed: SLL rejection propagates upward via overapproximation. *)
  Lemma sll_predict'_reject__ll_predict'_neq_succ :
    forall gr hw rm cm ts sps sps' ca ca' hk hk' hc rhs,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps ts
      -> overapprox sps' sps
      -> sll_predict' rm cm sps' ts ca hk' hc = (pred_reject, ca')
      -> ll_predict' gr hw rm sps ts hk <> pred_succ rhs.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca ca' hk hk' hc rhs hn hp hmc hw' hs he ho hsll hll;
      pose proof hll as hll'; simpl in hsll, hll.
    - injection hsll; intros heq' heq; subst.
      eapply handle_final_subparsers_overapprox_reject in heq; eauto; tc.
    - destruct sps as [| sp sps]; tc.
      destruct sps' as [| sp' sps'].
      + (* all SLL sps are exhausted *)
        eapply overapprox_nil_cons_contra; eauto.
      + (* at least one SLL sp remains *)
        destruct (all_predictions_equal_b _ _ sp' sps') eqn:ha'; tc.
        clear hll.
        eapply esp_ll_predict'_succ__exists_target in hll'; eauto.
        destruct hll' as [sps'' [ht hll']].
        apply sll_predict'_cont_cases in hsll. 
        destruct hsll as [[sps''' [hf hsll]] | [sps''' [ht' hsll]]].
        * pose proof hf as hf'; apply hc in hf'.
          destruct hf' as [hk'' ht'].
          eapply IH in hsll; eauto.
          -- eapply ll_target_preserves_stacks_wf_invar; eauto.
          -- eapply ll_target_preserves_stacks_stable_invar; eauto.
          -- eapply ll_target_preserves_successful_sp_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
        * eapply IH in hsll; eauto.
          -- eapply ll_target_preserves_stacks_wf_invar; eauto.
          -- eapply ll_target_preserves_stacks_stable_invar; eauto.
          -- eapply ll_target_preserves_successful_sp_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
  Qed.

  (* This might belong somewhere else *)
  (** If ll_predict' produces pred_ambig, a valid target state exists along with a continuation that also produces pred_ambig. *)
  Lemma esp_ll_predict'_succ__exists_target :
    forall gr hw rm sps a l ts hk ys,
      no_left_recursion gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> ll_predict' gr hw rm sps (@existT _ _ a l :: ts) hk = pred_ambig ys
      -> exists sps' hk',
          ll_target gr hw rm (@existT _ _ a l) sps hk = inr sps'
          /\ ll_predict' gr hw rm sps' ts hk' = pred_ambig ys.
  Proof.
    intros gr hw rm sps a l ts hk ys hn hw' hs hl; sis; dms; tc.
    apply ll_predict'_cont_cases in hl; destruct hl as [sps'' [ht hl]]; eauto.
  Qed.

  (* to do : it might be possible to remove some assumptions here *)
  (** If the SLL prediction loop rejects, the LL loop cannot produce pred_ambig: rejects in the over-approximation exclude all LL outcomes. *)
  Lemma sll_predict'_reject__ll_predict'_neq_ambig :
    forall gr hw rm cm ts sps sps' hk hk' ca hc ca' rhs,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> overapprox sps' sps
      -> sll_predict' rm cm sps' ts ca hk' hc = (pred_reject, ca')
      -> ll_predict' gr hw rm sps ts hk <> pred_ambig rhs.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' hk hk' ca hc ca' rhs hn hp hmc hw' hs ho hsll hll;
      pose proof hll as hll'; simpl in hsll, hll.
    - injection hsll; intros heq' heq; subst.
      eapply handle_final_subparsers_overapprox_reject in heq; eauto; tc.
    - destruct sps as [| sp sps]; tc.
      destruct sps' as [| sp' sps'].
      + (* all SLL sps are exhausted *)
        eapply overapprox_nil_cons_contra; eauto.
      + (* at least one SLL sp remains *)
        destruct (all_predictions_equal_b _ _ sp sps) eqn:ha; tc.
        apply ll_predict'_cont_cases in hll.
        destruct hll as [sps'' [ht hll]].
        destruct (all_predictions_equal_b _ _ sp' sps') eqn:ha'; tc.
        apply sll_predict'_cont_cases in hsll.
        destruct hsll as [[sps''' [hf hsll]] | [sps''' [ht' hsll]]].
        * pose proof hf as hf'; apply hc in hf'.
          destruct hf' as [hk'' ht'].
          eapply IH in hsll; eauto.
          -- eapply ll_target_preserves_stacks_wf_invar; eauto.
          -- eapply ll_target_preserves_stacks_stable_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
        * eapply IH in hsll; eauto.
          -- eapply ll_target_preserves_stacks_wf_invar; eauto.
          -- eapply ll_target_preserves_stacks_stable_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
  Qed.

  (** Under a stack-accepts-suffix regime, sll_predict never rejects: the over-approximation ensures SLL cannot reject when LL would succeed. *)
  Lemma ussr_sll_predict_neq_reject :
    forall gr (hw : grammar_wf gr) rm cm fr pre vs x suf frs ts ca hc ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_pushes_from_keyset rm (fr, frs)
      -> stack_wf gr (fr, frs)
      -> stack_accepts_suffix gr (fr, frs) ts
      -> sll_predict rm cm x ts ca hc <> (pred_reject, ca').
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hc ca'
           hn hpc hmc ? hk hw' hg hp'; pose proof hmc as [hsou hcom]; subst.
    unfold sll_predict in hp'.
    apply sll_predict_cases in hp'.
    destruct hp' as [sps' [hss' hp']].
    destruct (ll_start_state gr hw rm pre vs x suf frs hk) as [? | sps] eqn:hs; tc.
    - eapply ll_start_state_never_returns_error; eauto.
    - destruct (ll_predict' gr hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ hs))
        as [rhs | rhs | | e] eqn:hp.
      + eapply sll_predict'_reject__ll_predict'_neq_succ; eauto.
        * eapply ll_start_state_preserves_stacks_wf_invar; eauto.
        * eapply ll_start_state_all_stacks_stable; eauto.
        * eapply ll_start_state_preserves_esp_invar; eauto.
        * eapply overapprox_start_state; eauto. 
      + eapply sll_predict'_reject__ll_predict'_neq_ambig; eauto.
        * eapply ll_start_state_preserves_stacks_wf_invar; eauto.
        * eapply ll_start_state_all_stacks_stable; eauto.
        * eapply overapprox_start_state; eauto. 
      + eapply esp_ll_predict'_neq_reject; eauto.
        * eapply ll_start_state_preserves_stacks_wf_invar; eauto.
        * eapply ll_start_state_all_stacks_stable; eauto.
        * eapply ll_start_state_preserves_esp_invar; eauto.
      + eapply ll_predict'_never_returns_error; eauto.
        * eapply ll_start_state_preserves_stacks_wf_invar; eauto.
        * eapply ll_start_state_all_stacks_stable; eauto.
  Qed.
  
  (* THE PRIZE *)
  (** Completeness theorem: adaptive_predict never rejects when the stack accepts the suffix, so no valid parse is missed. *)
  Theorem sas_adaptive_predict_neq_reject :
    forall gr hw rm cm fr pre vs x suf frs ts ca hc hk ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_wf gr (fr, frs)
      -> stack_accepts_suffix gr (fr, frs) ts
      -> adaptive_predict gr hw rm cm pre vs x suf frs ts ca hc hk <> (pred_reject, ca').
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hc hk ca' hn hp hm ? hw' hr ha; subst; simpl in hr.
    unfold adaptive_predict in ha.
    dmeq hsll; dms; tc; inv ha.
    - eapply ussr_ll_predict_neq_reject; eauto.
    - eapply ussr_sll_predict_neq_reject; eauto.
  Qed.
  
End SllPredictionCompleteFn.
