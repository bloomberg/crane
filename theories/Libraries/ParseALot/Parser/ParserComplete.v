(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Bool List String.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import ParserErrorFree.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module ParserCompleteFn (Import D : Defs.T).

  Module Export PEF := ParserErrorFreeFn D.

  (** A successful-prediction push preserves [stack_accepts_suffix]: the new callee frame accepts the same remaining input as the caller frame did. *)
  Lemma push_succ_preserves_sas :
    forall gr hw rm cm cr ce frs pre vs x suf rhs w ca hc hk ca',
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr (cr, frs)
      -> adaptive_predict gr hw rm cm pre vs x suf frs w ca hc hk = (pred_succ rhs, ca')
      -> stack_accepts_suffix gr (cr, frs) w
      -> stack_accepts_suffix gr (ce, cr :: frs) w.
  Proof.
    intros gr hw rm cm cr ce frs pre vs x suf rhs w ca hc hk ca' ? ? hn hr hc' hw' ha hs; subst; sis.
    destruct hc' as [hcs hcc].
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    destruct vs_suf as (v_suf, vs_suf).
    eapply svd_inv_nonterminal_head with
        (x   := x)
        (v'  := v_suf)
        (vs' := vs_suf)
        (heq := eq_refl) in hd; eauto.
    destruct hd as (wpre' & wpre'' & heq & hh & ht); subst.
    inv_sv hh hm hvs hp; s_inj.
    pose proof hm as hm'.
    apply pm_mapsto_in in hm.
    eapply adaptive_predict_succ_at_most_one_rhs_applies in ha; eauto; subst.
    - exists wpre'; exists (wpre'' ++ wsuf); eexists; repeat split; eauto; apps.
      exists wpre''; exists wsuf; repeat eexists; repeat split; eauto.
    - red.
      exists wpre'; exists (wpre'' ++ wsuf); eexists; repeat split; eauto; apps.
      repeat eexists; repeat split; eauto.
  Qed.

  (** An ambiguous-prediction push preserves [stack_accepts_suffix]: the chosen right-hand side still accepts the remaining input. *)
  Lemma push_ambig_preserves_sas :
    forall gr hw rm cm cr ce pre vs x suf frs w ca hc hk rhs ca',
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> adaptive_predict gr hw rm cm pre vs x suf frs w ca hc hk = (pred_ambig rhs, ca')
      -> stack_accepts_suffix gr (cr, frs) w
      -> stack_accepts_suffix gr (ce, cr :: frs) w.
  Proof.
    intros gr hw rm cm cr ce pre vs x suf frs w ca hc hk rhs ca' ? ? hn hr hw' ha hs; subst.
    eapply adaptive_predict_ambig_rhs_unproc_stack_syms; eauto.
  Qed.
  
  (** Any [step_k] result preserves [stack_accepts_suffix], so a parseable input remains parseable after each step. *)
  Lemma step_preserves_sas :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> stack_accepts_suffix gr sk ts
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> stack_accepts_suffix gr sk' ts'. 
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca'
           hc hk hn hp hm hw' hr hs.
    unfold step in hs; dmeqs h; tc; inv hs.
    - appl_fpaa; eapply return_preserves_sas; eauto; auto.
    - eapply consume_preserves_sas; eauto; auto.
    - eapply push_succ_preserves_sas; eauto.
    - eapply push_ambig_preserves_sas; eauto.
  Qed.

  (** If the stack accepts the current suffix, [step] cannot produce a [step_reject]; acceptance rules out every rejection case. *)
  Lemma sas__step_neq_reject :
    forall gr hw rm cm sk ts vi un ca hc hk s,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> stack_accepts_suffix gr sk ts
      -> step gr hw rm cm sk ts vi un ca hc hk <> step_reject s.
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk s
           hn hr hm hw' hsas hs.
    unfold step in hs; dmeqs h; tc; inv hs; sis.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & heq'); subst; sis; rew_anr; subst.
      inv hd.
    - pose proof hsas as hsas'.
      destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      destruct hl as (wsuf' & wsuf'' & vs_suf' & p & f & heq & hd' & hm' & hp' & hl); subst.
      appl_fpaa.
      eapply sas_failed_predicate_contra; eauto.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      symmetry in heq; apply app_eq_nil in heq; destruct heq; subst.
      eapply svd_terminal_head_contra; eauto.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl).
      apply svd_inv_terminal_head in hd.
      destruct hd as (v & ts' & heq'); subst; sis.
      inv_cons_tokens_eq; tc.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      destruct vs_suf as (v_suf, vs_suf).
      eapply svd_inv_nonterminal_head with
          (v'  := v_suf)
          (vs' := vs_suf)
          (heq := eq_refl) in hd; eauto.
      destruct hd as (ts' & ts'' & heq & hh & ht); subst.
      inv_sv hh hm' hd' hp'.
      (* lemma *)
      red in hr.
      destruct hr as (_ & _ & hrc).
      red in hrc.
      apply pm_mapsto_in in hm'.
      apply hrc in hm'.
      destruct hm' as (yss & hm' & hi).
      apply NMF.find_mapsto_iff in hm'; tc.
    - eapply sas_adaptive_predict_neq_reject; eauto.
  Qed.

  (** Internal induction step: if [stack_accepts_suffix] holds, [multistep] never returns [result_reject]; proved over the accessibility relation. *)
  Lemma sas__multistep_doesn't_reject' :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (sk     : parser_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (hk     : stack_pushes_from_keyset rm sk)
           (a'     : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (s      : string),
      tri = parser_meas rm sk ts vi
      -> no_left_recursion gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> stack_accepts_suffix gr sk ts
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb a' <> result_reject _ s.
  Proof.
    intros gr hw rm hr cm x tri a'.
    induction a' as [tri hlt IH].
    intros sk ts vi un ca hc hk hb a s ? hn hcm hw' hg hm; subst. 
    apply multistep_cases in hm.
    destruct hm as [hs | (sk' & ts' & vi' & un' & ca' & hc' & hk' & hb' & a'' & hs & hm)]. 
    - eapply sas__step_neq_reject; eauto.
    - eapply IH with (y := parser_meas rm sk' ts' vi'); eauto. 
      + eapply step_parser_meas_lt; eauto. 
      + eapply step_preserves_stack_wf_invar; eauto.  
      + eapply step_preserves_sas; eauto.
  Qed.

  (** Public version: [stack_accepts_suffix] implies [multistep] never rejects, for any valid initial conditions. *)
  Lemma sas_implies_multistep_doesn't_reject :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (sk     : parser_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (a      : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (s      : string),
      no_left_recursion gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> stack_accepts_suffix gr sk ts
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb a <> result_reject _ s.
  Proof.
    intros; eapply sas__multistep_doesn't_reject'; eauto.
  Qed.

  (** If the initial stack accepts the input [w], then [parse] never rejects; the grammar must be non-left-recursive. *)
  Theorem init_state_sas__parser_doesn't_reject :
    forall g Hwf x w s,
      no_left_recursion g
      -> stack_accepts_suffix g (Fr [] tt [NT x], []) w
      -> parse g Hwf x w <> result_reject _ s.
  Proof.
    intros g hw x w s hn hsas hp; unfold parse in hp.
    eapply sas_implies_multistep_doesn't_reject; eauto; simpl; apps.
    apply mk_closure_map_correct.
  Qed.

  (** Completeness: if a semantic value [v] can be derived from [w] under [x], then [parse] returns either [unique] or [ambig] with some value. *)
  Theorem parse_complete :
    forall (g  : grammar)
           (hw : grammar_wf g)
           (x  : nonterminal)
           (w  : list token)
           (v  : nt_semty x),
      no_left_recursion g
      -> sem_value_derivation g (NT x) w v
      -> exists (v' : nt_semty x),
          parse g hw x w = unique _ v'
          \/ parse g hw x w = ambig _ v'.
  Proof.
    intros g hw x w v hn hd.
    destruct (parse g hw x w) as [v' | v' | s | e] eqn:hp; eauto.
    - exfalso.
      eapply init_state_sas__parser_doesn't_reject; eauto.
      red.
      exists w; exists []; exists (v, tt); repeat split; auto; apps.
      apply svd_singleton; auto.
    - exfalso; destruct e.
      + eapply parse_never_reaches_invalid_state; eauto.
      + eapply parse_doesn't_find_left_recursion_in_non_left_recursive_grammar; eauto.
      + eapply parse_never_returns_prediction_error; eauto.
  Qed.
  
End ParserCompleteFn.
