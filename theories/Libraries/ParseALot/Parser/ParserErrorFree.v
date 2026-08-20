(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import ParserSound.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
From Crane.Libraries.ParseALot.Parser Require Import LLPredictionErrorFree.
Import ListNotations.

Module ParserErrorFreeFn (Import D : Defs.T).

  Module Export PS := ParserSoundFn D.

  (* The following three groups of lemmas correspond to the three
   types of parser errors: errors indicating an invalid parser
   state, errors that indicate a left-recursive grammar, and 
   errors that arise during prediction *)

  (* The parser never reaches an invalid state;
   i.e., impossible states really are impossible *)

  (** A well-formed stack can never cause [step] to return [invalid_state]; that constructor is truly unreachable. *)
  Lemma stacks_wf__step_neq_invalid_state :
    forall (gr    : grammar)
           (hw    : grammar_wf gr)
           (rm    : rhs_map)
           (cm    : closure_map)
           (sk    : parser_stack)
           (ts    : list token)
           (vi    : NtSet.t)
           (un    : bool)
           (ca    : cache)
           (hc    : cache_stores_target_results rm cm ca)
           (hk    : stack_pushes_from_keyset rm sk),
      stack_wf gr sk
      -> step gr hw rm cm sk ts vi un ca hc hk <> step_error invalid_state.
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk hw'; unfold not; intros hs. 
    unfold step in hs; dmeqs H; tc; rew_anr; inv hw'; rew_anr.
    eapply fpaa_none_contra; eauto.
  Qed.

  (** [multistep] never produces [result_error _ invalid_state] when the stack is well-formed; inductively proved over the accessibility relation. *)
  Lemma multistep_never_reaches_error_state :
    forall (gr   : grammar)
           (hw   : grammar_wf gr) 
           (rm   : rhs_map)
           (hr   : rhs_map_correct rm gr)
           (cm   : closure_map)
           (x    : nonterminal)
           (tri  : nat * nat * nat)
           (ha   : Acc lex_nat_triple tri)
           (sk   : parser_stack)
           (ts   : list token)
           (vi   : NtSet.t)
           (un   : bool)
           (ca   : cache)
           (hc   : cache_stores_target_results rm cm ca)
           (hk   : stack_pushes_from_keyset rm sk)
           (hb   : bottom_stack_sym_eq_start_sym sk x)
           (ha'  : Acc lex_nat_triple (parser_meas rm sk ts vi)),
      tri = parser_meas rm sk ts vi
      -> stack_wf gr sk
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha' <> result_error _ invalid_state.
  Proof.
    intros gr hw rm hr cm x tri ha'.
    induction ha' as [tri hlt IH].
    intros sk ts vi un ca hc hk hb ha ? hw' hm; subst. 
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply stacks_wf__step_neq_invalid_state; eauto.
    - destruct hm as (sk' & ts' & vi' & un' & ca' & hc' & hk' & hb' & ha' & hs & hm).
      eapply IH in hm; eauto.
      + eapply step_parser_meas_lt; eauto.  
      + eapply step_preserves_stack_wf_invar; eauto.
  Qed.

  (** The top-level [parse] function never returns [result_error _ invalid_state] for any grammar and input. *)
  Lemma parse_never_reaches_invalid_state :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ts  : list token),
      parse gr hw x ts <> result_error _ invalid_state.
  Proof.
    intros g hw x ts hp; unfold parse in hp.
    eapply multistep_never_reaches_error_state in hp; eauto.
    - apply lex_nat_triple_wf.
    - constructor.
  Qed.

  (* The parser doesn't return a "left recursion detected" error
   when given a non-left-recursive grammar *)
  (** The initial stack satisfies the unavailable-nonterminals invariant: no nonterminals are in the visited set at the start. *)
  Lemma unavailable_nts_invar_starts_true :
    forall g x,
      unavailable_nts_are_open_calls g NtSet.empty (Fr [] tt [NT x], []). 
  Proof.
    intros g x; intros x' hi hni; ND.fsetdec.
  Qed.

  (** A [step_k] result preserves the unavailable-nonterminals invariant across return, consume, and push steps. *)
  Lemma step_preserves_unavailable_nts_invar :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      rhs_map_correct rm gr
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> unavailable_nts_are_open_calls gr vi  sk
      -> unavailable_nts_are_open_calls gr vi' sk'.
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hr hs hu.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_unavailable_nts_invar; eauto. 
    - intros x hi hn; ND.fsetdec. 
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptive_predict_succ_in_grammar; eauto.
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptive_predict_ambig_in_grammar; eauto.
      Unshelve.
      all : auto.
  Qed.

  (** If [step] raises [left_recursion x] and the unavailable-nts invariant holds, then [x] is genuinely left-recursive in the grammar. *)
  Lemma step_left_recursion_detection_sound :
    forall gr hw rm cm sk ts vi un ca hc hk x,
      rhs_map_correct rm gr
      -> unavailable_nts_are_open_calls gr vi sk
      -> step gr hw rm cm sk ts vi un ca hc hk = step_error (left_recursion x)
      -> left_recursive gr (NT x).
  Proof.
    intros g hw rm cm sk ts vi un ca hc hk x hp hu hs.
    apply step_left_recursion_facts in hs.
    destruct hs as [hi [[yss hf] [pre [vs [suf [frs heq]]]]]]; subst.
    apply hu in hi; auto.
    - destruct hi as (frs_pre & cr & frs_suf & pre' & vs' & suf' & ? & ? & hf'); subst.
      eapply frnp_grammar_nullable_path; eauto.
    - eapply find_all_nts; eauto.
  Qed.

  (** If [multistep] returns [result_error _ (left_recursion y)], then [y] is truly left-recursive in the grammar. *)
  Lemma multistep_left_recursion_detection_sound :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (tri    : nat * nat * nat)
           (ha     : Acc lex_nat_triple tri)
           (sk     : parser_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (ha'    : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (y      : nonterminal),
      tri = parser_meas rm sk ts vi
      -> unavailable_nts_are_open_calls gr vi sk
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha' = result_error _ (left_recursion y)
      -> left_recursive gr (NT y).
  Proof.
    intros gr hw rm hr cm x tri ha'; induction ha' as [tri hlt IH].
    intros sk ts vi un ca hc hk hb ha y ? hu hm; subst.
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_left_recursion_detection_sound; eauto. 
    - destruct hm as (sk' & ts' & vi' & un' & ca' & hc' & hk' & hb' & ha' & hs & hm).
      eapply IH with (y := parser_meas rm sk' ts' vi'); eauto.
      + eapply step_parser_meas_lt; eauto. 
      + eapply step_preserves_unavailable_nts_invar; eauto. 
  Qed.

  (** If [parse] returns [result_error _ (left_recursion y)], then [y] is genuinely left-recursive in the grammar. *)
  Lemma parse_left_recursion_detection_sound :
    forall gr hw x y ts,
      parse gr hw x ts = result_error _ (left_recursion y)
      -> left_recursive gr (NT y).
  Proof.
    intros g hw x y ts hp; unfold parse in hp.
    eapply multistep_left_recursion_detection_sound in hp; eauto.
    - apply lex_nat_triple_wf.
    - intros x' hi hn; ND.fsetdec.
  Qed.
  
  (** [parse] never reports left recursion when the grammar has none; soundness of the detection entails this. *)
  Lemma parse_doesn't_find_left_recursion_in_non_left_recursive_grammar :
    forall (g   : grammar)
           (hw  : grammar_wf g)
           (x y : nonterminal)
           (ts  : list token),
      no_left_recursion g
      -> parse g hw x ts <> result_error _ (left_recursion y).
  Proof.
    intros g hw x y ts hn hp.
    apply parse_left_recursion_detection_sound in hp; firstorder.
  Qed.

  (* Errors never arise during prediction, given a non-left-recursive grammar *)

  (** With a non-left-recursive, well-formed grammar and correct closure map, [step] never produces a [prediction_err]. *)
  Lemma step_never_returns_prediction_error :
    forall gr hw rm cm sk ts vi un ca hc hk e,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> step gr hw rm cm sk ts vi un ca hc hk <> step_error (prediction_err e).
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk e hn hp hm hw' hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
    eapply adaptive_predict_neq_error; eauto.
  Qed.
  
  (** [multistep] never produces [result_error _ (prediction_err e)] when the grammar is non-left-recursive and the closure map is correct. *)
  Lemma multistep_never_returns_prediction_error :
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
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (a'     : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (e      : prediction_error),
      no_left_recursion gr
      -> closure_map_correct gr cm 
      -> tri = parser_meas rm sk ts vi
      -> stack_wf gr sk
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb a' <> result_error _ (prediction_err e).
  Proof.
    intros gr hw rm hr cm x tri ha.
    induction ha as [tri hlt IH].
    intros sk ts vi un ca hc hk hb ha' e hn hcm ? hw' hm; subst.
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_never_returns_prediction_error in hs; eauto.
    - destruct hm as (sk' & ts' & av' & un' & ca' & hc' & hk' & hb' & a'' & hs & hm). 
      eapply IH in hm; eauto.
      + eapply step_parser_meas_lt; eauto. 
      + eapply step_preserves_stack_wf_invar; eauto. 
  Qed.

  (** The top-level [parse] function never returns a [prediction_err] for a non-left-recursive grammar. *)
  Lemma parse_never_returns_prediction_error :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ts  : list token)
           (e   : prediction_error),
      no_left_recursion gr
      -> parse gr hw x ts <> result_error _ (prediction_err e).
  Proof.
    intros g hw x ts e hn hp; unfold parse in hp.
    eapply multistep_never_returns_prediction_error in hp; eauto.
    - apply lex_nat_triple_wf.
    - apply mk_closure_map_correct.
    - constructor.
  Qed.

End ParserErrorFreeFn.
