(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import LLPrediction.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module LLPredictionErrorFreeFn (Import D : Defs.T).

  Module Export LLP := LLPredictionFn D.

  (* BREAKING THIS INTO TWO GROUPS OF LEMMAS
   FOR THE TWO TYPES OF PREDICTION ERRORS *)

  (* SP INVALID STATE CASE *)

  (** A stack is stable if it has either an empty suffix (final) or a terminal at the head; closure won't step further. *)
  Inductive stable_config : parser_stack -> Prop :=
  | sc_empty :
      forall pre vs,
      stable_config (Fr pre vs [], [])
  | sc_terminal :
      forall pre vs a suf frs,
        stable_config (Fr pre vs (T a :: suf), frs).

  Hint Constructors stable_config : core.

  (** Requires [stable_config] for every subparser in a list. *)
  Definition all_stacks_stable sps :=
    forall sp, In sp sps -> stable_config sp.(stack).

  (** A well-formed stack guarantees [cstep] never yields [sp_invalid_state]: invalid cases are unreachable. *)
  Lemma cstep_never_returns_sp_invalid_state :
    forall gr hw rm vi sp,
      stack_wf gr sp.(stack)
      -> cstep gr hw rm vi sp <> cstep_error sp_invalid_state.
  Proof.
    intros gr hw rm vi sp hw'; unfold not; intros hs.
    unfold cstep in hs; dmeqs H; tc; inv hw'.
    rew_anr.
    match goal with
    | H : find_predicate_and_action _ _ _ = None |- _ =>
      apply fpaa_cases in H
    end.
    eapply in_find_contra; eauto.
  Qed.

  (** [llc] never returns [sp_invalid_state] on a well-formed stack, by induction on the termination measure. *)
  Lemma llc_never_returns_sp_invalid_state :
    forall (gr   : grammar)
           (hw   : grammar_wf gr)
           (rm   : rhs_map)
           (pr   : nat * nat)
           (ha   : Acc lex_nat_pair pr)
           (vi   : NtSet.t)
           (sp   : subparser)
           (hk   : sp_pushes_from_keyset rm sp)
           (ha'  : Acc lex_nat_pair (ll_meas rm vi sp)),
      pr = ll_meas rm vi sp
      -> rhs_map_correct rm gr
      -> stack_wf gr sp.(stack)
      -> llc gr hw rm vi sp hk ha' <> inl sp_invalid_state.
  Proof.
    intros gr hw rm pr ha'. 
    induction ha' as [pr hlt IH].
    intros vi sp hk ha heq hc hw'; unfold not; intros hs; subst.
    apply llc_error_cases in hs.
    destruct hs as [hs | [sps [av' [hs [crs [heq heq']]]]]]; subst.
    - eapply cstep_never_returns_sp_invalid_state; eauto.
    - apply aggr_closure_results_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_wf_invar; eauto.
  Qed.
  
  (** [ll_closure] never yields [sp_invalid_state] when all input stacks are well-formed. *)
  Lemma ll_closure_never_returns_sp_invalid_state :
    forall gr hw rm sps hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> ll_closure gr hw rm sps hk <> inl sp_invalid_state.
  Proof.
    intros gr hw rm sps hk hp hw'; unfold not; intros hc.
    unfold ll_closure in hc.
    apply aggr_closure_results_error_in_input in hc.
    eapply dmap_in in hc; eauto.
    destruct hc as [sp [hi [_ hc]]].
    eapply llc_never_returns_sp_invalid_state; eauto.
    apply lex_nat_pair_wf.
  Qed.

  (** [ll_start_state] never yields [sp_invalid_state] when the initial caller frame is well-formed. *)
  Lemma ll_start_state_never_returns_sp_invalid_state :
    forall gr hw rm fr frs pre vs x suf hk,
      rhs_map_correct rm gr
      -> stack_wf gr (fr, frs)
      -> fr = Fr pre vs  (NT x :: suf)
      -> ll_start_state gr hw rm pre vs x suf frs hk <> inl sp_invalid_state.
  Proof.
    intros gr hw rm fr frs pre vs x suf hk hr hw' ?; unfold not; intros hss. 
    eapply ll_closure_never_returns_sp_invalid_state; eauto.
    intros sp hi.
    unfold ll_init_sps in hi.
    apply in_map_iff in hi.
    destruct hi as [rhs [heq' hi]]; subst; simpl.
    (* LEMMA *)
    clear hss; inv hw'; sis; subst.
    - destruct vs.
      wf_upper_nil. 
      eapply rhss_for_in_iff; eauto.
    - wf_upper_nil. 
      eapply rhss_for_in_iff; eauto.
  Qed.

  (** [handle_final_subparsers] only returns [pred_succ], [pred_ambig], or [pred_reject], never [pred_error]. *)
  Lemma handle_final_subparsers_never_returns_error :
    forall sps e,
      handle_final_subparsers sps <> pred_error e.
  Proof.
    intros sps e; unfold not; intro hh.
    unfold handle_final_subparsers in hh; dms; tc.
  Qed.

  (** A stable subparser never causes [move_sp] to return [sp_invalid_state]. *)
  Lemma move_sp_never_returns_sp_invalid_state_for_ready_sp :
    forall t sp,
      stable_config sp.(stack)
      -> move_sp t sp <> move_error sp_invalid_state.
  Proof.
    intros t sp hr; unfold not; intros hm.
    unfold move_sp in hm.
    dms; tc; sis; inv hr.
  Qed.

  (** Moving a list of stable subparsers never yields [sp_invalid_state]. *)
  Lemma move_never_returns_sp_invalid_state_for_ready_sps :
    forall t sps,
      all_stacks_stable sps
      -> move t sps <> inl sp_invalid_state.
  Proof.
    intros t sps ha; unfold not; intros hm.
    unfold move in hm.
    apply aggr_move_results_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply move_sp_never_returns_sp_invalid_state_for_ready_sp; eauto.
  Qed.

  (** [move_sp] preserves the [stack_wf] invariant: the post-move stack is still well-formed. *)
  Lemma move_sp_preserves_stack_wf_invar :
    forall g t sp sp',
      stack_wf g sp.(stack)
      -> move_sp t sp = move_succ sp'
      -> stack_wf g sp'.(stack).
  Proof.
    intros g t sp sp' hw hm.
    unfold move_sp in hm; dms; tc; inv hm; sis.
    inv_fwf hw hi hw'.
    rewrite app_cons_group_l in hi; eauto.
  Qed.

  (** [move] preserves [stack_wf] for all subparsers that survive the move. *)
  Lemma move_preserves_stack_wf_invar :
    forall g t sps sps',
      all_stacks_wf g sps
      -> move t sps = inr sps'
      -> all_stacks_wf g sps'.
  Proof.
    intros g t sps sps' ha hm.
    unfold all_stacks_wf.
    intros sp' hi.
    unfold move in hm.
    eapply aggr_move_results_succ_in_input in hm; eauto.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi']].
    eapply move_sp_preserves_stack_wf_invar; eauto.
  Qed.

  (** [llc] preserves [stack_wf] for every subparser it produces, by well-founded induction. *)
  Lemma llc_preserves_stack_wf_invar :
    forall gr hw rm pr (a : Acc lex_nat_pair pr) vi sp sp' hk a' sps',
      pr = ll_meas rm vi sp
      -> rhs_map_correct rm gr
      -> stack_wf gr sp.(stack)
      -> llc gr hw rm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> stack_wf gr sp'.(stack).
  Proof.
    intros gr hw rm pr a'.
    induction a' as [pr hlt IH]; intros vi sp sp' hk a sps' heq hp hw' hs hi; subst.
    apply llc_success_cases in hs.
    destruct hs as [[hd heq] | [sps'' [av' [hs [crs [heq heq']]]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggr_closure_results_succ_in_input in heq'; eauto.
      destruct heq' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_wf_invar; eauto.
  Qed.
  
  (** [ll_closure] preserves [stack_wf] for all subparsers it produces. *)
  Lemma ll_closure_preserves_stack_wf_invar :
    forall gr hw rm sps hk sps',
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> ll_closure gr hw rm sps hk = inr sps'
      -> all_stacks_wf gr sps'.
  Proof.
    intros gr hw rm sps hk sps' hp ha hc.
    unfold ll_closure in hc.
    unfold all_stacks_wf.
    intros sp' hi.
    eapply aggr_closure_results_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply llc_preserves_stack_wf_invar; eauto.
    apply lex_nat_pair_wf.
  Qed.

  (** When [cstep] returns [cstep_done] on a well-formed stack, the subparser is in a stable configuration. *)
  Lemma cstep_done_stable_config :
    forall gr hw rm vi sp,
      stack_wf gr sp.(stack)
      -> cstep gr hw rm vi sp = cstep_done
      -> stable_config sp.(stack).
  Proof.
    intros gr hw rm vi sp hw' hs.
    unfold cstep in hs; dms; tc; sis; inv hw'; auto.
  Qed.

  (** Every subparser produced by [llc] on a well-formed stack is in a stable configuration. *)
  Lemma sp_in_llc_result_stable_config :
    forall gr hw rm pr (a : Acc lex_nat_pair pr) vi sp sp' hk a' sps',
      pr = ll_meas rm vi sp
      -> rhs_map_correct rm gr
      -> stack_wf gr sp.(stack)
      -> llc gr hw rm  vi sp hk a' = inr sps'
      -> In sp' sps'
      -> stable_config sp'.(stack).
  Proof.
    intros gr hw rm pr a'.
    induction a' as [pr hlt IH]; intros vi sp sp' hk a sps' heq hp hw' hs hi; subst.
    apply llc_success_cases in hs.
    destruct hs as [[hd heq] | [sps'' [av' [hs [crs [heq heq']]]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
      eapply cstep_done_stable_config; eauto.
    - eapply aggr_closure_results_succ_in_input in heq'; eauto.
      destruct heq' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_wf_invar; eauto.
  Qed.

  (** [ll_closure] always produces a stable set of subparsers from well-formed inputs. *)
  Lemma all_stacks_stable_after_closure :
    forall gr hw rm sps hk sps',
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> ll_closure gr hw rm sps hk = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros gr hw rm sps hk sps' hp hw' hc.
    unfold ll_closure in hc.
    unfold all_stacks_stable.
    intros sp' hi.
    eapply aggr_closure_results_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply sp_in_llc_result_stable_config; eauto.
    apply lex_nat_pair_wf.
  Qed.

  (** [ll_target] never yields [sp_invalid_state] when inputs are well-formed and stable. *)
  Lemma ll_target_never_returns_sp_invalid_state :
    forall gr hw rm t sps hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> ll_target gr hw rm t sps hk <> inl sp_invalid_state.
  Proof.
    intros gr hw rm t sps hk hp hw' hs; unfold not; intros ht.
    apply ll_target_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply move_never_returns_sp_invalid_state_for_ready_sps; eauto.
    - eapply move_preserves_stack_wf_invar in hm; eauto.
      eapply ll_closure_never_returns_sp_invalid_state; eauto.
  Qed.

  (** [ll_target] preserves [stack_wf] for all subparsers it produces. *)
  Lemma ll_target_preserves_stacks_wf_invar :
    forall gr hw rm t sps hk sps',
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> ll_target gr hw rm t sps hk = inr sps'
      -> all_stacks_wf gr sps'.
  Proof.
    intros gr hw rm t sps hk sps' hp hw' ht.
    apply ll_target_cases in ht.
    destruct ht as [sps'' [hk' [hm hc]]].
    eapply move_preserves_stack_wf_invar in hm; eauto.
    eapply ll_closure_preserves_stack_wf_invar; eauto.
  Qed.

  (** [ll_target] produces only stable subparsers when given well-formed, stable inputs. *)
  Lemma ll_target_preserves_stacks_stable_invar :
    forall gr hw rm t sps hk sps',
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> ll_target gr hw rm t sps hk = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros gr hw rm t sps hk sps' hp hw' hs ht; unfold ll_target in ht.
    apply ll_target_cases in ht.
    destruct ht as [sps'' [hk' [hm hc]]].
    eapply move_preserves_stack_wf_invar in hm; eauto.
    eapply all_stacks_stable_after_closure; eauto.
  Qed.

  (** [ll_predict'] never returns [pred_error sp_invalid_state] given well-formed, stable inputs. *)
  Lemma ll_predict'_never_returns_sp_invalid_state :
    forall gr hw rm ts sps hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> ll_predict' gr hw rm sps ts hk <> pred_error sp_invalid_state.
  Proof.
    intros gr hw rm ts; induction ts as [| (a,l) ts IH]; intros sps hk hp ha ha';
      unfold not; intros hl; sis.
    - eapply handle_final_subparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps']; tc.
      dm; tc.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [ht | [sps'' [ht hl]]].
      + eapply ll_target_never_returns_sp_invalid_state; eauto.
      + eapply IH in hl; eauto.
        * eapply ll_target_preserves_stacks_wf_invar; eauto.
        * eapply ll_target_preserves_stacks_stable_invar; eauto.
  Qed.

  (** [ll_start_state] preserves [stack_wf] for all subparsers it produces. *)
  Lemma ll_start_state_preserves_stacks_wf_invar :
    forall gr hw rm fr frs pre vs x suf hk sps,
      rhs_map_correct rm gr
      -> stack_wf gr (fr, frs)
      -> fr = Fr pre vs (NT x :: suf)
      -> ll_start_state gr hw rm pre vs x suf frs hk = inr sps
      -> all_stacks_wf gr sps.
  Proof.
    intros gr hw rm  [pre' vs' suf'] frs o x suf hk sps hp hw' heq hs; sis; subst.
    eapply ll_closure_preserves_stack_wf_invar; eauto.
    unfold all_stacks_wf; intros sp hi.
    eapply ll_init_sps_preserves_stack_wf_invar; eauto.
  Qed.

  (** After [ll_start_state] succeeds, all produced subparsers are in stable configurations. *)
  Lemma ll_start_state_all_stacks_stable :
    forall gr hw rm cr pre vs x suf frs hk sps,
      rhs_map_correct rm gr
      -> cr = Fr pre vs (NT x :: suf)
      -> stack_wf gr (cr, frs)
      -> ll_start_state gr hw rm pre vs x suf frs hk = inr sps
      -> all_stacks_stable sps.
  Proof.
    intros gr hw rm cr pre vs x suf frs hk sps hp ? hw' hs sp hi.
    eapply all_stacks_stable_after_closure; eauto.
    eapply ll_init_sps_preserves_stack_wf_invar; eauto.
  Qed.

  (** [ll_predict] never returns [pred_error sp_invalid_state] given a well-formed caller frame. *)
  Lemma ll_predict_never_returns_sp_invalid_state :
    forall gr hw rm fr frs pre vs x suf ts hk,
      rhs_map_correct rm gr
      -> stack_wf gr (fr, frs)
      -> fr = Fr pre vs (NT x :: suf)
      -> ll_predict gr hw rm pre vs x suf frs ts hk <> pred_error sp_invalid_state.
  Proof.
    intros gr hw rm fr frs pre vs x suf ts hk hp hw' heq; unfold not; intros hl.
    apply ll_predict_cases in hl.
    destruct hl as [hl | [sps [hs hl]]].
    - eapply ll_start_state_never_returns_sp_invalid_state; eauto.
    - eapply ll_predict'_never_returns_sp_invalid_state; eauto.
      + eapply ll_start_state_preserves_stacks_wf_invar; eauto. 
      + eapply ll_start_state_all_stacks_stable; eauto.
  Qed.

  (* LEFT RECURSION CASE *)

  (** A nonterminal found in the rhs_map must appear in the set of all grammar nonterminals. *)
  Lemma find_all_nts :
    forall g rm x ys,
      rhs_map_correct rm g
      -> NM.find x rm = Some ys
      -> NtSet.In x (all_nts g).
  Proof.
    intros g rm x ys [hs [hs' hc]] hi.
    apply all_nts_lhss_iff.
    apply find_some__in in hi.
    apply hs in hi.
    destruct hi as [ys' hi].
    eapply production_lhs_in_lhss; eauto.
  Qed.

  (** If [cstep] returns [sp_left_recursion x], then [x] is in [vi] and the frame has [NT x] at its suffix head. *)
  Lemma cstep_left_recursion_facts :
    forall gr hw rm vi pred fr frs x,
      rhs_map_correct rm gr
      -> cstep gr hw rm vi (Sp pred (fr, frs)) = cstep_error (sp_left_recursion x)
      -> NtSet.In x vi
         /\ NtSet.In x (all_nts gr)
         /\ exists pre vs suf,
             fr = Fr pre vs (NT x :: suf).
  Proof.
    intros gr hw rm vi pred fr frs x hp hs.
    unfold cstep in hs; repeat dmeq h; tc; inv hs; sis.
    repeat split; eauto.
    - apply NF.mem_iff; auto. 
    - eapply find_all_nts; eauto.
  Qed.

  (** In a non-left-recursive grammar, [cstep] never returns [sp_left_recursion x]: the unavailable-nts invariant rules it out. *)
  Lemma cstep_never_finds_left_recursion :
    forall gr hw rm vi sp x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> unavailable_nts_invar gr vi sp
      -> cstep gr hw rm vi sp <> cstep_error (sp_left_recursion x).
  Proof.
    intros gr hw rm vi [pred (fr, frs)] x hn hc hu; unfold not; intros hs.
    pose proof hs as hs'.
    eapply cstep_left_recursion_facts in hs'; eauto.
    destruct hs' as [hn' [hi [pre [vs [suf' heq]]]]]; subst.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & ? & ? & hf); subst.
    eapply frnp_grammar_nullable_path in hf; eauto.
    firstorder.
  Qed.

  (** [llc] never yields [sp_left_recursion] in a non-left-recursive grammar, by induction on the measure. *)
  Lemma llc_never_finds_left_recursion :
    forall gr hw rm pr (a : Acc lex_nat_pair pr) vi sp hk a' x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> unavailable_nts_invar gr vi sp
      -> pr = ll_meas rm vi sp
      -> llc gr hw rm vi sp hk a' <> inl (sp_left_recursion x).
  Proof.
    intros gr hw rm pr a'; induction a' as [pr hlt IH]. 
    intros vi sp hk a x hn hc hu heq; unfold not; intros hs; subst.
    apply llc_error_cases in hs.
    destruct hs as [hs | [sps [av' [hs [crs [hc' ha]]]]]]; subst.
    - eapply cstep_never_finds_left_recursion; eauto.
    - apply aggr_closure_results_error_in_input in ha.
      eapply dmap_in in ha; eauto.
      destruct ha as [sp' [hi [hi' hs']]].
      eapply IH with (sp := sp'); eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_unavailable_nts_invar; eauto.
  Qed.

  (** [ll_closure] never yields [sp_left_recursion] in a non-left-recursive grammar. *)
  Lemma closure_never_finds_left_recursion :
    forall gr hw rm sps hk x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> ll_closure gr hw rm sps hk <> inl (sp_left_recursion x).
  Proof.
    intros gr hw rm sps hk x hn hp; unfold not; intros hc.
    unfold ll_closure in hc.
    apply aggr_closure_results_error_in_input in hc.
    eapply dmap_in in hc; eauto.
    destruct hc as [[pred (fr, frs)] [hi [_ hs]]].
    eapply llc_never_finds_left_recursion; eauto.
    - apply lex_nat_pair_wf.
    - apply unavailable_nts_empty.
  Qed.        

  (** [move_sp] structurally cannot return [sp_left_recursion]: the move operation never examines nonterminals. *)
  Lemma move_sp_never_returns_sp_left_recursion :
    forall t sp x,
      move_sp t sp <> move_error (sp_left_recursion x).
  Proof.
    intros t sp x; unfold not; intros hm.
    unfold move_sp in hm; dms; tc.
  Qed.

  (** [move] never returns [sp_left_recursion]: the move operation only matches terminals, not nonterminals. *)
  Lemma move_never_returns_sp_left_recursion :
    forall t sps x,
      move t sps <> inl (sp_left_recursion x).
  Proof.
    intros t sps x; unfold not; intros hm.
    unfold move in hm.
    apply aggr_move_results_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply move_sp_never_returns_sp_left_recursion; eauto.
  Qed.

  (** [ll_target] never yields [sp_left_recursion] in a non-left-recursive grammar: neither move nor closure can. *)
  Lemma ll_target_never_returns_sp_left_recursion :
    forall gr hw rm a sps hk x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> ll_target gr hw rm a sps hk <> inl (sp_left_recursion x).
  Proof.
    intros gr hw rm a sps hk x hn hp; unfold not; intros ht.
    apply ll_target_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply move_never_returns_sp_left_recursion; eauto.
    - eapply closure_never_finds_left_recursion; eauto.
  Qed.
  
  (** [ll_predict'] never returns [pred_error (sp_left_recursion x)] in a non-left-recursive grammar. *)
  Lemma ll_predict'_never_returns_sp_left_recursion :
    forall gr hw rm ts sps hk x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> ll_predict' gr hw rm sps ts hk <> pred_error (sp_left_recursion x).
  Proof.
    intros gr hw rm ts; induction ts as [| (a,l) ts IH];
      intros sps hk x hn hp hl; sis.
    - eapply handle_final_subparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps']; tc; dm; tc.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [ht | [sps'' [ht hl]]].
      + eapply ll_target_never_returns_sp_left_recursion; eauto.
      + eapply IH in hl; eauto.
  Qed.

  (** [ll_predict] never returns [pred_error (sp_left_recursion x')] in a non-left-recursive grammar. *)
  Lemma ll_predict_never_returns_sp_left_recursion :
    forall gr hw rm pre vs x suf frs ts hk x',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> ll_predict gr hw rm pre vs x suf frs ts hk <> pred_error (sp_left_recursion x').
  Proof.
    intros gr hw rm pre vs x suf frs ts hk x' hn hp hl.
    apply ll_predict_cases in hl.
    destruct hl as [hs | [sps [hs hp']]].
    - eapply closure_never_finds_left_recursion; eauto.
    - eapply ll_predict'_never_returns_sp_left_recursion; eauto.
  Qed.
  
  (* For convenience, some lemmas that generalize over both
     types of prediction errors *)

  (** [ll_target] never returns any prediction error under the standard well-formedness conditions. *)
  Lemma ll_target_never_returns_error :
    forall gr hw rm a sps hk e,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> ll_target gr hw rm a sps hk <> inl e.
  Proof.
    unfold not; intros gr hw rm a sps hk e hn hc hw' hs hl; destruct e.
    - eapply ll_target_never_returns_sp_invalid_state ; eauto.
    - eapply ll_target_never_returns_sp_left_recursion; eauto.
  Qed.

  (** [ll_start_state] never returns any prediction error given a well-formed, non-left-recursive grammar. *)
  Lemma ll_start_state_never_returns_error :
    forall gr hw rm pre vs x suf fr frs hk e,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (fr, frs)
      -> fr = Fr pre vs (NT x :: suf)
      -> ll_start_state gr hw rm pre vs x suf frs hk <> inl e.
  Proof.
    intros gr hw rm pre vs x suf fr frs hk e hn hp hw' ? hs; subst; destruct e.
    - eapply ll_start_state_never_returns_sp_invalid_state; eauto.
    - eapply closure_never_finds_left_recursion; eauto.
  Qed.

  (** [ll_predict'] never returns any [pred_error] given well-formed, stable, non-left-recursive conditions. *)
  Lemma ll_predict'_never_returns_error :
    forall gr hw rm sps ts hk e,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> ll_predict' gr hw rm sps ts hk <> pred_error e.
  Proof.
    intros gr hw rm sps ts hk e hn hp hw' hs hl; destruct e.
    - eapply ll_predict'_never_returns_sp_invalid_state ; eauto.
    - eapply ll_predict'_never_returns_sp_left_recursion; eauto.
  Qed.
  
  (** The main error-freedom theorem: [ll_predict] never returns [pred_error] on a well-formed, non-left-recursive grammar. *)
  Lemma ll_predict_never_returns_error :
    forall gr hw rm pre vs x suf fr frs ts hk e,
      fr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (fr, frs)
      -> ll_predict gr hw rm pre vs x suf frs ts hk <> pred_error e.
  Proof.
    unfold not; intros gr hw rm pre vs x suf fr frs ts hk e ? hn hp hw' hl; subst; destruct e.
    - eapply ll_predict_never_returns_sp_invalid_state;  eauto.
    - eapply ll_predict_never_returns_sp_left_recursion; eauto.
  Qed.

End LLPredictionErrorFreeFn. 
