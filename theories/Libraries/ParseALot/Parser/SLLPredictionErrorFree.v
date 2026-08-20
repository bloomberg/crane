(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import SLLOptimizationSound.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module SllPredictionErrorFreeFn (Import D : Defs.T).

  Module Export SLLS := SllOptimizationSoundFn D.

  (* A more permissive well-formedness invariant that
     places fewer restrictions on the bottom frame *)
  (** Well-formedness for SLL frame stacks requiring only the non-bottom frames to be consistent with the grammar. *)
  Inductive frames_top_wf (g : grammar) : list sll_frame -> Prop :=
  | twf_bottom :
      forall o ys,
        frames_top_wf g [sll_fr o ys]
  | twf_upper :
      forall x pre' suf suf' o frs,
        PM.In (x, pre' ++ suf') g
        -> frames_top_wf g (sll_fr o (NT x :: suf) :: frs)
        -> frames_top_wf g (sll_fr (Some x) suf' :: sll_fr o (NT x :: suf) :: frs).

  Hint Constructors frames_top_wf : core.

  (* invert an sframes_top_wf judgment, naming the hypotheses hi and hw' *)
  Ltac inv_twf hw  hi hw' :=
    inversion hw as [ ? ? | ? ? ? ? ? ? hi hw']; subst; clear hw.

  Ltac twf_upper_nil := eapply twf_upper with (pre' := []); sis; eauto. 

  (* The stack top well-formedness predicate *)
  (** Lifts frames_top_wf to an SLL stack pair. *)
  Definition stack_top_wf (g : grammar) (stk : sll_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_top_wf g (fr :: frs)
    end.

  (** Requires every subparser in a list to have a well-formed stack top. *)
  Definition all_stack_tops_wf g sps :=
    forall sp, In sp sps -> stack_top_wf g (sll_stk sp).

  (*
  Lemma suffix_frames_wf__frames_top_wf :
    forall g frs,
      suffix_frames_wf g frs -> frames_top_wf g frs.
  Proof.
    intros g frs hw; induction hw; eauto.
  Qed.
  
  Lemma suffix_stack_wf__stack_top_wf :
    forall g fr frs,
      suffix_stack_wf g (fr, frs) -> stack_top_wf g (fr, frs).
  Proof.
    intros; apply suffix_frames_wf__frames_top_wf; auto.
  Qed.
   *)
  
  (** Returning from a completed NT frame preserves the frames_top_wf invariant. *)
  Lemma return_preserves_frames_top_wf :
    forall g o o' suf_cr x frs,
      frames_top_wf g (sll_fr o [] :: sll_fr o' (NT x :: suf_cr) :: frs)
      -> frames_top_wf g (sll_fr o' suf_cr :: frs).
  Proof.
    intros g o o' suf_cr x locs hw.
    inv_twf hw  hi hw'.
    inv_twf hw' hi' hw''; auto.
    rewrite app_cons_group_l in hi'; eauto.
  Qed.

  (** Pushing a new NT frame for a grammar production preserves frames_top_wf. *)
  Lemma push_preserves_frames_top_wf :
    forall g o suf x rhs frs,
      PM.In (x, rhs) g
      -> frames_top_wf g (sll_fr o (NT x :: suf) :: frs)
      -> frames_top_wf g (sll_fr (Some x) rhs :: sll_fr o (NT x :: suf) :: frs).
  Proof.
    intros; twf_upper_nil. 
  Qed.
       
  (** Consuming a terminal from the top frame preserves frames_top_wf. *)
  Lemma consume_preserves_frames_top_wf_invar :
    forall g o suf a frs,
      frames_top_wf g (sll_fr o (T a :: suf) :: frs)
      -> frames_top_wf g (sll_fr o suf :: frs).
  Proof.
    intros g o suf a frs hw.
    inv_twf hw  hi hw'; auto.
    rewrite app_cons_group_l in hi; eauto.
  Qed.

  (** A successful sll_move_sp step preserves the stack top well-formedness invariant. *)
  Lemma sll_move_sp_preserves_stack_top_wf :
    forall g t sp sp',
      stack_top_wf g sp.(sll_stk)
      -> sll_move_sp t sp = move_succ sp'
      -> stack_top_wf g sp'.(sll_stk).
  Proof.
    intros g t sp sp' hw hm.
    unfold sll_move_sp in hm; dms; tc; inv hm; sis.
    eapply consume_preserves_frames_top_wf_invar; eauto.
  Qed.

  (** sll_move preserves stack top well-formedness across the whole subparser list. *)
  Lemma sll_move_preserves_stack_top_wf :
    forall g t sps sps',
      all_stack_tops_wf g sps
      -> sll_move t sps = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g t sps sps' ha hm sp' hi.
    eapply aggr_move_results_succ_in_input in hm; eauto.
    apply in_map_iff in hm; destruct hm as [sp [hm hi']].
    eapply sll_move_sp_preserves_stack_top_wf ; eauto.
  Qed.

  (** sll_cstep preserves stack top well-formedness for every produced subparser. *)
  Lemma sll_cstep_preserves_stack_top_wf :
    forall g rm sp sp' sps' av av',
      rhs_map_correct rm g
      -> stack_top_wf g sp.(sll_stk)
      -> sll_cstep rm av sp = cstep_k av' sps'
      -> In sp' sps'
      -> stack_top_wf g sp'.(sll_stk).
  Proof.
    intros g pm sp sp' sps' av av' hc hw hs hi.
    unfold sll_cstep in hs; dms; tc; sis; inv hs.
    - apply in_singleton_eq in hi; subst; sis.
      eapply return_preserves_frames_top_wf; eauto.
    - inv hi.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
      apply push_preserves_frames_top_wf; auto.
      eapply rhss_for_in_iff; eauto.
  Qed.

  (* refactor *)
  (** Subparsers produced by sim_return have well-formed stack tops, since their frames come from the closure map. *)
  Lemma sim_return_stack_top_wf :
    forall g cm sp sp' sps',
      closure_map_correct g cm
      -> sim_return cm sp = Some sps'
      -> In sp' sps'
      -> stack_top_wf g (sll_stk sp').
  Proof.
    intros g cm [pr (fr, frs)] sp' sps' [hs hc] hr hi.
    pose proof hr as heq; apply sim_return_stack_shape in heq.
    destruct heq as [x heq]; inv heq; inv hr.
    apply in_map_iff in hi. destruct hi as [fr [heq hi]]; subst; sis.
    unfold dest_frames in hi.
    dmeq hf; tc.
    - (* lemma *)
      apply FMF.find_mapsto_iff in hf.
      eapply hs in hi; eauto.
      destruct hi as [hm hst].
      destruct fr as [[y |] [| [a | y'] suf]]; inv hst; auto.
    - inv hi.
  Qed.

  (** sllc preserves stack top well-formedness for all output subparsers. *)
  Lemma sllc_preserves_suffix_stack_wf_invar :
    forall gr rm cm pr (a : Acc lex_nat_pair pr) vi sp hk sp' a' sps',
      pr = sll_meas rm vi sp
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_top_wf gr sp.(sll_stk)
      -> sllc rm cm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> stack_top_wf gr sp'.(sll_stk).
  Proof.
    intros g pm cm pr a'.
    induction a' as [pr hlt IH]; intros vi sp hk sp' a sps' heq hp hc hw hs hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs' ?] | [ys' [avy' [hs' [? [? ha']]]]]]]]; subst.
    - eapply sim_return_stack_top_wf; eauto.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggr_closure_results_succ_in_input in ha'; eauto.
      destruct ha' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply sll_cstep_meas_lt; eauto.
      + eapply sll_cstep_preserves_stack_top_wf; eauto.
  Qed.

  (** sll_closure preserves the all_stack_tops_wf invariant across the subparser list. *)
  Lemma sll_closure_preserves_stack_top_wf :
    forall g pm cm sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sll_closure pm cm sps hk = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g pm cm sps hk sps' hp hc ha hs sp' hi.
    eapply aggr_closure_results_succ_in_input in hs; eauto.
    destruct hs as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply sllc_preserves_suffix_stack_wf_invar; eauto.
    apply lex_nat_pair_wf.
  Qed.
  
  (** sll_target (move + closure) preserves all_stack_tops_wf. *)
  Lemma sll_target_preserves_stack_top_wf :
    forall g pm cm a sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sll_target pm cm a sps hk = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g pm cm a sps hk sps' hp hc hw ht.
    apply sll_target_cases in ht.
    destruct ht as [sps'' [hk' [hm hc']]].
    eapply sll_move_preserves_stack_top_wf in hm; eauto.
    eapply sll_closure_preserves_stack_top_wf; eauto.
  Qed.

  (** The initial SLL subparsers for x all have well-formed stack tops by construction. *)
  Lemma sll_init_sps_stack_tops_wf :
    forall g pm x,
      all_stack_tops_wf g (sll_init_sps pm x).
  Proof.
    intros g pm x [pr (fr, frs)] hi; sis.
    apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; inv heq; auto.
  Qed.

  (** The sll_start_state result has all-stack-tops-well-formed. *)
  Lemma sll_start_state_preserves_stack_top_wf :
    forall g pm cm x sps,
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> sll_start_state pm cm x = inr sps
      -> all_stack_tops_wf g sps.
  Proof.
    intros g pm cm x sps hp hm hs sp hi.
    eapply sll_closure_preserves_stack_top_wf; eauto.
    apply sll_init_sps_stack_tops_wf; auto.
  Qed.

  (* Some facts about the stable_config invariant --
     these should eventually move elsewhere *)

  (* refactor *)
  (** Subparsers returned by sim_return are all stable, because closure map destinations are stable. *)
  Lemma sim_return_some__all_stacks_stable :
    forall g cm sp sps',
      closure_map_correct g cm
      -> sim_return cm sp = Some sps'
      -> all_stable sps'.
  Proof.
    intros g cm sp sps' [hs hc] hr sp' hi.
    unfold sim_return in hr; dms; tc; inv hr.
    apply in_map_iff in hi; destruct hi as [fr [heq hi]]; subst; sis.
    unfold dest_frames in hi; dmeq hf; try solve [inv hi].
    apply FMF.find_mapsto_iff in hf; eapply hs in hi; eauto.
    destruct hi as [_ hst].
    destruct fr as [[x |] [| [a|y] suf]]; sis; tc; auto.
  Qed.

  (** When sim_return returns None and sll_cstep is done, the subparser's stack is in a stable config. *)
  Lemma sim_return_none_cstep_done__stable_config :
    forall g pm cm vi sp,
      stack_top_wf g sp.(sll_stk)
      -> sim_return cm sp = None
      -> sll_cstep pm vi sp = cstep_done
      -> sll_stable_config sp.(sll_stk).
  Proof.
    intros g pm cm vi [pred ([o suf], frs)] hw hr hs.
    unfold sll_cstep in hs; dms; tc; sis; inv hw; auto.
    dms; tc.
  Qed.
  
  (** All subparsers produced by a successful sllc are in a stable configuration. *)
  Lemma sllc_all_stacks_stable :
    forall g pm cm pr (a : Acc lex_nat_pair pr) vi sp hk a' sps',
      pr = sll_meas pm vi sp
      -> rhs_map_correct pm g
      -> closure_map_correct g cm
      -> stack_top_wf g sp.(sll_stk)
      -> sllc pm cm vi sp hk a' = inr sps'
      -> all_stable sps'. 
  Proof.
    intros g pm cm pr a'.
    induction a' as [pr hlt IH]; intros vi sp hk a sps' ? hp hc hw hs sp' hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs' ?] | [ys' [avy' [hs' [? [? ha']]]]]]]]; subst.
    - eapply sim_return_some__all_stacks_stable; eauto.
    - apply in_singleton_eq in hi; subst.
      eapply sim_return_none_cstep_done__stable_config; eauto.
    - eapply aggr_closure_results_succ_in_input in ha'; eauto.
      destruct ha' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply sll_cstep_meas_lt; eauto.
      + eapply sll_cstep_preserves_stack_top_wf; eauto.
  Qed.

  (** All subparsers produced by a successful sll_closure are in a stable configuration. *)
  Lemma sll_closure__all_stacks_stable :
    forall g pm cm sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sll_closure pm cm sps hk = inr sps'
      -> all_stable sps'.
  Proof.
    intros g pm cm sps hk sps' hp hm hw hc sp' hi.
    eapply aggr_closure_results_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply sllc_all_stacks_stable; eauto.
    apply lex_nat_pair_wf.
  Qed.

  (** All subparsers produced by a successful sll_target are in a stable configuration. *)
  Lemma sll_target__all_stacks_stable :
    forall g pm cm a sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sll_target pm cm a sps hk = inr sps'
      -> all_stable sps'.
  Proof.
    intros g pm cm a sps hk sps' hp hc hw ht.
    apply sll_target_cases in ht.
    destruct ht as [sps'' [hk' [hm hc']]].
    eapply sll_move_preserves_stack_top_wf in hm; eauto.
    eapply sll_closure__all_stacks_stable; eauto.
  Qed.
  
  (* X never returns sp_invalid_state *)

  (** A stable SLL subparser never triggers sp_invalid_state in sll_move_sp. *)
  Lemma sll_move_sp_never_returns_sp_invalid_state_for_ready_sp :
    forall t sp,
      sll_stable_config sp.(sll_stk)
      -> sll_move_sp t sp <> move_error sp_invalid_state.
  Proof.
    intros t sp hr; unfold not; intros hm.
    unfold sll_move_sp in hm.
    dms; tc; sis; inv hr.
  Qed.

  (** A list of stable SLL subparsers never produces sp_invalid_state from sll_move. *)
  Lemma sll_move_never_returns_sp_invalid_state_for_ready_sps :
    forall t sps,
      all_stable sps
      -> sll_move t sps <> inl sp_invalid_state.
  Proof.
    intros t sps ha; unfold not; intros hm.
    unfold move in hm.
    apply aggr_move_results_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply sll_move_sp_never_returns_sp_invalid_state_for_ready_sp; eauto.
  Qed.
  
  (** A well-formed SLL subparser never triggers sp_invalid_state in sll_cstep. *)
  Lemma sll_cstep_never_returns_sp_invalid_state :
    forall g pm vi sp,
      stack_top_wf g sp.(sll_stk)
      -> sll_cstep pm vi sp <> cstep_error sp_invalid_state.
  Proof.
    intros g pm vi sp hw hs.
    unfold sll_cstep in hs; dms; subst; tc; inv hw.
  Qed.

  (** sllc never returns sp_invalid_state when the input subparser has a well-formed stack top. *)
  Lemma sllc_never_returns_sp_invalid_state :
    forall (g    : grammar)
           (pm   : rhs_map)
           (cm   : closure_map)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (vi   : NtSet.t)
           (sp   : sll_subparser)
           (hk   : sll_sp_pushes_from_keyset pm sp)
           (a'   : Acc lex_nat_pair (sll_meas pm vi sp)),
      pair = sll_meas pm vi sp
      -> rhs_map_correct pm g
      -> stack_top_wf g sp.(sll_stk)
      -> sllc pm cm vi sp hk a' <> inl sp_invalid_state.
  Proof.
    intros g pm cm pair a'.
    induction a' as [pair hlt IH].
    intros vi sp hk ha heq hp hw hs; subst.
    apply sllc_error_cases in hs.
    destruct hs as [hsr [hs | [sps [av' [hs [crs [heq heq']]]]]]]; subst.
    - eapply sll_cstep_never_returns_sp_invalid_state; eauto. 
    - apply aggr_closure_results_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply sll_cstep_meas_lt; eauto.
      + eapply sll_cstep_preserves_stack_top_wf; eauto.
  Qed.
  
  (** sll_closure never returns sp_invalid_state when all input subparsers have well-formed stack tops. *)
  Lemma sll_closure_neq_sp_invalid_state :
    forall g pm cm sps hk,
      rhs_map_correct pm g
      -> all_stack_tops_wf g sps
      -> sll_closure pm cm sps hk <> inl sp_invalid_state.
  Proof.
    intros g pm cm sps hk hp hw hc.
    unfold sll_closure in hc.
    apply aggr_closure_results_error_in_input in hc.
    eapply dmap_in in hc; eauto; sis.
    destruct hc as [sp [hi [_ hs]]].
    eapply sllc_never_returns_sp_invalid_state; eauto.
    apply lex_nat_pair_wf.
  Qed.

  (** sll_target never returns sp_invalid_state when inputs are well-formed and stable. *)
  Lemma sll_target_neq_sp_invalid_state :
    forall g pm cm a sps hk,
      rhs_map_correct pm g
      -> all_stack_tops_wf g sps
      -> all_stable sps
      -> sll_target pm cm a sps hk <> inl sp_invalid_state.
  Proof.
    intros g pm cm a sps hk hp hw hs ht.
    apply sll_target_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply sll_move_never_returns_sp_invalid_state_for_ready_sps; eauto. 
    - eapply sll_move_preserves_stack_top_wf in hm; eauto.
      eapply sll_closure_neq_sp_invalid_state; eauto.
  Qed.

  (** sll_handle_final_subparsers never returns pred_error for any error value. *)
  Lemma sll_handle_final_subparsers_never_returns_error :
    forall sps e,
      sll_handle_final_subparsers sps <> pred_error e.
  Proof.
    intros sps e; unfold not; intro hh.
    unfold sll_handle_final_subparsers in hh; dms; tc.
  Qed.

  (** sll_predict' never returns sp_invalid_state when inputs are well-formed and stable. *)
  Lemma sll_predict'_neq_sp_invalid_state :
    forall g pm cm ts sps ca hk hc ca',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> all_stable sps
      -> sll_predict' pm cm sps ts ca hk hc <> (pred_error sp_invalid_state, ca').
  Proof.
    intros g pm cm ts; induction ts as [| (a, l) ts IH];
      intros sps ca hk hc ca' hp' hm hw hs hp; sis.
    - inv hp; eapply sll_handle_final_subparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps]; tc; dm; tc.
      apply sll_predict'_cont_cases in hp.
      destruct hp as [ [sps'' [hf hp]] | [ht | [sps'' [ht hp]]]].
      + pose proof hf as hf'; apply hc in hf'.
        destruct hf' as [hk' ht].
        eapply IH in hp; eauto.
        * eapply sll_target_preserves_stack_top_wf; eauto.
        * eapply sll_target__all_stacks_stable; eauto.
      + eapply sll_target_neq_sp_invalid_state; eauto.
      + eapply IH in hp; eauto.
        * eapply sll_target_preserves_stack_top_wf; eauto.
        * eapply sll_target__all_stacks_stable; eauto.
  Qed.

  (** sll_start_state never returns sp_invalid_state because the initial subparsers are well-formed. *)
  Lemma sll_start_state_neq_sp_invalid_state :
    forall g pm cm x,
      rhs_map_correct pm g
      -> sll_start_state pm cm x <> inl sp_invalid_state.
  Proof.
    intros g pm cm x hp hss.
    eapply sll_closure_neq_sp_invalid_state; eauto.
    apply sll_init_sps_stack_tops_wf; auto.
  Qed.
  
  (** sll_predict never returns sp_invalid_state for a well-formed grammar and correct closure map. *)
  Lemma sll_predict_neq_sp_invalid_state :
    forall g pm cm x ts ca hc ca',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> sll_predict pm cm x ts ca hc <> (pred_error sp_invalid_state, ca').
  Proof.
    intros g pm cm x ts ca hc ca' hp hc' hs.
    apply sll_predict_cases in hs.
    destruct hs as [hs | [sps [hss hs]]].
    - eapply sll_start_state_neq_sp_invalid_state; eauto.
    - eapply sll_predict'_neq_sp_invalid_state; eauto.
      + eapply sll_start_state_preserves_stack_top_wf; eauto.
      + eapply sll_closure__all_stacks_stable; eauto.
        apply sll_init_sps_stack_tops_wf; auto.
  Qed.

  (* X never returns SpLeft Recursion *)

  (* to do -- we might be able to merge the two "unavailable NTs" invariants
     into a single definition *)

  (* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

  (* Auxiliary definition *)
  (** The SLL frame list represents a nullable path in the grammar: consecutive frames are linked by grammar productions with nullable prefixes. *)
  Inductive sll_frames_repr_nullable_path (g : grammar) : list sll_frame -> Prop :=
  | fr_direct :
      forall x pre' suf suf' o o',
        PM.In (x, pre' ++ suf') g
        -> nullable_gamma g pre'
        -> sll_frames_repr_nullable_path g [sll_fr o' suf' ; sll_fr o (NT x :: suf)]
  | fr_indirect :
      forall x pre' suf suf' o o' frs,
        PM.In (x, pre' ++ suf') g
        -> nullable_gamma g pre'
        -> sll_frames_repr_nullable_path g (sll_fr o (NT x :: suf) :: frs)
        -> sll_frames_repr_nullable_path g (sll_fr o' suf' :: sll_fr o (NT x :: suf) :: frs).

  Hint Constructors sll_frames_repr_nullable_path : core.

  Ltac inv_frnp hf hi hn hf' :=
    inversion hf as [? ? ? ? ? ? hi hn | ? ? ? ? ? ? ? hi hn hf']; subst; clear hf.

  (** Dropping the outermost head frame of a nullable path yields a shorter valid nullable path. *)
  Lemma sll_frnp_inv_two_head_frames :
    forall g fr fr' fr'' frs,
      sll_frames_repr_nullable_path g (fr'' :: fr' :: frs ++ [fr])
      -> sll_frames_repr_nullable_path g (fr' :: frs ++ [fr]).
  Proof.
    intros g fr fr'' fr''' frs hf.
    destruct frs as [| fr' frs]; sis; inv hf; auto.
  Qed.

  (** In a nullable path of length ≥ 2, the second frame always starts with an NT symbol. *)
  Lemma sll_frnp_second_frame_nt_head :
    forall g fr fr' frs,
      sll_frames_repr_nullable_path g (fr' :: fr :: frs)
      -> exists o x suf,
        fr = sll_fr o (NT x :: suf).
  Proof.
    intros g fr fr' frs hf; inv hf; eauto.
  Qed.

  (** Consuming a nullable prefix of the top frame preserves the nullable path property. *)
  Lemma sll_frnp_shift_head_frame :
    forall g frs o pre suf,
      nullable_gamma g pre
      -> sll_frames_repr_nullable_path g (sll_fr o (pre ++ suf) :: frs)
      -> sll_frames_repr_nullable_path g (sll_fr o suf :: frs).
  Proof.
    intros g frs o pre suf hn hf; destruct frs as [| fr frs]; inv_frnp hf hi hn' hf'.
    - rewrite app_assoc in hi; econstructor; eauto.
      apply nullable_app; auto.
    - rewrite app_assoc in hi; econstructor; eauto.
      apply nullable_app; auto.
  Qed.
  
  (** A nullable path in the SLL frame list implies a corresponding nullable grammar path from x to y. *)
  Lemma sll_frnp_grammar_nullable_path :
    forall g frs fr fr_cr o o' x y suf suf',
      fr       = sll_fr o' (NT y :: suf')
      -> fr_cr = sll_fr o (NT x :: suf)
      -> sll_frames_repr_nullable_path g (fr :: frs ++ [fr_cr])
      -> nullable_path g (NT x) (NT y).
  Proof.
    intros g frs.
    induction frs as [| fr' frs IH]; intros fr fr_cr o o' x z suf suf'' ? ? hf; subst; sis.
    - inv_frnp hf hi hn hf'.
      + eapply direct_path; eauto.
      + inv hf'.
    - pose proof hf as hf'; apply sll_frnp_second_frame_nt_head in hf'.
      destruct hf' as (? & y & suf' & ?); subst.
      apply nullable_path_trans with (y := NT y).
      + apply sll_frnp_inv_two_head_frames in hf; eauto.
      + inv_frnp hf hi hn hf'; eauto.
  Qed.

  (** If the top frame's suffix is nullable and represents a nullable path, then the caller NT x is nullable. *)
  Lemma sll_frnp_caller_nt_nullable :
    forall g x o o' suf suf' frs,
      sll_frames_repr_nullable_path g (sll_fr o' suf' :: sll_fr o (NT x :: suf) :: frs)
      -> nullable_gamma g suf'
      -> nullable_sym g (NT x).
  Proof.
    intros g x o o' suf suf' frs hf hng.
    inv_frnp hf hi hn hf'.
    - econstructor; eauto.
      apply nullable_app; auto.
    - econstructor; eauto.
      apply nullable_app; auto.
  Qed.

  (* The invariant itself *)
  (** Every NT in vi (unavailable for prediction) corresponds to an open call frame in the SLL stack with a nullable path. *)
  Definition sll_unavailable_nts_are_open_calls g vi stk : Prop :=
    match stk with
    | (fr, frs) =>
      forall (x : nonterminal),
        NtSet.In x (all_nts g)
        -> NtSet.In x vi
        -> exists frs_pre fr_cr frs_suf o suf,
            frs = frs_pre ++ fr_cr :: frs_suf
            /\ fr_cr = sll_fr o (NT x :: suf)
            /\ sll_frames_repr_nullable_path g (fr :: frs_pre ++ [fr_cr])
    end.

  (* Lift the invariant to a subparser *)
  (** Lifts sll_unavailable_nts_are_open_calls to a single SLL subparser. *)
  Definition sll_unavailable_nts_invar g vi sp :=
    match sp with
    | sll_sp _ stk => sll_unavailable_nts_are_open_calls g vi stk
    end.

  (* Lift the invariant to a list of subparsers *)
  (** Requires every subparser in a list to satisfy the unavailable NTs invariant. *)
  Definition sll_sps_unavailable_nts_invar g vi sps : Prop :=
    forall sp, In sp sps -> unavailable_nts_invar g vi sp.

  (** A return step removes x from vi and the invariant is maintained for the shorter stack. *)
  Lemma sll_return_preserves_unavailable_nts_invar :
    forall g vi pr o o' suf x fr cr cr' frs,
      fr     = sll_fr o []
      -> cr  = sll_fr o' (NT x :: suf)
      -> cr' = sll_fr o' suf
      -> sll_unavailable_nts_invar g vi (sll_sp pr (fr, cr :: frs))
      -> sll_unavailable_nts_invar g (NtSet.remove x vi) (sll_sp pr (cr', frs)). 
  Proof.
    intros g vi pr o o' suf' x' fr cr cr' frs ? ? ? hu; subst.
    intros x hi hn.
    assert (hn' : NtSet.In x vi) by ND.fsetdec.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & suf & heq & ? & hf); subst.
    destruct frs_pre as [| fr' frs_pre]; sis; inv heq.
    - ND.fsetdec.
    - pose proof hf as hf'; apply sll_frnp_inv_two_head_frames in hf'.
      apply sll_frnp_shift_head_frame with (pre := [NT x']) in hf'; eauto 8.
      constructor; auto.
      apply sll_frnp_caller_nt_nullable in hf; auto.
  Qed.

  (** A push step adds x to vi and the invariant is maintained for the extended stack. *)
  Lemma sll_push_preserves_unavailable_nts_invar :
    forall g cr ce vi pr o o' suf x rhs frs,
      cr = sll_fr o (NT x :: suf)
      -> ce = sll_fr o' rhs
      -> PM.In (x, rhs) g
      -> sll_unavailable_nts_invar g vi (sll_sp pr (cr, frs))
      -> sll_unavailable_nts_invar g (NtSet.add x vi) (sll_sp pr (ce, cr :: frs)).
  Proof.
    intros g cr ce vi pr o o' suf' x' rhs frs ? ? hi hu; subst.
    intros x hi' hn.
    destruct (NF.eq_dec x' x); subst.
    - exists []; repeat eexists; eauto; sis.
      eapply fr_direct with (pre' := []); auto.
    - assert (hn' : NtSet.In x vi) by ND.fsetdec.
      apply hu in hn'; simpl in hn'; clear hu; auto.
      destruct hn' as (frs_pre & fr_cr & frs_suf & ? &
                       suf & heq & heq' & hf); subst.
      exists (sll_fr o (NT x' :: suf') :: frs_pre); repeat eexists; eauto.
      eapply fr_indirect with (pre' := []); eauto.
  Qed.

  (** sll_cstep preserves the unavailable NTs invariant for each produced subparser. *)
  Lemma sll_cstep_preserves_unavailable_nts_invar :
    forall g pm sp sp' sps' vi vi',
      rhs_map_correct pm g
      -> sll_unavailable_nts_invar g vi sp
      -> sll_cstep pm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> sll_unavailable_nts_invar g vi' sp'.
  Proof.
    intros g pm sp sp' sps' vi vi' hc hu hs hi.
    unfold sll_cstep in hs; dmeqs h; inv hs; tc.
    - apply in_singleton_eq in hi; subst.
      eapply sll_return_preserves_unavailable_nts_invar; eauto.
    - inv hi.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply sll_push_preserves_unavailable_nts_invar; eauto.
      eapply rhss_for_in_iff; eauto.
  Qed.

  (** The unavailable NTs invariant holds trivially when vi is empty (no NTs are blocked). *)
  Lemma sll_unavailable_nts_empty :
    forall g pred stk,
      sll_unavailable_nts_invar g NtSet.empty (sll_sp pred stk).
  Proof.
    intros g pred (fr, frs); repeat red; intros; ND.fsetdec.
  Qed.

  (* Moving on to facts about the prediction mechanism ... *)
  
  (** When sll_cstep returns sp_left_recursion x, x is in vi and all_nts gr, and the top frame starts with NT x. *)
  Lemma sll_cstep_left_recursion_facts :
    forall gr rm vi pred fr frs x,
      rhs_map_correct rm gr
      -> sll_cstep rm vi (sll_sp pred (fr, frs)) = cstep_error (sp_left_recursion x)
      -> NtSet.In x vi
         /\ NtSet.In x (all_nts gr)
         /\ exists o suf,
             fr = sll_fr o (NT x :: suf).
  Proof.
    intros gr rm vi pred fr frs x hp hs.
    unfold sll_cstep in hs; repeat dmeq h; tc; inv hs; sis.
    repeat split; eauto.
    - apply NF.mem_iff; auto. 
    - eapply find_all_nts; eauto.
  Qed.

  (** In a non-left-recursive grammar, sll_cstep never reports sp_left_recursion: no nullable cycle can be traversed. *)
  Lemma sll_cstep_never_finds_left_recursion :
    forall gr rm vi sp x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> sll_unavailable_nts_invar gr vi sp
      -> sll_cstep rm vi sp <> cstep_error (sp_left_recursion x).
  Proof.
    intros gr rm vi [pred (fr, frs)] x hn hc hu; unfold not; intros hs.
    pose proof hs as hs'.
    eapply sll_cstep_left_recursion_facts in hs'; eauto.
    destruct hs' as [hn' [hi [o [suf' heq]]]]; subst.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & ? & hf); subst.
    eapply sll_frnp_grammar_nullable_path in hf; eauto.
    firstorder.
  Qed.
  
  (** sllc never returns sp_left_recursion in a non-left-recursive grammar. *)
  Lemma sllc_neq_sp_left_recursion :
    forall (g    : grammar)
           (pm   : rhs_map)
           (cm   : closure_map)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (vi   : NtSet.t)
           (sp   : sll_subparser)
           (hk   : sll_sp_pushes_from_keyset pm sp)
           (a'   : Acc lex_nat_pair (sll_meas pm vi sp))
           (x    : nonterminal),
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_unavailable_nts_invar g vi sp
      -> pair = sll_meas pm vi sp
      -> sllc pm cm vi sp hk a' <> inl (sp_left_recursion x).
  Proof.
    intros g pm cm pair a'.
    induction a' as [pair hlt IH].
    intros vi sp hk a x hn hp hu ? hs; subst.
    apply sllc_error_cases in hs.
    destruct hs as [hsr [hs | [sps [vi' [hs [crs [heq heq']]]]]]]; subst.
    - eapply sll_cstep_never_finds_left_recursion; eauto. 
    - apply aggr_closure_results_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply sll_cstep_meas_lt; eauto.
      + eapply sll_cstep_preserves_unavailable_nts_invar; eauto.
  Qed.
  
  (** sll_closure never returns sp_left_recursion in a non-left-recursive grammar. *)
  Lemma sll_closure_neq_sp_left_recursion :
    forall g pm cm sps hk x,
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_closure pm cm sps hk <> inl (sp_left_recursion x).
  Proof.
    intros g pm cm sps hk x hn hp hc; unfold sll_closure in hc.
    apply aggr_closure_results_error_in_input in hc.
    eapply dmap_in in hc; eauto; sis.
    destruct hc as [[pr (fr, frs)] [hi [_ hs]]].
    eapply sllc_neq_sp_left_recursion; eauto.
    - apply lex_nat_pair_wf.
    - apply sll_unavailable_nts_empty.
  Qed.

  (** sll_move_sp never produces sp_left_recursion — the move operation has no left-recursion check. *)
  Lemma sll_move_sp_never_returns_sp_left_recursion :
    forall t sp x,
      sll_move_sp t sp <> move_error (sp_left_recursion x).
  Proof.
    intros t sp x; unfold not; intros hm.
    unfold sll_move_sp in hm; dms; tc.
  Qed.

  (** sll_move never returns sp_left_recursion because each constituent sll_move_sp cannot produce that error. *)
  Lemma sll_move_never_returns_sp_left_recursion :
    forall t sps x,
      sll_move t sps <> inl (sp_left_recursion x).
  Proof.
    intros t sps x; unfold not; intros hm.
    unfold sll_move in hm.
    apply aggr_move_results_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply sll_move_sp_never_returns_sp_left_recursion; eauto.
  Qed.

  (** sll_target never returns sp_left_recursion: neither move nor closure can produce that error in a non-left-recursive grammar. *)
  Lemma sll_target_neq_sp_left_recursion :
    forall g pm cm a sps hk x,
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_target pm cm a sps hk <> inl (sp_left_recursion x).
  Proof.
    intros g pm cm a sps hk x hn hp ht.
    apply sll_target_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply sll_move_never_returns_sp_left_recursion; eauto.
    - eapply sll_closure_neq_sp_left_recursion; eauto. 
  Qed.
  
  (** The SLL prediction loop never reports sp_left_recursion, propagating the absence of that error from sll_target. *)
  Lemma sll_predict'_neq_sp_left_recursion :
    forall g pm cm ts sps ca hk hc ca' x,
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_predict' pm cm sps ts ca hk hc <> (pred_error (sp_left_recursion x), ca').
  Proof.
    intros g pm cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca hk hc ca' x hn hp hl; sis.
    - inv hl; eapply sll_handle_final_subparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps]; tc; dm; tc.
      apply sll_predict'_cont_cases in hl.
      destruct hl as [ [sps'' [hf hl]] | [ht | [sps'' [ht hl]]]].
      + pose proof hf as hf' ; apply hc in hf'.
        destruct hf' as [hk' ht].
        eapply IH in hl; eauto.
      + eapply sll_target_neq_sp_left_recursion; eauto.
      + eapply IH in hl; eauto.
  Qed. 
  
  (** sll_start_state never returns sp_left_recursion because it delegates closure which is already sp_left_recursion-free. *)
  Lemma sll_start_state_neq_sp_left_recursion :
    forall g pm cm x x',
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_start_state pm cm x <> inl (sp_left_recursion x').
  Proof.
    intros g pm cm x x' hn hp hss.
    eapply sll_closure_neq_sp_left_recursion; eauto.
  Qed.

  (** sll_predict never returns sp_left_recursion: both its start-state and prediction loop phases are sp_left_recursion-free. *)
  Lemma sll_predict_neq_sp_left_recursion :
    forall g pm cm x x' ts ca hc ca',
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_predict pm cm x ts ca hc <> (pred_error (sp_left_recursion x'), ca').
  Proof.
    intros g pm cm x x' ts ca hc ca' hn hp hs.
    apply sll_predict_cases in hs.
    destruct hs as [hss | [sps [hss hs]]].
    - eapply sll_start_state_neq_sp_left_recursion; eauto. 
    - eapply sll_predict'_neq_sp_left_recursion; eauto. 
  Qed.  

  (* Putting it all together *)
  (** sll_predict never returns any pred_error: combines the sp_invalid_state and sp_left_recursion freedom results. *)
  Lemma sll_predict_never_returns_error :
    forall g pm cm x ts ca hc e ca',
      no_left_recursion g
      -> rhs_map_correct pm g
      -> closure_map_correct g cm
      -> sll_predict pm cm x ts ca hc <> (pred_error e, ca').
  Proof.
    intros g pm cm x ts ca hc e ca' hn hp hm hs; destruct e as [| x'].
    - eapply sll_predict_neq_sp_invalid_state; eauto.
    - eapply sll_predict_neq_sp_left_recursion; eauto.
  Qed.
  
  (** adaptive_predict never returns a prediction error: both the SLL fast path and the LL fallback are error-free. *)
  Theorem adaptive_predict_neq_error :
    forall gr hw rm cm fr pre vs x suf frs ts ca hc hk e ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr (fr, frs)
      -> fr = Fr pre vs (NT x :: suf)
      -> adaptive_predict gr hw rm cm pre vs x suf frs ts ca hc hk <> (pred_error e, ca').
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hc hk e ca' hn hp hc' hw' ? ha; subst.
    unfold adaptive_predict in ha.
    dmeq hsll; dms; tc; inv ha.
    - eapply ll_predict_never_returns_error; eauto.
    - eapply sll_predict_never_returns_error; eauto.
  Qed.
  
End SllPredictionErrorFreeFn.
