(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Bool Lia List.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import LLPredictionErrorFree.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module LLPredictionCompleteFn (Import D : Defs.T).

  Module Export LLPEF := LLPredictionErrorFreeFn D.

  (* Beginning of the proofs themselves *)
  
  (** Relational specification of advancing one subparser over a single terminal token. *)
  Inductive move_step :
    subparser -> list token -> subparser -> list token -> Prop :=
  | mv_consume :
      forall pred pre vs suf a v ts frs,
        move_step (Sp pred (Fr pre vs (T a :: suf), frs)) (@existT _ _ a v :: ts)
                  (Sp pred (Fr (T a :: pre) (v, vs) suf, frs)) ts.

  Hint Constructors move_step : core.

  (** A move step does not change the prediction label of a subparser. *)
  Lemma move_step_preserves_label :
    forall sp sp' w w',
      move_step sp w sp' w'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros sp sp' w w' hm; inv hm; auto.
  Qed.

  (** A move step strictly shortens the remaining token list. *)
  Lemma move_step_word_length_lt :
    forall sp sp' ts ts',
      move_step sp ts sp' ts'
      -> length ts' < length ts.
  Proof.
    intros sp sp' ts ts' hm; inv hm; auto.
  Qed.

  (** The [move] function is sound with respect to [move_step]: if a step succeeds, the result is in [move]'s output. *)
  Lemma move_func_refines_move_step :
    forall t ts sp sp' sps sps',
      In sp sps
      -> move_step sp (t :: ts) sp' ts
      -> move t sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros t ts sp sp' sps sps' hi hr hf.
    inv hr.
    eapply move_succ_all_sps_step; eauto.
    auto.
  Qed.

  (** If [move_step] holds, the corresponding [move_sp] call returns [move_succ]. *)
  Lemma move_sp_move_step :
    forall t w' sp sp',
      move_step sp (t :: w') sp' w'
      -> move_sp t sp = move_succ sp'.
  Proof.
    intros t w' sp sp' hm.
    inv hm; unfold move_sp; dms; tc.
  Qed.

  (** If [move_sp] returns [move_succ], then [move_step] holds between the two subparsers. *)
  Lemma move_step_move_sp :
    forall t w' sp sp',
      move_sp t sp = move_succ sp'
      -> move_step sp (t :: w') sp' w'.
  Proof.
    intros [a v] w' [pred ([pre vs suf], frs)] [pred' ([pre' vs' suf'], frs')] hm.
    unfold move_sp in hm.
    destruct suf as [| [a' | x] suf]; try (dms; tc); subst.
    apply inv_move_succ_eq in hm.
    apply inv_sp_eq_terminal_head in hm.
    destruct hm as (? & ? & ? & [heq heq']); subst.
    rewrite cast_ss_refl.
    constructor.
  Qed.

  (** A move step preserves [stack_wf]. *)
  Lemma move_step_preserves_stack_wf_invar :
    forall g sp sp' t w,
      move_step sp (t :: w) sp' w
      -> stack_wf g sp.(stack)
      -> stack_wf g sp'.(stack).
  Proof.
    intros g sp sp' (a,v) w' hm hw.
    eapply move_sp_preserves_stack_wf_invar; eauto.
    eapply move_sp_move_step; eauto.
  Qed.

  (** A move step preserves the keyset invariant. *)
  Lemma move_step_preserves_pushes_invar :
    forall pm sp sp' t w,
      move_step sp (t :: w) sp' w
      -> sp_pushes_from_keyset pm sp
      -> sp_pushes_from_keyset pm sp'.
  Proof.
    intros pm sp sp' (a,l) w' hm hp.
    eapply move_sp_preserves_pki; eauto.
    eapply move_sp_move_step; eauto.
  Qed.
  
  (** A move step shifts the accepted suffix: if the old stack accepts [t :: w'], the new stack accepts [w']. *)
  Lemma move_step_preserves_sas :
    forall gr sp sp' t w',
      move_step sp (t :: w') sp' w'
      -> stack_accepts_suffix gr sp.(stack) (t :: w')
      -> stack_accepts_suffix gr sp'.(stack) w'.
  Proof.
    intros gr [pred ([pre vs suf], frs)] [pred' (fr', frs')] t w' hm hs; red in hs; inv hm; ss_inj; sis.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl).
    pose proof hd as hts.
    apply svd_inv_terminal_head in hts.
    destruct hts as (v' & ts' & ?); subst; sis.
    inv heq; t_inj.
    inv hd; ss_inj.
    inv_t_der; s_inj; sis.
    inv_cons_tokens_eq; t_inj.
    exists ts'; exists wsuf; eexists.
    repeat split; eauto.
    eapply lfas_eq; eauto.
    t'; eauto.
    Unshelve.
    apps.
  Qed.

  (** A stable subparser accepting [t :: w'] can always take a move step consuming [t]. *)
  Lemma move_step_recognize_cons :
    forall g sp t w',
      stable_config sp.(stack)
      -> stack_accepts_suffix g sp.(stack) (t :: w')
      -> exists sp',
          move_step sp (t :: w') sp' w'.
  Proof.
    intros g [pred stk] t w' hs hs'; sis.
    inv hs; auto; sis.
    - destruct hs' as (wpre & wsuf & vs_suf & heq & hd & heq'); subst; rew_anr.
      inv hd.
      exfalso.
      eapply nil_cons; eauto.
    - destruct hs' as (wpre & wsuf & vs_suf & heq & hd & heq'); subst.
      inv hd; ss_inj.
      inv_t_der; s_inj; sis. 
      inv heq; eauto.
  Qed.

  (** Relational spec of one epsilon-closure step: either return from a completed nonterminal or push a new one. *)
  Inductive closure_step (g : grammar) : NtSet.t -> subparser -> NtSet.t -> subparser -> Prop :=
  | cs_ret :
      forall vi pred pre pre' vs vs' x suf frs p f,
        PM.MapsTo (x, rev pre') (@existT _ _ (x, rev pre') (p, f)) g
        -> p (rev_tuple _ vs') = true
        -> closure_step g
                        vi
                        (Sp pred (Fr pre' vs' [], Fr pre vs (NT x :: suf) :: frs))
                        (NtSet.remove x vi)
                        (Sp pred (Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf, frs))
  | cs_push :
      forall vi pred pre vs x suf frs rhs,
        ~ NtSet.In x vi
        -> PM.In (x, rhs) g
        -> closure_step g
                        vi
                        (Sp pred (Fr pre vs (NT x :: suf), frs))
                        (NtSet.add x vi)
                        (Sp pred (Fr [] tt rhs, Fr pre vs (NT x :: suf) :: frs)).

  Hint Constructors closure_step : core.

  (** Inversion for [closure_step]: decomposes into the return case or the push case. *)
  Lemma inv_closure_step :
    forall g vi vi' sp sp',
      closure_step g vi sp vi' sp'
      -> (exists pred pre pre' vs vs' x suf frs p f,
             sp     = Sp pred (Fr pre' vs' [], Fr pre vs (NT x :: suf) :: frs)
             /\ sp' = Sp pred (Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf, frs)
             /\ PM.MapsTo (x, rev pre') (@existT _ _ (x, rev pre') (p, f)) g
             /\ p (rev_tuple _ vs') = true
             /\ vi' = NtSet.remove x vi)
         \/ (exists pred pre vs x suf frs rhs,
                sp = Sp pred (Fr pre vs (NT x :: suf), frs)
                /\ sp' = Sp pred (Fr [] tt rhs, Fr pre vs (NT x :: suf) :: frs)
                /\ ~ NtSet.In x vi
                /\ PM.In (x, rhs) g
                /\ vi' = NtSet.add x vi).
  Proof.
    intros g vi vi' sp sp' hc; inv hc; eauto 16.
  Qed.
      
  Ltac inv_cs hs  hm hp hi hi' :=
    inversion hs as [ ? ? ? ? ? ? ? ? ? ? ? hm hp
                    | ? ? ? ? ? ? ? ? hi hi']; subst; clear hs.

  (** A closure step does not change the prediction label of a subparser. *)
  Lemma closure_step_preserves_label :
    forall g vi vi' sp sp',
      closure_step g vi sp vi' sp'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g vi vi' sp sp' hc; inv hc; auto.
  Qed.

  (** A closure step preserves [stack_wf]. *)
  Lemma closure_step_preserves_stack_wf_invar :
    forall g vi vi' sp sp',
      closure_step g vi sp vi' sp'
      -> stack_wf g sp.(stack)
      -> stack_wf g sp'.(stack).
  Proof.
    intros g sp sp' vi vi' hc hw; inv hc; sis; auto.
    eapply return_preserves_frames_wf_invar; eauto.
  Qed.

  (** A closure step preserves the keyset invariant. *)
  Lemma closure_step_preserves_pki :
    forall g rm vi vi' sp sp',
      rhs_map_correct rm g
      -> closure_step g vi sp vi' sp'
      -> sp_pushes_from_keyset rm sp
      -> sp_pushes_from_keyset rm sp'.
  Proof.
    intros g rm sp sp' vi vi' hp hc hp'; inv hc.
    repeat red in hp'; sis.
    - eapply return_preserves_keyset_invar; eauto.
    - apply push_preserves_keyset_invar; auto.
      eapply production_lhs_in_key_set; eauto.
  Qed.

  (** [cstep] is sound: each produced subparser corresponds to a valid [closure_step] from the input. *)
  Lemma cstep_sound :
    forall gr hw rm vi vi' sp sp' sps',
      rhs_map_correct rm gr
      -> stack_wf gr sp.(stack)
      -> cstep gr hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> closure_step gr vi sp vi' sp'.
  Proof.
    intros gr hw rm vi vi' sp sp' sps' hc hw' hs hi.
    unfold cstep in hs; dmeqs h; tc; subst; sis.
    - inv hw'; inv hs; repeat ss_inj.
      apply in_singleton_eq in hi; subst.
      appl_fpaa; eauto.
    - exfalso; inv hs; inv hi.
    - exfalso; inv hs; inv hi.
    - inv hs.
      apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst.
      constructor.
      + apply NF.not_mem_iff; auto.
      + eapply rhss_for_in_iff; eauto.
  Qed.

  (** Reflexive–transitive closure of [closure_step]: zero or more epsilon-closure steps to a stable state. *)
  Inductive closure_multistep (g : grammar) :
    NtSet.t -> subparser -> NtSet.t -> subparser -> Prop :=
  | cms_empty :
      forall vi pred pre vs,
        closure_multistep g
                          vi (Sp pred (Fr pre vs [], []))
                          vi (Sp pred (Fr pre vs [], []))
  | cms_terminal :
      forall vi pred pre vs a suf frs,
        closure_multistep g vi (Sp pred (Fr pre vs (T a :: suf), frs))
                            vi (Sp pred (Fr pre vs (T a :: suf), frs))
  | cms_trans :
      forall vi vi' vi'' sp sp' sp'',
        closure_step g vi sp vi' sp'
        -> closure_multistep g vi' sp' vi'' sp''
        -> closure_multistep g vi sp vi'' sp''.

  Hint Constructors closure_multistep : core.

  Ltac inv_cm hm hs hm' :=
    inversion hm as [ ? ? ? ?
                    | ? ? ? ? ? ? ?
                    | ? ? ? ? ? ? hs hm']; subst; clear hm.

  Ltac induct_cm hm hs hm' IH :=
    induction hm as [ ? ? ? ?
                    | ? ? ? ? ? ? ?
                    | ? ? ? ? ? ? hs hm' IH].

  (** Closure multistep preserves the prediction label throughout. *)
  Lemma closure_multistep_preserves_label :
    forall g vi vi' sp sp',
      closure_multistep g vi sp vi' sp'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g vi vi' sp sp' hm.
    induct_cm hm hs hm' IH; auto.
    apply closure_step_preserves_label in hs; tc.
  Qed.

  (** If [cstep] is done and [closure_multistep] holds, the start and end subparsers are equal. *)
  Lemma closure_multistep_done_eq :
    forall g hw rm vi vi' sp sp',
      closure_multistep g vi sp vi' sp'
      -> cstep g hw rm vi sp = cstep_done
      -> sp = sp'.
  Proof.
    intros g hw rm vi vi' sp sp' hm hs; unfold cstep in hs; dms; tc;
      inv_cm hm hs' hm'; try ss_inj; auto; inv hs'.
  Qed.
  
  (** When [cstep] continues and multistep reaches [sp''], there is an intermediate subparser in [sps'] on the path. *)
  Lemma closure_multistep_not_done_middle_sp_in_continuation :
    forall gr hw rm vi vi' vi'' sp sp'' sps',
      rhs_map_correct rm gr
      -> closure_multistep gr vi sp vi'' sp''
      -> cstep gr hw rm vi sp = cstep_k vi' sps'
      -> exists sp',
          closure_step gr vi sp vi' sp'
          /\ closure_multistep gr vi' sp' vi'' sp''
          /\ In sp' sps'.
  Proof.
    intros gr hw rm vi vi' vi'' sp sp'' sps' hc hm hs; unfold cstep in hs; dmeqs h; tc; inv hs; eauto.
    - inv_cm hm hs hm'; inv hs; repeat ss_inj; eexists; repeat split; eauto.
      + eauto.
      + appl_fpaa.
        mapsto_fun heq.
        apply inv_grammar_entry_eq in heq.
        destruct heq; subst.
        apply in_eq.
    - exfalso.
      inv_cm hm hs hm'.
      inv_cs hs hm hp hi hi'.
      repeat ss_inj.
      appl_fpaa.
      mapsto_fun heq.
      apply inv_grammar_entry_eq in heq; destruct heq; tc.
    - exfalso.
      inv_cm hm hs hm'.
      inv_cs hs hm hp hi hi'.
      eapply in_grammar_find_some in hi'; eauto.
      destruct hi' as [? [? ?]]; tc.
    - inv_cm hm hs hm'; inv hs; ss_inj. 
      eexists; split.
      + eapply cs_push with (rhs := rhs); eauto.
      + split; auto.
        apply in_map_iff; eexists; split; eauto.
        eapply rhss_for_in_iff; eauto.
  Qed.

  (** Inductive auxiliary: [llc] contains every subparser reachable by closure multistep, by well-founded induction. *)
  Lemma llc_refines_closure_multistep' :
    forall (g  : grammar)
           (hw : grammar_wf g)
           (rm : rhs_map)
           (pr : nat * nat)
           (a  : Acc lex_nat_pair pr)
           (vi vi'' : NtSet.t)
           (sp sp'' : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (a' : Acc lex_nat_pair (ll_meas rm vi sp))
           (sps'' : list subparser),
      pr = ll_meas rm vi sp
      -> rhs_map_correct rm g
      -> closure_multistep g vi sp vi'' sp''
      -> llc g hw rm vi sp hk a' = inr sps''
      -> In sp'' sps''.
  Proof.
    intros g hw rm pr a.
    induction a as [pr hlt IH]; intros vi vi'' sp sp'' hk a' sps'' heq hp hc hs; subst.
    unfold llc in hs.
    apply llc_success_cases in hs.
    destruct hs as [[hdone heq] | [sps' [av' [hs [crs [heq ha]]]]]]; subst.
    - (* sp must be in a "done" configuration, so sp = sp' *)
      eapply closure_multistep_done_eq in hc; subst; eauto.
      apply in_eq.
    - (* sp is in a non-final configuration, so we know something about what's in sps'' *)
      (* also, we know that sp must step to some intermediate subparser sp',
       and sp' multisteps to sp'' *)
      eapply closure_multistep_not_done_middle_sp_in_continuation in hc; eauto.
      destruct hc as [sp' [hs' [hm hi]]].
      eapply aggr_closure_results_dmap_succ_elt_succ in ha; eauto.
      destruct ha as [hi' [sps''' [heq hall]]].
      apply hall.
      eapply IH; eauto.
      eapply cstep_meas_lt; eauto.
  Qed.

  (** [llc] is complete wrt [closure_multistep]: any multistep target is in [llc]'s output. *)
  Lemma llc_refines_closure_multistep :
    forall (g  : grammar)
           (hw : grammar_wf g)
           (rm : rhs_map)
           (vi vi'' : NtSet.t)
           (sp sp'' : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (a : Acc lex_nat_pair (ll_meas rm vi sp))
           (sps'' : list subparser),
      rhs_map_correct rm g
      -> closure_multistep g vi sp vi'' sp''
      -> llc g hw rm vi sp hk a = inr sps''
      -> In sp'' sps''.
  Proof.
    intros; eapply llc_refines_closure_multistep'; eauto.
  Qed.

  (** Inductive auxiliary: every subparser in [llc]'s output is a multistep target, by well-founded induction. *)
  Lemma llc_sound_wrt_closure_multistep' :
    forall (gr : grammar)
           (hw : grammar_wf gr)
           (rm : rhs_map)
           (pr : nat * nat)
           (a  : Acc lex_nat_pair pr)
           (vi : NtSet.t)
           (sp sp''' : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (a' : Acc lex_nat_pair (ll_meas rm vi sp))
           (sps''' : list subparser),
      pr = ll_meas rm vi sp
      -> rhs_map_correct rm gr
      -> stack_wf gr sp.(stack)
      -> llc gr hw rm vi sp hk a' = inr sps'''
      -> In sp''' sps'''
      -> exists vi''',
          closure_multistep gr vi sp vi''' sp'''.
  Proof.
    intros gr hw rm pr a.
    induction a as [pr hlt IH]; intros vi sp sp''' hk a' sps''' heq hp hw' hs hi; subst.
    apply llc_success_cases in hs.
    destruct hs as [[hdone heq] | [sps' [vi' [hs [crs [heq ha]]]]]]; subst.
    - apply in_singleton_eq in hi; subst.
      eapply cstep_done_stable_config in hdone; eauto.
      destruct sp as [pred ([o suf], frs)].
      inv hdone; eauto.
    - eapply aggr_closure_results_dmap_backwards in ha; eauto.
      destruct ha as [sp' [hi' [sps'' [hi'' [hs' hi''']]]]].
      eapply IH in hs'; eauto.
      + destruct hs' as [vi''' hs'].
        exists vi'''.
        eapply cms_trans with (sp' := sp'); eauto.
        eapply cstep_sound; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_wf_invar; eauto.
  Qed.

  (** [llc] is sound wrt [closure_multistep]: every output subparser is a multistep target. *)
  Lemma llc_sound_wrt_closure_multistep :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (rm : rhs_map)
           (vi : NtSet.t)
           (sp sp' : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (a : Acc lex_nat_pair (ll_meas rm vi sp))
           (sps' : list subparser),
      rhs_map_correct rm gr
      -> stack_wf gr sp.(stack)
      -> llc gr hw rm vi sp hk a = inr sps'
      -> In sp' sps'
      -> exists vi',
          closure_multistep gr vi sp vi' sp'.
  Proof.
    intros; eapply llc_sound_wrt_closure_multistep'; eauto.
  Qed.
  
  (** [ll_closure] contains every subparser reachable by closure multistep from any element of [sps]. *)
  Lemma closure_func_refines_closure_multistep :
    forall gr hw rm vi'' sp sp'' sps sps'' hk,
      rhs_map_correct rm gr
      -> In sp sps
      -> closure_multistep gr NtSet.empty sp vi'' sp''
      -> ll_closure gr hw rm sps hk = inr sps''
      -> In sp'' sps''.
  Proof.
    intros gr hw rm vi'' sp sp'' sps sps'' hk hp hi hc hc'.
    eapply aggr_closure_results_dmap_succ_elt_succ in hc'; eauto.
    destruct hc' as [hi' [sps' [heq hall]]].
    apply hall.
    eapply llc_refines_closure_multistep; eauto.
  Qed.

  (** Inductive auxiliary: there exists a closure-multistep target that still accepts the remaining input. *)
  Lemma exists_cm_target_preserving_sas' :
    forall (w  : list token)
           (pr : nat * nat)
           (a  : Acc lex_nat_pair pr)
           (gr : grammar)
           (rm : rhs_map)
           (vi : NtSet.t)
           (sp : subparser)
           (a' : Acc lex_nat_pair (ll_meas rm vi sp)),
      pr = ll_meas rm vi sp
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> sp_pushes_from_keyset rm sp
      -> stack_wf gr sp.(stack)
      -> unavailable_nts_invar gr vi sp
      -> stack_accepts_suffix gr sp.(stack) w
      -> exists vi' sp',
          closure_multistep gr vi sp vi' sp'
          /\ stack_accepts_suffix gr sp'.(stack) w. 
    Proof.
      intros w pr ha.
      induction ha as [m hlt IH]; intros g rm vi sp ha' heq hn hr hk hw hu hg; subst.
      destruct sp as [pred ([pre vs [| [a|x] suf]], frs)]; sis; eauto.
      - destruct frs as [| [pre_cr vs_cr [| [a|x] suf_cr]] frs]; try solve [inv hw; eauto].
        destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
        destruct hl as (wsuf' & wsuf'' & vs_suf' & p & f & heq & hd' & hm & hp & hl); subst; sis.
        assert (heq : (x, rev pre ++ []) = (x, rev pre)) by apps.
        specialize IH with
            (sp := Sp pred (Fr (NT x :: pre_cr) ((cast_action _ _ heq f) (rev_tuple _ vs), vs_cr) suf_cr, frs)).
        edestruct IH as (vi' & sp' & hcm & hr'); sis; eauto.
        + eapply meas_lt_after_return; eauto.
        + apply lex_nat_pair_wf.
        + repeat red in hk; sis. 
          eapply return_preserves_keyset_invar; eauto.
        + apply return_preserves_frames_wf_invar; auto.
        + eapply return_preserves_unavailable_nts_invar; eauto.
        + apply svd_inv_nil_syms with (heq := eq_refl) in hd.
          rewrite cast_ss_refl in hd.
          destruct hd as [? ?]; subst; sis.
          exists wsuf'; exists wsuf''; exists vs_suf'.
          repeat split; auto.
          t'; sis.
          repeat unct.
          eapply lfas_eq; eauto.
          t'.
          erewrite concat_tuple_nil_r.
          t'; auto.
        + (do 2 eexists); split; eauto.
          eapply cms_trans; eauto.
          eapply cs_ret.
          -- apply mapsto_cast with (x := (x, rev pre ++ [])); apps; eauto.
          -- destruct vs_suf.
             t'.
             erewrite concat_tuple_nil_r.
             t'; auto.
      - destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
        destruct vs_suf as (v', vs').
        eapply svd_inv_nonterminal_head with
            (v' := v')
            (vs' := vs') in hd; eauto.
        + destruct hd as (ts' & ts'' & ? & hd & hd'); subst.
          inv_sv hd hm hvs hp; s_inj.
          assert (hi' : ~ NtSet.In x vi).
          { (* lemma *)
            destruct (In_dec x vi) as [hi' | hn']; auto.
            apply hu in hi'.
            - destruct hi' as (? & ? & ? & ? & ? & ? & heq' & heq'' & hnp); subst.
              eapply frnp_grammar_nullable_path in hnp; eauto.
              firstorder.
            - apply all_nts_lhss_iff.
              eapply production_lhs_in_lhss.
              eapply pm_mapsto_in; eauto. }
          specialize IH with
              (sp := Sp pred (Fr [] tt ys, Fr pre vs (NT x :: suf) :: frs)).
          pose proof hm as hm'.
          apply pm_mapsto_in in hm'.
          edestruct IH as [vi' [sp' [hcm hg'']]]; eauto.
          * eapply meas_lt_after_push; sis; eauto.
            -- eapply production_lhs_in_key_set; eauto.
            -- eapply rhss_for_all_rhss.
               eapply rhss_for_in_iff; eauto.
          * apply lex_nat_pair_wf.
          * apply push_preserves_keyset_invar; auto.
            eapply production_lhs_in_key_set; eauto.
          * eapply push_preserves_frames_wf_invar; eauto.
          * eapply push_preserves_unavailable_nts_invar; eauto.
          * exists ts'; exists (ts'' ++ wsuf); eexists.
            rewrite <- app_assoc.
            repeat split; eauto.
            repeat eexists; eauto. 
          * exists vi'; exists sp'; split; auto.
            econstructor; eauto.
            constructor; auto.
        + rewrite cast_ss_refl; auto.
          Unshelve.
          all : apps.
    Qed.

  (** Closure always produces a stable subparser that continues to accept the remaining suffix. *)
  Lemma exists_cm_target_preserving_sas:
    forall gr rm vi sp w,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> sp_pushes_from_keyset rm sp
      -> stack_wf gr sp.(stack)
      -> unavailable_nts_invar gr vi sp
      -> stack_accepts_suffix gr sp.(stack) w
      -> exists vi' sp',
          closure_multistep gr vi sp vi' sp'
          /\ stack_accepts_suffix gr sp'.(stack) w. 
  Proof.
    intros; eapply exists_cm_target_preserving_sas'; eauto;
      apply lex_nat_pair_wf.
  Qed.

  (** Closure multistep preserves [stack_wf] throughout. *)
  Lemma closure_multistep_preserves_stack_wf_invar :
    forall g vi vi' sp sp',
      closure_multistep g vi sp vi' sp'
      -> stack_wf g sp.(stack)
      -> stack_wf g sp'.(stack).
  Proof.
    intros g vi vi' sp sp' hc; induction hc; intros hw; auto.
    eapply IHhc.
    eapply closure_step_preserves_stack_wf_invar; eauto.
  Qed.

  (** Closure multistep preserves the keyset invariant throughout. *)
  Lemma closure_multistep_preserves_pushes_invar :
    forall g rm vi vi' sp sp',
      rhs_map_correct rm g
      -> closure_multistep g vi sp vi' sp'
      -> sp_pushes_from_keyset rm sp
      -> sp_pushes_from_keyset rm sp'.
  Proof.
    intros g rm vi vi' sp sp' hp hc; induction hc; intros hp'; auto.
    eapply IHhc; eapply closure_step_preserves_pki; eauto. 
  Qed.

  (** The final subparser of a closure multistep is always in a stable configuration. *)
  Lemma stable_config_after_closure_multistep :
    forall g vi vi' sp sp',
      stack_wf g sp.(stack)
      -> closure_multistep g vi sp vi' sp'
      -> stable_config sp'.(stack).
  Proof.
    intros g vi vi' sp sp' hw hc.
    induct_cm hc  hs hc' IH; try constructor; sis.
    apply IH; eapply closure_step_preserves_stack_wf_invar; eauto.
  Qed.

  (** The oracle subparser (built from [rhs]) can multistep to some stable subparser that still accepts [w]. *)
  Lemma ll_start_state_closure_multistep_from_orig_sp' :
    forall gr hw rm cr ce pre vs x suf rhs frs hk sps w,
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> PM.In (x, rhs) gr
      -> stack_accepts_suffix gr (ce, cr :: frs) w
      -> ll_start_state gr hw rm pre vs x suf frs hk = inr sps
      -> exists vi sp,
          closure_multistep gr NtSet.empty (Sp rhs (ce, cr :: frs)) vi sp
          /\ stack_accepts_suffix gr sp.(stack) w. 
  Proof.
    intros gr hw rm cr ce pre vs x suf rhs frs hk sps w ? ? hn hp hw' hi hg hs; subst; sis.
    eapply exists_cm_target_preserving_sas; eauto.
    - apply push_preserves_keyset_invar; auto.
      eapply production_lhs_in_key_set; eauto.
    - apply push_preserves_frames_wf_invar; auto.
    - apply unavailable_nts_empty.
  Qed.

  (** The oracle subparser multisteps to a stable subparser accepting [w] that is also in [ll_start_state]'s output. *)
  Lemma ll_start_state_closure_multistep_from_orig_sp :
    forall gr hw rm cr ce pre vs x suf rhs frs hk sps w,
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> PM.In (x, rhs) gr
      -> stack_accepts_suffix gr (ce, cr :: frs) w
      -> ll_start_state gr hw rm pre vs x suf frs hk = inr sps
      -> exists vi sp,
          closure_multistep gr NtSet.empty (Sp rhs (ce, cr :: frs))
                              vi sp
          /\ stack_accepts_suffix gr sp.(stack) w
          /\ In sp sps.
  Proof.
    intros gr hw rm cr ce pre vs x suf rhs frs hk sps w ? ?
           hn hp hw' hi hg hs; subst.
    pose proof hs as hs'.
    eapply ll_start_state_closure_multistep_from_orig_sp' in hs'; eauto.
    destruct hs' as [vi [sp [hc hg']]].
    exists vi; exists sp; repeat split; auto.
    eapply closure_func_refines_closure_multistep; eauto.
    eapply ll_init_sps_result_incl_all_rhss; eauto.
  Qed.

  (** Interleaved move-then-close multistep relation: the "oracle" trace of an accepting parse. *)
  Inductive move_closure_multistep (g : grammar) :
    subparser -> list token -> subparser -> list token -> Prop :=
  | mc_empty :
      forall pred pre vs,
        move_closure_multistep g (Sp pred (Fr pre vs [], [])) []
                                 (Sp pred (Fr pre vs [], [])) []
  | mc_terminal :
      forall pred pre vs suf frs a l ts,
        move_closure_multistep g (Sp pred (Fr pre vs (T a :: suf), frs)) (@existT _ _ a l :: ts)
                                 (Sp pred (Fr pre vs (T a :: suf), frs)) (@existT _ _ a l :: ts)
  | mc_trans :
      forall vi'' sp sp' sp'' sp''' ts ts'' ts''',
        move_step sp ts sp' ts''
        -> closure_multistep g NtSet.empty sp' vi'' sp''
        -> move_closure_multistep g sp'' ts'' sp''' ts'''
        -> move_closure_multistep g sp ts sp''' ts'''.

  Hint Constructors move_closure_multistep : core.

  Ltac induct_mcms hm :=
    induction hm as [ ? ? ? 
                    | ? ? ? ? ? ? ? ?
                    | ? ? ? ? ? ? ? ? hm hc hms IH].

  Ltac inv_mcms hm :=
    inversion hm as [ ? ? ? 
                    | ? ? ? ? ? ? ? ?
                    | ? ? ? ? ? ? ? ? hm' hc hms IH]; subst; clear hm.

  (** Move-closure multistep preserves the prediction label throughout. *)
  Lemma mcms_preserves_label :
    forall g sp sp' w w',
      move_closure_multistep g sp w sp' w'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g sp sp' w w' hm.
    induct_mcms hm; auto.
    apply move_step_preserves_label in hm.
    apply closure_multistep_preserves_label in hc; tc. 
  Qed.

  (** If the remaining suffix is empty after mcms, the final subparser is in a final configuration. *)
  Lemma mcms_succ_final_config :
    forall g sp sp' wpre wsuf,
      move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
      -> wsuf = []
      -> final_config sp' = true.
  Proof.
    intros g sp sp' wpre wsuf hm.
    induction hm; intros heq; auto.
    inv heq.
  Qed.

  (** Move-closure multistep is monotone: the remaining token list never grows. *)
  Lemma mcms_word_length_le :
    forall g sp sp' ts ts',
      move_closure_multistep g sp ts sp' ts'
      -> length ts' <= length ts. 
  Proof.
    intros g sp sp' ts ts' hm.
    induct_mcms hm; auto.
    inv hm; sis; auto.
  Qed.

  (** Auxiliary: split an mcms trace into a prefix group and a suffix continuation. *)
  Lemma mcms_backtrack_three_groups' :
    forall g sp sp'' w wsuf,
      move_closure_multistep g sp w sp'' wsuf
      -> forall wpre wmid,
        wpre ++ wmid ++ wsuf = w
        -> exists sp',
          move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
          /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros g sp sp'' w wsuf hm.
    induct_mcms hm; intros wpre wmid heq; subst.
    - rewrite app_nil_r in *; apply app_eq_nil in heq; destruct heq; subst; eauto.
    - apply app_double_left_identity_nil in heq; destruct heq; subst; sis; eauto.
    - destruct wpre as [| t wpre]; sis.
      + destruct wmid as [| t wmid]; sis.
        * apply move_step_word_length_lt in hm; apply mcms_word_length_le in hms.
          lia.
        * inv hm; eauto.
      + inv hm; destruct (IH wpre wmid) as [sp' [hms' hms'']]; eauto.
  Qed.

  (** An mcms trace over [wpre ++ wmid ++ wsuf] splits into a [wpre]-prefix trace and a [wmid ++ wsuf]-suffix trace. *)
  Lemma mcms_backtrack_three_groups :
    forall g sp sp'' wpre wmid wsuf,
      move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp'' wsuf
      -> exists sp',
        move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
        /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros; eapply mcms_backtrack_three_groups'; eauto.
  Qed.

  (** An mcms trace to [] splits into a prefix trace ending at [wsuf] and a suffix trace from [wsuf] to []. *)
  Lemma mcms_backtrack_two_groups :
    forall g sp sp'' wpre wsuf,
      move_closure_multistep g sp (wpre ++ wsuf) sp'' []
      -> exists sp',
        move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
        /\ move_closure_multistep g sp' wsuf sp'' [].
  Proof.
    intros g sp sp'' wpre wsuf hm.
    assert (happ : wpre ++ wsuf = (wpre ++ wsuf ++ [])) by apps.
    rewrite happ in hm.
    eapply mcms_backtrack_three_groups in hm; rew_anr; eauto.
  Qed.

  (** An mcms trace splits at a specific terminal [t]: there is an intermediate subparser right before [t]. *)
  Lemma mcms_backtrack_terminal :
    forall g sp sp'' t wpre wsuf,
      move_closure_multistep g sp (wpre ++ t :: wsuf) sp'' wsuf
      -> exists sp',
        move_closure_multistep g sp (wpre ++ t :: wsuf) sp' (t :: wsuf)
        /\ move_closure_multistep g sp' (t :: wsuf) sp'' wsuf.
  Proof.
    intros; rewrite cons_app_singleton in *.
    eapply mcms_backtrack_three_groups; eauto.
  Qed.

  (** Auxiliary: if the token lists are equal in mcms, the subparsers are equal too. *)
  Lemma mcms_words_eq__subparsers_eq' :
    forall g sp sp' ts ts',
      move_closure_multistep g sp ts sp' ts'
      -> ts = ts'
      -> sp = sp'.
  Proof.
    intros g sp sp' ts ts' hm heq; inv_mcms hm; auto.
    apply move_step_word_length_lt in hm'; apply mcms_word_length_le in hms; lia.
  Qed.

  (** If mcms reaches [sp'] with the same token list, then [sp = sp']. *)
  Lemma mcms_words_eq__subparsers_eq :
    forall g sp sp' ts,
      move_closure_multistep g sp ts sp' ts
      -> sp = sp'.
  Proof.
    intros; eapply mcms_words_eq__subparsers_eq'; eauto. 
  Qed.

  (** Inversion for mcms over a nonempty token list: there is a move step followed by a closure multistep. *)
  Lemma mcms_inv_nonempty_word :
    forall g sp sp'' t wsuf,
      move_closure_multistep g sp (t :: wsuf) sp'' wsuf
      -> exists vi' vi'' sp',
        move_step sp (t :: wsuf) sp' wsuf
        /\ closure_multistep g vi' sp' vi'' sp''.
  Proof.
    intros g sp sp'' t wsuf hm; inv_mcms hm; auto.
    - exfalso; eapply cons_neq_tail; eauto.
    - inv hm'; apply mcms_words_eq__subparsers_eq in hms;
        destruct hms; subst; eauto. 
  Qed.

  (** From an mcms consuming token [t], extract the intermediate subparser after the move step. *)
  Lemma mcms_consume_exists_intermediate_subparser :
    forall g sp sp'' t wsuf,
      move_closure_multistep g sp (t :: wsuf) sp'' wsuf
      -> exists vi'' sp',
        move_step sp (t :: wsuf) sp' wsuf
        /\ closure_multistep g NtSet.empty sp' vi'' sp''.
  Proof.
    intros g sp sp'' t wsuf hm; inv_mcms hm.
    - exfalso; eapply cons_neq_tail; eauto.
    - inv hm'.
      eapply mcms_words_eq__subparsers_eq in hms;
        destruct hms; subst; eauto.
  Qed.

  (** A stable subparser accepting the empty input is reflexively related to itself in mcms. *)
  Lemma mcms_recognize_nil_empty :
    forall gr sp,
      stable_config sp.(stack)
      -> stack_accepts_suffix gr sp.(stack) []
      -> move_closure_multistep gr sp [] sp [].
  Proof.
    intros g [pred stk] hs hg; simpl in hs.
    inversion hs as [| a suf frs]; subst; clear hs; sis; auto.
    destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    symmetry in heq; apply app_eq_nil in heq; destruct heq; subst.
    exfalso; eapply svd_terminal_head_contra; eauto.
  Qed.

  (** A stable subparser that accepts [w] can always consume all of [w] via mcms, reaching an empty token list. *)
  Lemma mcms_subparser_consumes_remaining_input :
    forall gr rm w sp,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> sp_pushes_from_keyset rm sp
      -> stable_config sp.(stack)
      -> stack_wf gr sp.(stack)
      -> stack_accepts_suffix gr sp.(stack) w
      -> exists sp'', 
          move_closure_multistep gr sp w sp'' [].
  Proof.
    intros gr rm w; induction w as [| t w' IH]; intros sp hn hp hp' hs hw hg.
    - eapply mcms_recognize_nil_empty in hg; eauto.
    - assert (hm : exists sp', move_step sp (t :: w') sp' w'). 
      { apply move_step_recognize_cons in hg; auto. }
      destruct hm as [sp' hm].
      assert (hc : exists vi'' sp'', 
                 closure_multistep gr NtSet.empty sp' vi'' sp''
                 /\ stack_accepts_suffix gr sp''.(stack) w'). 
      { eapply exists_cm_target_preserving_sas; eauto.
        - eapply move_step_preserves_pushes_invar; eauto.
        - eapply move_step_preserves_stack_wf_invar; eauto.
        - destruct sp'; apply unavailable_nts_empty.
        - eapply move_step_preserves_sas; eauto. }
      destruct hc as [vi'' [sp'' [hc hg'']]].
      eapply IH in hg''; eauto.
      + destruct hg'' as [sp''' hmcms]; eauto.
      + eapply closure_multistep_preserves_pushes_invar; eauto.
        eapply move_step_preserves_pushes_invar; eauto.
      + eapply stable_config_after_closure_multistep
          with (sp := sp'); eauto.
        eapply move_step_preserves_stack_wf_invar; eauto.
      + eapply closure_multistep_preserves_stack_wf_invar; eauto.
        eapply move_step_preserves_stack_wf_invar; eauto.
  Qed.

  (** Move-closure multistep is transitive. *)
  Lemma mcms_transitive :
    forall g w w' sp sp',
      move_closure_multistep g sp w sp' w'
      -> forall sp'' w'',
        move_closure_multistep g sp' w' sp'' w''
        -> move_closure_multistep g sp w sp'' w''.
  Proof.
    intros g w w' sp sp' hm.
    induction hm; intros sp'''' w'' hm'; inv hm'; try ss_inj; try t_inj; eauto. 
  Qed.

  (** Transitivity for three-part mcms decompositions: combines a prefix and suffix trace. *)
  Lemma mcms_transitive_three_groups :
    forall g wpre wmid wsuf sp sp' sp'',
      move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
      -> move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf
      -> move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros; eapply mcms_transitive; eauto.
  Qed.

  (* Next definitions and lemmas relate to this invariant *)
  (** Completeness invariant: every mcms trace from an original subparser lands in the current set. *)
  Definition subparsers_complete_wrt_originals g sps wpre sps' wsuf : Prop :=
    forall sp sp',
      In sp sps
      -> move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
      -> In sp' sps'.

  (** One move+close step preserves the completeness invariant: the new set still covers all mcms traces. *)
  Lemma move_closure_op_preserves_subparsers_complete_invar :
    forall gr hw rm t wpre wsuf sps sps' sps'' sps''' hk,
      rhs_map_correct rm gr
      -> subparsers_complete_wrt_originals gr sps wpre sps' (t :: wsuf)
      -> move t sps' = inr sps''
      -> ll_closure gr hw rm sps'' hk = inr sps'''
      -> subparsers_complete_wrt_originals gr sps (wpre ++ [t]) sps''' wsuf.
  Proof.
    intros g hw rm t wpre wsuf sps sps' sps'' sps'''
           hk hp hinvar hm hc. 
    unfold subparsers_complete_wrt_originals. 
    rewrite <- app_assoc; simpl; intros sp sp''' hi hms.
    eapply mcms_backtrack_terminal in hms.
    destruct hms as [sp' [hms hms']].
    apply hinvar in hms; auto.
    eapply mcms_consume_exists_intermediate_subparser in hms'.
    destruct hms' as [av'' [sp'' [hm' hc']]].
    eapply move_func_refines_move_step in hm'; eauto.
    eapply closure_func_refines_closure_multistep; eauto.
  Qed.

  (** [ll_target] preserves the completeness invariant: all mcms traces are still covered after the target step. *)
  Lemma ll_target_preserves_subparsers_complete_invar :
    forall gr hw rm t wpre wsuf sps sps' sps'' hk,
      rhs_map_correct rm gr
      -> subparsers_complete_wrt_originals gr sps wpre sps' (t :: wsuf)
      -> ll_target gr hw rm t sps' hk = inr sps''
      -> subparsers_complete_wrt_originals gr sps (wpre ++ [t]) sps'' wsuf.
  Proof.
    intros g hw rm t wpre wsuf sps sps' sps'' hk hp hc ht.
    apply ll_target_cases in ht.
    destruct ht as [sps''' [hk' [hm hc']]].
    eapply move_closure_op_preserves_subparsers_complete_invar; eauto.
  Qed.
  
  (** If [ll_predict'] succeeds, there is a prefix position where all oracle traces agree on the returned prediction. *)
  Lemma ll_predict'_succ_labels_eq_after_prefix :
    forall gr hw rm orig_sps wsuf wpre curr_sps hk rhs,
      rhs_map_correct rm gr
      -> subparsers_complete_wrt_originals gr orig_sps wpre curr_sps wsuf
      -> ll_predict' gr hw rm curr_sps wsuf hk = pred_succ rhs
      -> exists wpre' wsuf',
          wpre ++ wsuf = wpre' ++ wsuf'
          /\ forall sp sp',
            In sp orig_sps
            -> move_closure_multistep gr sp (wpre' ++ wsuf') sp' wsuf'
            -> sp.(prediction) = rhs.
  Proof.
    intros g hw rm orig_sps wsuf.
    induction wsuf as [| (a,l) wsuf' IH]; intros wpre curr_sps hk rhs hp hi hl; sis.
    - unfold handle_final_subparsers in hl.
      destruct (filter _ _) as [| sp'' sps''] eqn:hf; tc.
      destruct (all_predictions_equal_b _ _ sp'' sps'') eqn:ha'; tc.
      inv hl.
      exists wpre; exists []; split; auto.
      intros orig_sp curr_sp' hin hm.
      apply eq_trans with (y := curr_sp'.(prediction)).
      + eapply mcms_preserves_label; eauto.
      + pose proof hm as hm'.
        apply hi in hm; auto.
        apply mcms_succ_final_config in hm'; auto.
        eapply filter_in' in hm; eauto.
        rewrite hf in hm.
        destruct hm as [hh | ht]; subst; auto.
        eapply all_predictions_equal_prop; eauto.
        apply beq_gamma_eq_iff.
    - destruct curr_sps as [| curr_sp curr_sps]; tc.
      destruct (all_predictions_equal_b _ _ curr_sp curr_sps) eqn:ha.
      + inv hl; exists wpre; exists (@existT _ _ a l :: wsuf'); split; auto.
        intros orig_sp curr_sp' hin hm.
        apply eq_trans with (y := curr_sp'.(prediction)).
        * eapply mcms_preserves_label; eauto.
        * eapply hi in hm; eauto.
          destruct hm as [hh | ht]; subst; auto.
          eapply all_predictions_equal_prop; eauto.
          apply beq_gamma_eq_iff.
      + apply ll_predict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]]. 
        eapply IH with (wpre := wpre ++ [@existT _ _ a l]) in hl; eauto.
        * destruct hl as [wpre' [wsuf'' [heq hall]]].
          exists wpre'; exists wsuf''; split; auto.
          rewrite <- heq; apps.
        * eapply ll_target_preserves_subparsers_complete_invar; eauto.
  Qed.

  (** The completeness invariant holds trivially at the start with an empty prefix. *)
  Lemma subparsers_complete_invar_starts_true :
    forall g sps w,
      subparsers_complete_wrt_originals g sps [] sps w.
  Proof.
    intros g sps w sp sp' hi hm; sis.
    eapply mcms_words_eq__subparsers_eq in hm; subst; auto.
  Qed.

    (* One of the main lemmas in this file; if ll_predict return a right-hand side
   and finds no ambiguity, then only that right-hand side will result in a 
   successful derivation *)
  (* This probably belongs in a different file, since it's involved in more than
   just proving completeness *)
  (** If [ll_predict] succeeds with [rhs'] and the oracle parse uses [rhs], then [rhs' = rhs]: at most one RHS applies. *)
  Lemma ll_predict_succ_at_most_one_rhs_applies :
    forall gr hw rm cr ce pre vs x suf frs w hk rhs rhs',
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs 
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> PM.In (x, rhs) gr
      -> stack_accepts_suffix gr (ce, cr :: frs) w
      -> ll_predict gr hw rm pre vs x suf frs w hk = pred_succ rhs'
      -> rhs' = rhs.
  Proof.
    intros gr hw rm cr ce pre vs x suf frs w hk rhs rhs' ? ? hn hp hw' hi hr hl; subst.
    apply ll_predict_cases in hl.
    destruct hl as [sps [hs hl]].
    pose proof hs as hs'.
    eapply ll_start_state_closure_multistep_from_orig_sp in hs'; eauto.
    destruct hs' as [vi [sp [hc [hg' hi']]]].
    eapply ll_predict'_succ_labels_eq_after_prefix
      with (wpre := []) (orig_sps := sps) in hl;
      [ .. | eapply subparsers_complete_invar_starts_true; eauto]; eauto.
    destruct hl as [wpre' [wsuf' [heq hall]]]; simpl in heq; subst.
    eapply mcms_subparser_consumes_remaining_input in hg'; eauto.
    - destruct hg' as [sp'' hm].
      eapply mcms_backtrack_two_groups in hm.
      destruct hm as [sp' [hm hm']].
      apply hall in hm; subst; auto.
      apply closure_multistep_preserves_label in hc; auto.
    - eapply closure_multistep_preserves_pushes_invar; eauto.
      constructor; auto.
      eapply production_lhs_in_key_set; eauto.
    - eapply stable_config_after_closure_multistep; eauto; sis.
      eapply push_preserves_frames_wf_invar; eauto.
    - eapply closure_multistep_preserves_stack_wf_invar; eauto; sis.
      apply push_preserves_frames_wf_invar; auto.
  Qed.

  (* relational spec for ambiguous prediction *)

  (** Variant of mcms where the base cases accept any remaining tokens (used for ambiguity proofs). *)
  Inductive move_closure_multistep' (g : grammar) :
    subparser -> list token -> subparser -> list token -> Prop :=
  | mc_empty' :
      forall pred pre vs ts,
        move_closure_multistep' g
                                (Sp pred (Fr pre vs [], [])) ts
                                (Sp pred (Fr pre vs [], [])) ts
  | mc_terminal' :
      forall pred pre vs a suf frs ts,
        move_closure_multistep' g
                                (Sp pred (Fr pre vs (T a :: suf), frs)) ts
                                (Sp pred (Fr pre vs (T a :: suf), frs)) ts
  | mc_trans' :
      forall vi'' sp sp' sp'' sp''' ts ts'' ts''',
        move_step sp ts sp' ts''
        -> closure_multistep g NtSet.empty sp' vi'' sp''
        -> move_closure_multistep' g sp'' ts'' sp''' ts'''
        -> move_closure_multistep' g sp ts sp''' ts'''.

  Hint Constructors move_closure_multistep' : core.

  (** Soundness invariant: every current subparser traces back to an original subparser via mcms'. *)
  Definition subparsers_sound_wrt_originals g sps wpre sps' wsuf :=
    forall sp',
      In sp' sps'
      -> exists sp,
        In sp sps
        /\ move_closure_multistep' g sp (wpre ++ wsuf) sp' wsuf.

  (** Backward direction: each subparser in [move]'s output came from a [move_step] on some input. *)
  Lemma move_func_refines_move_step_backward :
    forall a l w sps sps' sp',
      move (@existT _ _ a l) sps = inr sps'
      -> In sp' sps'
      -> exists sp,
          In sp sps
          /\ move_step sp (@existT _ _ a l :: w) sp' w.
  Proof.
    intros a l s sps sps' sp' hm hi.
    unfold move in hm.
    eapply aggr_move_results_map_backwards in hm; eauto.
    destruct hm as [sp [hi' hm]].
    exists sp; split; auto.
    apply move_step_move_sp; auto.
  Qed.

  (** Backward direction: each subparser in [ll_closure]'s output came from a closure multistep on some input. *)
  Lemma closure_func_refines_closure_multistep_backward :
    forall gr hw rm sps sps'' sp'' hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> ll_closure gr hw rm sps hk = inr sps''
      -> In sp'' sps''
      -> exists vi'' sp,
          In sp sps
          /\ closure_multistep gr NtSet.empty sp vi'' sp''.
  Proof.
    intros gr hw rm sps sps'' sp'' hk hp ha hc hi.
    eapply aggr_closure_results_dmap_backwards in hc; eauto.
    destruct hc as [sp [hi' [sps' [_ [hl hi'']]]]].
    eapply llc_sound_wrt_closure_multistep in hl; destruct hl; eauto.
  Qed.

  (** [move_closure_multistep'] is transitive. *)
  Lemma mcms'_transitive :
    forall g w w' sp sp',
      move_closure_multistep' g sp w sp' w'
      -> forall sp'' w'',
        move_closure_multistep' g sp' w' sp'' w''
        -> move_closure_multistep' g sp w sp'' w''.
  Proof.
    intros g w w' sp sp' hm.
    induction hm; intros sp'''' w'' hm'; inv hm'; try ss_inj; eauto. 
  Qed.

  (** Transitivity for three-part mcms' decompositions. *)
  Lemma mcms'_transitive_three_groups :
    forall g wpre wmid wsuf sp sp' sp'',
      move_closure_multistep' g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
      -> move_closure_multistep' g sp' (wmid ++ wsuf) sp'' wsuf
      -> move_closure_multistep' g sp (wpre ++ wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros; eapply mcms'_transitive; eauto.
  Qed.

  (** [move_closure_multistep'] preserves the prediction label. *)
  Lemma mcms'_preserves_label :
    forall g sp sp' w w',
      move_closure_multistep' g sp w sp' w'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g sp sp' w w' hm.
    induction hm; auto.
    apply move_step_preserves_label in H.
    apply closure_multistep_preserves_label in H0; tc.
  Qed.

  (* refactor *)
  (** [move_closure_multistep'] preserves [stack_wf] throughout. *)
  Lemma mcms'_preserves_stack_wf_invar :
    forall g sp sp' w w',
      move_closure_multistep' g sp w sp' w'
      -> stack_wf g sp.(stack)
      -> stack_wf g sp'.(stack).
  Proof.
    intros g sp sp' w w' hm.
    induction hm; intros; sis; auto.
    apply IHhm.
    eapply closure_multistep_preserves_stack_wf_invar; eauto.
    pose proof H as H'; inv H; sis; subst.
    eapply move_step_preserves_stack_wf_invar with (g := g) in H'; eauto.
  Qed.

  (* refactor? *)
  (** One move+close step preserves the soundness invariant: every new subparser traces back to an original. *)
  Lemma move_closure_op_preserves_subparsers_sound_invar :
    forall gr hw rm a l wpre wsuf sps sps' sps'' sps''' hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> subparsers_sound_wrt_originals gr sps wpre sps' (@existT _ _ a l :: wsuf)
      -> move (@existT _ _ a l) sps' = inr sps''
      -> ll_closure gr hw rm sps'' hk = inr sps'''
      -> subparsers_sound_wrt_originals gr sps (wpre ++ [@existT _ _ a l]) sps''' wsuf.
  Proof.
    intros gr hw rm a l wpre wsuf sps sps' sps'' sps''' hk hp ha hi hm hc. 
    unfold subparsers_sound_wrt_originals in *.
    rewrite <- app_assoc; simpl; intros sp''' hi'''.
    (* lemma *)
    assert (ha' : all_stacks_wf gr sps').
    { intros sp' hi'.
      apply hi in hi'.
      destruct hi' as [sp [hi' hmcms]].
      eapply mcms'_preserves_stack_wf_invar; eauto. }
    assert (ha'' : all_stacks_wf gr sps'').
    { eapply move_preserves_stack_wf_invar; eauto. }
    assert (ha''' : all_stacks_wf gr sps''').
    { eapply ll_closure_preserves_stack_wf_invar; eauto. }
    eapply closure_func_refines_closure_multistep_backward in hc; eauto.
    destruct hc as [av'' [sp'' [hi'' hc]]].
    eapply move_func_refines_move_step_backward
      with (w := wsuf) in hm; eauto.
    destruct hm as [sp' [hi' hm]].
    apply hi in hi'; clear hi.
    destruct hi' as [sp [hi hmcms]].
    exists sp; split; auto.
    rewrite cons_app_singleton in *.
    eapply mcms'_transitive_three_groups; eauto.
    econstructor; eauto.
    apply stable_config_after_closure_multistep in hc.
    - destruct sp''' as [pred ([suf], frs)]; inv hc; auto.
    - eapply move_step_preserves_stack_wf_invar; eauto.
      eapply mcms'_preserves_stack_wf_invar; eauto.
  Qed.

  (** [ll_target] preserves the soundness invariant: produced subparsers trace back to originals via mcms'. *)
  Lemma ll_target_preserves_subparsers_sound_invar :
    forall gr hw rm a l wpre wsuf sps sps' sps'' hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> subparsers_sound_wrt_originals gr sps wpre sps' (@existT _ _ a l:: wsuf)
      -> ll_target gr hw rm (@existT _ _ a l) sps' hk = inr sps''
      -> subparsers_sound_wrt_originals gr sps (wpre ++ [@existT _ _ a l]) sps'' wsuf.
  Proof.
    intros gr hw rm a l wpre wsuf sps sps' sps'' hk hp hw' hs ht.
    apply ll_target_cases in ht.
    destruct ht as [sps''' [hk' [hm hc]]].
    eapply move_closure_op_preserves_subparsers_sound_invar; eauto.
  Qed.

  (** If [ll_predict'] returns ambiguous, there exist original and final subparsers witnessing a full accepting parse. *)
  Lemma ll_predict'_ambig_rhs_leads_to_successful_parse :
    forall gr hw rm orig_sps wsuf wpre curr_sps hk rhs,
      rhs_map_correct rm gr
      -> all_stacks_wf gr orig_sps
      -> subparsers_sound_wrt_originals gr orig_sps wpre curr_sps wsuf
      -> ll_predict' gr hw rm curr_sps wsuf hk = pred_ambig rhs
      -> exists orig_sp final_sp,
          In orig_sp orig_sps
          /\ orig_sp.(prediction) = rhs
          /\ move_closure_multistep' gr orig_sp (wpre ++ wsuf) final_sp []
          /\ final_config final_sp = true.
  Proof.
    intros gr hw rm orig_sps wsuf.
    induction wsuf as [| (a,l) wsuf' IH]; intros wpre curr_sps hk rhs hp ha hi hl; sis; tc.
    - unfold handle_final_subparsers in hl.
      destruct (filter _ _) as [| csp' csps'] eqn:hf; tc.
      destruct (all_predictions_equal_b _ _ csp' csps') eqn:ha''; tc.
      inv hl.
      unfold subparsers_sound_wrt_originals in hi.
      pose proof hf as hf'.
      eapply filter_cons_in in hf.
      apply hi in hf.
      destruct hf as [orig_sp [hi' hm]].
      exists orig_sp; exists csp'; repeat split; auto.
      + (* easy *)
        eapply mcms'_preserves_label; eauto.
      + assert (hi'' : In csp' (filter final_config curr_sps)).
        { rewrite hf'; apply in_eq. }
        eapply filter_In in hi''; destruct hi''; auto.
    - destruct curr_sps as [| sp' sps']; tc.
      destruct (all_predictions_equal_b _ _); tc.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      eapply IH with (wpre := wpre ++ [@existT _ _ a l]) in hl; auto.
      + destruct hl as [osp [fsp [hi' [heq [hm' hf]]]]].
        exists osp; exists fsp; repeat split; auto.
        rewrite <- app_assoc in hm'; auto.
      + eapply ll_target_preserves_subparsers_sound_invar; eauto.
  Qed.

  (** Backward closure step: if the post-step stack accepts [w], the pre-step stack also accepts [w]. *)
  Lemma closure_step_ussr_backward :
    forall g vi vi' sp sp' w,
      closure_step g vi sp vi' sp'
      -> stack_accepts_suffix g sp'.(stack) w
      -> stack_accepts_suffix g sp.(stack) w. 
  Proof.
    intros g vi vi' (pred & ([pre vs suf], frs)) (pred' & ([pre' vs' suf'], frs')) w hc hg; sis.
    destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    apply inv_closure_step in hc.
    destruct hc as [hl' | hr'].
    - destruct hl' as (pred'' & pre'' & pre''' & vs'' & vs''' & x & suf'' & frs'' & p & f & heq & heq' & hm & hp & hvi); subst.
      inv heq; inv heq'; repeat ss_inj.
      exists []; eexists; exists tt; repeat split; eauto.
      red.
      exists wpre; exists wsuf; eexists.
      assert (heq : (x, rev pre''') = (x, rev pre''' ++ [])) by apps.
      exists (cast_predicate _ _ heq p).
      exists (cast_action    _ _ heq f).
      repeat split; eauto.
      + t'.
      + t'; erewrite concat_tuple_nil_r; eauto.
      + simpl in hl; unrt.
        eapply lfas_replace_head; eauto.
        eapply lfas_eq; eauto.
        t'; eauto.
        simpl; unct.
        t'; auto.
        symmetry; t'.
        erewrite concat_tuple_nil_r; eauto.
    - destruct hr' as (pred'' & pre'' & vs'' & x & suf'' & frs'' & rhs & heq & heq' & hnin & hin & heq''); subst.
      inv heq; inv heq'; repeat ss_inj; sis.
      destruct hl as (wsuf' & wsuf'' & vs_suf' & p & f & heq & hd' & hm & hp & hl); subst; unct.
      exists (wpre ++ wsuf'); exists wsuf''; eexists; repeat split; eauto; sis; apps.
      constructor; eauto.
      Unshelve.
      all : apps.
  Qed.

  (** Backward closure multistep: acceptance propagates backward along the multistep trace. *)
  Lemma closure_multistep_ussr_backward :
    forall g vi vi' sp sp' w,
      closure_multistep g vi sp vi' sp'
      -> stack_accepts_suffix g sp'.(stack) w
      -> stack_accepts_suffix g sp.(stack) w.
  Proof.
    intros g vi vi' sp sp' w hc hg; induction hc; sis; auto.
    apply IHhc in hg.
    eapply closure_step_ussr_backward; eauto.
  Qed.

  (* refactor *)
  (** An mcms' trace ending at a final configuration implies the stack accepts [w]. *)
  Lemma mcms'_final_config :
    forall g w sp sp',
      move_closure_multistep' g sp w sp' []
      -> final_config sp' = true
      -> stack_accepts_suffix g sp.(stack) w.
  Proof.
    intros g w; induction w as [| [a v] w IH]; intros sp sp' hm hf.
    - inv hm; sis; tc.
      + exists []; exists []; exists tt; repeat split; auto. 
      + inv H.
    - inv hm.
      inv H; t_inj; sis.
      apply IH in H1; auto.
      eapply closure_multistep_ussr_backward in H1; eauto.
      destruct H1 as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      exists (@existT _ _ a v :: wpre); exists wsuf. exists (v, vs_suf); repeat split; auto; apps.
      + assert (heq : @existT _ _ a v :: wpre = [@existT _ _ a v] ++ wpre) by apps.
        rewrite heq; constructor; auto.
      + eapply lfas_eq; eauto.
        sis.
        unrt.
        t'; auto.
        simpl.
        rewrite cast_ss_refl.
        repeat unct; auto.
        Unshelve.
        all : sis; auto; apps.
  Qed.

  (** Backward from [ll_closure]: each output subparser has a pre-image in [sps] that also accepts [w]. *)
  Lemma closure_ussr_backwards :
    forall gr hw rm sps sps' sp' w hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> ll_closure gr hw rm sps hk = inr sps'
      -> In sp' sps'
      -> stack_accepts_suffix gr sp'.(stack) w
      -> exists sp vi',
          In sp sps
          /\ closure_multistep gr NtSet.empty sp vi' sp'
          /\ stack_accepts_suffix gr sp.(stack) w.
  Proof.
    intros gr hw rm sps sps' sp' w hk hp ha hc hi hg.
    eapply closure_func_refines_closure_multistep_backward in hc; eauto.
    destruct hc as [vi'' [sp [hi' hc]]].
    repeat eexists; eauto.
    eapply closure_multistep_ussr_backward; eauto.
  Qed.

  (* mention this one in email *)
  (** If [ll_predict] returns ambiguous with [rhs], the initial entry stack accepts [w] via [rhs]. *)
  Lemma ll_predict_ambig_rhs_unproc_stack_syms :
    forall gr hw rm cr ce pre vs x suf frs w rhs hk,
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> ll_predict gr hw rm pre vs x suf frs w hk = pred_ambig rhs
      -> stack_accepts_suffix gr (ce, cr :: frs) w. 
  Proof.
    intros gr hw rm ? ? pre vs x suf frs w rhs hk ? ? hn hr hw' hl; subst; sis.
    pose proof hl as hl'; eapply ll_predict_ambig_in_grammar in hl'; eauto.
    apply ll_predict_cases in hl.
    destruct hl as [sps [hs hl]].
    eapply ll_predict'_ambig_rhs_leads_to_successful_parse
      with (orig_sps := sps) (wpre := []) in hl; sis; eauto.
    - destruct hl as [sp [sp' [hi [heq [hm hf]]]]]; subst.
      eapply mcms'_final_config in hm; auto.
      unfold ll_start_state in hs.
      eapply closure_ussr_backwards in hs; eauto.
      + destruct hs as [init_sp [av' [hi' [hc hg]]]].
        (* lemma? *)
        unfold ll_init_sps in hi'.
        apply in_map_iff in hi'.
        destruct hi' as [rhs [heq hi']]; subst; sis.
        apply closure_multistep_preserves_label in hc; sis; subst; auto.
      + eapply ll_init_sps_preserves_stack_wf_invar; eauto. 
    - eapply ll_start_state_preserves_stacks_wf_invar; eauto. 
    - red. intros sp' hi; sis.
      exists sp'; split; auto.
      eapply closure_func_refines_closure_multistep_backward in hi; eauto.
      + destruct hi as [av'' [sp0 [hi hc]]].
        assert (hst : stable_config sp'.(stack)).
        { eapply stable_config_after_closure_multistep; eauto.
          eapply ll_init_sps_preserves_stack_wf_invar; eauto. }
        destruct sp' as [pred ([suf'], frs')]; sis.
        inv hst; auto.
      + eapply ll_init_sps_preserves_stack_wf_invar; eauto.
  Qed.
  
  (* Now some facts about how prediction doesn't return result_reject when the initial
   stack's unprocessed symbols recognize the input *)

  (** There exists a subparser in [sps] whose stack accepts [w]. *)
  Definition exists_successful_sp g sps w :=
    exists sp, In sp sps /\ stack_accepts_suffix g sp.(stack) w. 

  (** A stable subparser that accepts the empty word is in a final configuration. *)
  Lemma stable_config_sas_nil__final_config :
    forall g sp,
      stack_accepts_suffix g sp.(stack) []
      -> stable_config sp.(stack)
      -> final_config sp = true.
  Proof.
    intros g [pred ([pre vs [| [a|x] suf]], frs)] hg hs; inv hs; sis; auto.
    exfalso.
    destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    aen.
    apply svd_terminal_head_contra in hd; auto.
  Qed.

  (** A stable subparser accepting [t :: w'] must have a terminal at the head of its suffix. *)
  Lemma stable_config_sas_terminal_inv :
    forall g sp t w',
      stable_config sp.(stack)
      -> stack_accepts_suffix g sp.(stack) (t :: w')
      -> exists pre vs a suf frs,
          sp.(stack) = (Fr pre vs (T a :: suf), frs).
  Proof.
    intros g [pred ([pre vs [| [a|x] suf]], frs)] t w' hs hg; sis.
    - inv hs; ss_inj.
      destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); sis; subst.
      apply svd_inv_nil_syms in hd; subst; sis; tc; auto.
    - repeat eexists; eauto.
    - inv hs.
  Qed.
  
  (** A stable subparser accepting [a :: w'] yields a [move_succ] and a subparser accepting [w']. *)
  Lemma move_sp_preserves_successful_sp_invar :
    forall g sp a l w',
      stable_config sp.(stack)
      -> stack_accepts_suffix g sp.(stack) (@existT _ _ a l :: w') 
      -> exists sp',
          move_sp (@existT _ _ a l) sp = move_succ sp'
          /\ stack_accepts_suffix g sp'.(stack) w'. 
  Proof.
    intros g sp a l w' hs hg.
    pose proof hg as hg'.
    apply stable_config_sas_terminal_inv in hg; auto.
    destruct hg as (pre & vs & a' & suf & frs & heq).
    unfold move_sp.
    destruct sp as [pred stk]; subst; sis.
    rewrite heq; rewrite heq in hg'; sis.
    destruct hg' as (wpre & wsuf & vs_suf & heq' & hd & hl); subst.
    pose proof hd as hd'.
    apply svd_inv_terminal_head in hd.
    destruct hd as (v' & ts' & ?); subst.
    inv heq'; t_inj.
    dm; tc.
    eexists; split; eauto; simpl.
    eapply svd_terminal_head__svd_tl in hd'; eauto.
    destruct hd' as (vs' & heq & hd').
    rewrite cast_ss_refl in heq; inv heq.
    exists ts'; exists wsuf; eexists; repeat split; eauto.
    t'.
    eapply lfas_eq; eauto.
    Unshelve.
    all : auto; apps.
  Qed.

  (** If a stable successful subparser is in [sps], the aggregated move result contains a successful post-move subparser. *)
  Lemma aggr_move_results_map_preserves_successful_sp_invar :
    forall g sp sps sps' a l w',
      all_stacks_stable sps
      -> In sp sps
      -> stack_accepts_suffix g sp.(stack) (@existT _ _ a l :: w')
      -> aggr_move_results (map (move_sp (@existT _ _ a l)) sps) = inr sps'
      -> exists sp',
          move_sp (@existT _ _ a l) sp = move_succ sp'
          /\ In sp' sps'
          /\ stack_accepts_suffix g sp'.(stack) w'. 
  Proof.
    intros g sp sps.
    induction sps as [| hd tl IH]; intros sps' a l w' ha hi hg hm.
    - inv hi.
    - destruct hi as [hh | ht]; subst.
      + apply move_sp_preserves_successful_sp_invar in hg.
        * destruct hg as [sp' [hmsp hg]].
          unfold aggr_move_results in hm.
          rewrite map_cons in hm.
          rewrite hmsp in hm.
          dm; tc.
          inv hm.
          eexists; repeat split; eauto.
          apply in_eq.
        * firstorder. 
      + simpl in hm.
        dm; tc; dmeq hag; tc; inv hm; eapply IH in hag; eauto; firstorder.
  Qed.

  (** [move] preserves [exists_successful_sp]: a successful subparser survives and continues to accept the shorter input. *)
  Lemma move_preserves_successful_sp_invar :
    forall g sps sps' a l w',
      all_stacks_stable sps
      -> exists_successful_sp g sps (@existT _ _ a l :: w')
      -> move (@existT _ _ a l) sps = inr sps'
      -> exists_successful_sp g sps' w'.
  Proof.
    intros g sps sps' a l w' ha he hm.
    destruct he as [sp [hi hg]].
    red.
    eapply aggr_move_results_map_preserves_successful_sp_invar in hm; eauto.
    firstorder.
  Qed.

  (** A closure step produces a subparser set containing at least one successful subparser. *)
  Lemma cstep_preserves_successful_sp_invar :
    forall gr hw rm vi vi' sp sps' w,
      rhs_map_correct rm gr
      -> stack_accepts_suffix gr sp.(stack) w
      -> cstep gr hw rm vi sp = cstep_k vi' sps'
      -> exists_successful_sp gr sps' w.
  Proof.
    intros gr hw rm vi vi' sp sps' w hc hg hs.
    unfold cstep in hs; dmeqs h; tc; inv hs; try appl_fpaa.
    - eexists; split; [apply in_eq | ..].
      eapply return_preserves_sas; eauto.
      auto. 
    - exfalso; eapply sas_failed_predicate_contra; eauto.
    - exfalso; eapply sas_find_neq_none; eauto.
    - destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      inv_svs hd hh ht; ss_inj.
      inv_sv hh hm hvs hp; s_inj.
      eexists; split.
      + apply in_map_iff.
        eexists; split; eauto.
        eapply rhss_for_in_iff; eauto.
        eapply pm_mapsto_in; eauto.
      + sis.
        exists w1; exists (w2 ++ wsuf); eexists; repeat split; eauto 12; apps.
  Qed.

  (** Inductive auxiliary: [llc] preserves [exists_successful_sp], by well-founded induction on the measure. *)
  Lemma llc_preserves_successful_sp_invar' :
    forall gr hw rm pr (a : Acc lex_nat_pair pr) vi sp hk (a' : Acc lex_nat_pair (ll_meas rm vi sp)) sps' w,
      rhs_map_correct rm gr
      -> pr = ll_meas rm vi sp
      -> llc gr hw rm vi sp hk a' = inr sps'
      -> stack_accepts_suffix gr sp.(stack) w
      -> exists_successful_sp gr sps' w.
  Proof.
    intros gr hw rm pr a'.
    induction a' as [pr hlt IH]; intros vi sp hk a sps'' w hp ? hs hg; subst.
    apply llc_success_cases in hs.
    destruct hs as [[hdone heq] | [sps' [av' [hs [crs [heq ha]]]]]]; subst.
    - eexists; split; eauto.
      apply in_eq.
    - pose proof hs as hs'. 
      eapply cstep_preserves_successful_sp_invar in hs'; eauto.
      destruct hs' as [sp' [hi hg']].
      eapply aggr_closure_results_dmap_succ_elt_succ in ha; eauto.
      destruct ha as [? [? [hs' ha]]].
      eapply IH in hs'; eauto.
      + destruct hs' as [? [? ?]]; eexists; split; eauto.
      + eapply cstep_meas_lt; eauto.
  Qed.

  (** [llc] preserves [exists_successful_sp]: a successful input subparser leads to a successful output. *)
  Lemma llc_preserves_successful_sp_invar :
    forall gr hw rm vi sp hk (a : Acc lex_nat_pair (ll_meas rm vi sp)) sps' w,
      rhs_map_correct rm gr
      -> llc gr hw rm vi sp hk a = inr sps'
      -> stack_accepts_suffix gr sp.(stack) w
      -> exists_successful_sp gr sps' w.
  Proof.
    intros; eapply llc_preserves_successful_sp_invar'; eauto.
  Qed.

  (** [ll_closure] preserves [exists_successful_sp]: a successful subparser in [sps] leads to one in [sps']. *)
  Lemma closure_preserves_successful_sp_invar :
    forall gr hw rm sps sps' hk w,
      rhs_map_correct rm gr
      -> exists_successful_sp gr sps w
      -> ll_closure gr hw rm sps hk = inr sps'
      -> exists_successful_sp gr sps' w.
  Proof.
    intros gr hw rm sps sps'' hk w hp he hc; destruct he as [sp [hi hg]]; red.
    eapply aggr_closure_results_dmap_succ_elt_succ in hc; eauto.
    destruct hc as [hi' [sps' [hs ha]]].
    eapply llc_preserves_successful_sp_invar in hs; eauto; firstorder.
  Qed.
  
  (** A combined move+close preserves [exists_successful_sp]: a successful subparser survives both operations. *)
  Lemma move_closure_preserves_successful_sp_invar :
    forall gr hw rm sps sps' sps'' hk a l w',
      rhs_map_correct rm gr
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps (@existT _ _ a l :: w')
      -> move (@existT _ _ a l) sps = inr sps'
      -> ll_closure gr hw rm sps' hk = inr sps''
      -> exists_successful_sp gr sps'' w'.
  Proof.
    intros gr hw rm sps sps' sps'' hk a l w' hp ha he hm hc.
    eapply move_preserves_successful_sp_invar in hm; eauto.
    eapply closure_preserves_successful_sp_invar; eauto.
  Qed.

  (** [ll_target] preserves [exists_successful_sp]: a successful subparser leads to one after moving and closing. *)
  Lemma ll_target_preserves_successful_sp_invar :
    forall gr hw rm sps sps' hk a l w',
      rhs_map_correct rm gr
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps (@existT _ _ a l :: w')
      -> ll_target gr hw rm (@existT _ _ a l) sps hk = inr sps'
      -> exists_successful_sp gr sps' w'.
  Proof.
    intros gr hw rm sps sps' hk a l w' hp hs he ht.
    apply ll_target_cases in ht.
    destruct ht as [sps'' [hk' [hm hc]]].
    eapply move_closure_preserves_successful_sp_invar; eauto.
  Qed.
  
  (** A successful subparser in [sps] ensures [ll_predict'] does not return [pred_reject]. *)
  Lemma esp_ll_predict'_neq_reject :
    forall gr hw rm w sps hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps w
      -> ll_predict' gr hw rm sps w hk <> pred_reject.
  Proof.
    intros gr hw rm w; induction w as [| (a,l) w' IH]; intros sps hk hp ha ha' hex;
      unfold not; intros hl; unfold exists_successful_sp in hex; sis.
    - destruct hex as [sp [hi hg]].
      destruct sps as [| sp' sps']; try solve [inv hi].
      (* lemma *)
      unfold handle_final_subparsers in hl.
      destruct (filter _ _) as [| sp'' sps''] eqn:hf; dms; tc.
      apply stable_config_sas_nil__final_config in hg; auto.
      eapply filter_in' in hg; eauto.
      rewrite hf in hg; inv hg.
    - destruct hex as [sp [hi hg]]. 
      destruct sps as [| sp' sps']; try solve [inv hi].
      dm; tc.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      eapply IH in hl; eauto.
      + eapply ll_target_preserves_stacks_wf_invar; eauto.
      + eapply ll_target_preserves_stacks_stable_invar; eauto.
      + eapply ll_target_preserves_successful_sp_invar; eauto.
        exists sp; split; eauto.
  Qed.

  (** Unanimous predictions plus a successful subparser force [ll_predict'] to return [pred_succ]. *)
  Lemma ape_esp_ll_predict'_succ :
    forall gr hw rm sp sps ts hk,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> all_predictions_equal prediction sp sps
      -> exists_successful_sp gr sps ts
      -> ll_predict' gr hw rm sps ts hk = pred_succ (prediction sp).
  Proof.
    intros gr hw rm sp sps ts hk hn hp hw' hs ha he.
    destruct (ll_predict' gr hw rm sps ts hk) as [rhs | rhs | | e] eqn:hl.
    - f_equal; eapply ll_predict'_succ__eq_all_predictions_equal in hl; eauto.
    - exfalso; eapply all_predictions_equal__ll_predict'_neq_ambig; eauto. 
    - exfalso; eapply esp_ll_predict'_neq_reject; eauto.
    - exfalso; eapply ll_predict'_never_returns_error; eauto.
  Qed.
  
  (** If [ll_predict'] succeeds on a nonempty token list, there is a valid target and a recursive success call. *)
  Lemma esp_ll_predict'_succ__exists_target :
    forall gr hw rm sps a l ts hk ys,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps (@existT _ _ a l :: ts)
      -> ll_predict' gr hw rm sps (@existT _ _ a l :: ts) hk = pred_succ ys
      -> exists sps' (ht : ll_target gr hw rm (@existT _ _ a l) sps hk = inr sps'),
          ll_predict' gr hw rm sps' ts (ll_target_preserves_pki gr hw rm (@existT _ _ a l) sps sps' hk ht) = pred_succ ys.
  Proof.
    intros gr hw rm sps a l ts hk ys hn hp hw' hs he hl; sis.
    destruct sps as [| sp sps]; tc.
    destruct (all_predictions_equal_b _ _) eqn:ha.
    - inv hl; apply all_predictions_equal_prop in ha.
      pose proof (ll_target_destruct gr hw rm (@existT _ _ a l) (sp :: sps) hk) as ht.
      destruct ht as [[e ht] | [sps' ht]].
      + exfalso; eapply ll_target_never_returns_error; eauto.
      + exists sps'; exists ht. 
        eapply ape_esp_ll_predict'_succ; eauto. 
        * eapply ll_target_preserves_stacks_wf_invar; eauto.
        * eapply ll_target_preserves_stacks_stable_invar; eauto.
        * eapply ll_target_preserves_ape in ht; eauto.
          apply ape_cons_head_eq; auto.
        * eapply ll_target_preserves_successful_sp_invar; eauto.
      + apply beq_gamma_eq_iff.
    - apply ll_predict'_cont_cases in hl; eauto.
  Qed.
  
  (** The initial subparser set contains a successful subparser if the caller's frame accepts [w]. *)
  Lemma ll_init_sps_preserves_esp_invar :
    forall gr rm fr pre vs x suf frs w,
      rhs_map_correct rm gr
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_accepts_suffix gr (fr, frs) w
      -> exists_successful_sp gr (ll_init_sps rm pre vs x suf frs) w.
  Proof.
    intros gr rm fr pre vs x suf frs w hc ? hg; subst; sis.
    destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    inv_svs hd hh ht; ss_inj.
    inv_sv hh hm hvs hp; s_inj.
    eexists; split.
    - apply in_map_iff; eexists; split; eauto.
      eapply rhss_for_in_iff; eauto.
      eapply pm_mapsto_in; eauto.
    - (* lemma *)
      sis; rewrite <- app_assoc; eauto 16.
  Qed.

  (** [ll_start_state] preserves [exists_successful_sp]: a successful subparser survives the initial closure. *)
  Lemma ll_start_state_preserves_esp_invar :
    forall gr hw rm fr pre vs x suf frs hk w sps,
      rhs_map_correct rm gr
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_accepts_suffix gr (fr, frs) w
      -> ll_start_state gr hw rm pre vs x suf frs hk = inr sps
      -> exists_successful_sp gr sps w.
  Proof.
    intros gr hw rm fr pre vs x suf frs hk w sps hp ? hr hs; subst.
    eapply closure_preserves_successful_sp_invar; eauto.
    eapply ll_init_sps_preserves_esp_invar; eauto.
  Qed.
    
  (** Main completeness theorem: if the stack accepts [w], [ll_predict] does not return [pred_reject]. *)
  Theorem ussr_ll_predict_neq_reject :
    forall gr hw rm fr pre vs x suf frs w hk,
      rhs_map_correct rm gr
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_wf gr (fr, frs)
      -> stack_accepts_suffix gr (fr, frs) w
      -> ll_predict gr hw rm pre vs x suf frs w hk <> pred_reject.
  Proof.
    intros gr hw rm fr pre vs x suf frs w hk hp ? hw' hg hl; subst.
    apply ll_predict_cases in hl.
    destruct hl as [sps [hs hl]].
    eapply esp_ll_predict'_neq_reject; eauto.
    - eapply ll_start_state_preserves_stacks_wf_invar; eauto. 
    - eapply ll_start_state_all_stacks_stable; eauto.
    - eapply ll_start_state_preserves_esp_invar; eauto. 
  Qed.
  
End LLPredictionCompleteFn.
