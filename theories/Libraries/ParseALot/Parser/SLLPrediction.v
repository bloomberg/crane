(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import FMaps List FSets Program.Wf.
From Crane Require Import Extraction.
From Crane.Libraries.ParseALot.Parser Require Import GrammarAnalysis.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import Orders.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module SllPredictionFn (Import D : Defs.T).

  Module Export GA := GrammarAnalysisFn D.

  (* move operation *)

  (** Advances a single SLL subparser by consuming terminal a, or rejects/errors if the top symbol doesn't match. *)
  Definition sll_move_sp (a : terminal) (sp : sll_subparser) : subparser_move_result :=
      match sp with
      | sll_sp pred stk =>
        match stk with
        | (sll_fr _ [], [])            => move_reject
        | (sll_fr _ [], _ :: _)        => move_error sp_invalid_state
        | (sll_fr _ (NT _ :: _), _)    => move_error sp_invalid_state
        | (sll_fr o (T a' :: suf), frs) =>
          if t_eq_dec a' a then
            move_succ (sll_sp pred (sll_fr o suf, frs))
          else
            move_reject
        end
      end.

  (** A successful sll_move_sp step does not change the subparser's prediction. *)
  Lemma sll_move_sp_preserves_prediction :
    forall t sp sp',
      sll_move_sp t sp = move_succ sp'
      -> sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros t sp sp' hm; unfold sll_move_sp in hm.
    dms; tc; subst; inv hm; auto.
  Qed.

  (** A successful sll_move_sp step preserves the keyset invariant on pushes. *)
  Lemma sll_move_sp_preserves_lhss_invar :
    forall rm a sp sp',
      sll_sp_pushes_from_keyset rm sp
      -> sll_move_sp a sp = move_succ sp'
      -> sll_sp_pushes_from_keyset rm sp'.
  Proof.
    intros rm a sp sp' hk hm.
    unfold sll_move_sp in hm; dms; tc; inv hm; sis.
    red; red in hk; sis.
    eapply consume_preserves_keyset_invar; eauto.
  Qed.

  (** If sll_move_sp succeeds on sp producing sp', then sp' appears in the aggregated success list. *)
  Lemma aggr_move_results_succ_all_sll_sps_step :
    forall t sp sps sp' sps',
      In sp sps
      -> sll_move_sp t sp = move_succ sp'
      -> aggr_move_results (map (sll_move_sp t) sps) = inr sps'
      -> In sp' sps'.
  Proof.
    intros t sp sps. 
    induction sps as [| hd tl IH]; intros sp' sps' hi hm ha; inv hi; sis.
    - dms; tc. 
      inv hm; inv ha.
      apply in_eq.
    - dms; tc.
      inv ha.
      apply in_cons; auto.
  Qed.

  (** Applies sll_move_sp to all subparsers in the list and aggregates the results. *)
  Definition sll_move (a : terminal) (sps : list sll_subparser) : move_result sll_subparser :=
    aggr_move_results (map (sll_move_sp a) sps).

  (** Every output subparser of sll_move traces back to an input subparser with the same prediction. *)
  Lemma sll_move_preserves_prediction :
    forall t sp' sps sps',
      sll_move t sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros t sp' sps sps' hm hi.
    unfold move in hm.
    eapply aggr_move_results_succ_in_input in hm; eauto.
    eapply in_map_iff in hm; destruct hm as [sp [hmsp hi']].
    eexists; split; eauto.
    eapply sll_move_sp_preserves_prediction; eauto.
  Qed.

  (** sll_move preserves the keyset invariant across the whole subparser list. *)
  Lemma sll_move_preserves_pki :
    forall rm a sps sps',
      all_sll_sp_pushes_from_keyset rm sps
      -> sll_move a sps = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm a sps sps' hk hm sp' hi'.
    eapply aggr_move_results_map_backwards in hm; eauto.
    destruct hm as [sp [hi hm]].
    eapply sll_move_sp_preserves_lhss_invar; eauto.
  Qed.

  (* closure operation *)

  (** Simulates a return step using the closure map when the top frame is complete (suffix = []), bypassing full closure. *)
  Definition sim_return (cm : closure_map) (sp : sll_subparser) : option (list sll_subparser) :=
    match sp with
    | sll_sp pred (sll_fr (Some x) [], []) =>
      let dsts := dest_frames (sll_fr (Some x) []) cm in
      let sps' := map (fun d => sll_sp pred (d, [])) dsts
      in  Some sps'
    | _ => None
    end.

  (** sim_return preserves the prediction: all output subparsers carry the same prediction as the input. *)
  Lemma sim_return_preserves_prediction :
    forall cm sp sp' sps',
      sim_return cm sp = Some sps'
      -> In sp' sps'
      -> sll_pred sp' = sll_pred sp.
  Proof.
    intros cm [pred (fr, frs)] sp' sps' hs hi; sis; dms; tc; inv hs.
    apply in_map_iff in hi; destruct hi as [? [? ?]]; subst; auto.
  Qed.

  (** sim_return only fires when the subparser's top frame is a completed NT frame with no callers. *)
  Lemma sim_return_stack_shape :
    forall cm sp sps',
      sim_return cm sp = Some sps'
      -> exists x, sp.(sll_stk) = (sll_fr (Some x) [], []).
  Proof.
    intros cm sp sps' hr; unfold sim_return in hr; dms; inv hr; sis; eauto.
  Qed.

  (** The output subparsers of sim_return all satisfy the keyset push invariant. *)
  Lemma sim_return_pki :
    forall pm cm sp sps',
      sim_return cm sp = Some sps'
      -> all_sll_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm [pred (fr, frs)] sps' hr sp' hi; sis; dms; tc; inv hr.
    apply in_map_iff in hi; destruct hi as [[o suf] [heq hi]]; subst. 
    repeat red; auto.
  Qed.

  (** Computes one SLL closure step: handles return, terminal-stop, and NT-push cases using the rhs map. *)
  Definition sll_cstep (rm : rhs_map) (vi : NtSet.t) (sp : sll_subparser) :
    subparser_closure_step_result :=
    match sp with
    | sll_sp pred (fr, frs) =>
      match fr, frs with
      (* should be unreachable *)
      | sll_fr o [], [] =>  cstep_done 
      (* return to caller frame *)
      | sll_fr o [], sll_fr o_cr (NT x :: suf_cr) :: frs_tl =>
        let stk':= (sll_fr o_cr suf_cr, frs_tl) 
        in  cstep_k (NtSet.remove x vi) [sll_sp pred stk']
      (* done case -- top stack symbol is a terminal *)
      | sll_fr _ (T _ :: _), _ => cstep_done
      (* push case *)
      | sll_fr o (NT x :: suf), _ =>
        if NtSet.mem x vi then
          (* Unreachable for a left-recursive grammar *)
          match NM.find x rm with
          | Some _ => cstep_error (sp_left_recursion x)
          | None   => cstep_k NtSet.empty []
          end
        else
          let sps' := map (fun rhs => sll_sp pred (sll_fr (Some x) rhs, fr :: frs))
                          (rhss_for x rm)
          in  cstep_k (NtSet.add x vi) sps'
      | _, _ => cstep_error sp_invalid_state
      end
    end.
  
  (** An sll_cstep transition does not alter the prediction of any produced subparser. *)
  Lemma sll_cstep_preserves_prediction :
    forall rm sp sp' sps' vi vi',
      sll_cstep rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> sp.(sll_pred) = sp'.(sll_pred).
  Proof.
    intros rm sp sp' sps' vi vi' hs hi.
    unfold sll_cstep in hs; dms; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst; auto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; auto.
  Qed.

  (** sll_cstep preserves the keyset push invariant for every produced subparser. *)
  Lemma sll_cstep_preserves_pki :
    forall rm vi sp vi' sp' sps',
      sll_sp_pushes_from_keyset rm sp
      -> sll_cstep rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> sll_sp_pushes_from_keyset rm sp'.
  Proof.
    intros rm vi sp vi' sp' sps' hk hs hi.
    unfold sll_cstep in hs; dms; tc; inv hs; red; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      red; repeat red in hk; sis.
      eapply return_preserves_keyset_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply push_preserves_keyset_invar; eauto.
      eapply rhss_for_key_set; eauto.
  Qed.

  (** Lexicographic termination measure for the SLL closure: tracks remaining stack depth and NT availability. *)
  Definition sll_meas (rm : rhs_map) (vi : NtSet.t) (sp : sll_subparser) : nat * nat :=
    match sp with
    | sll_sp _ sk => meas rm vi (sll_stack_suffixes sk)
    end.

  (** Each sll_cstep transition strictly decreases the sll_meas measure under the lexicographic order. *)
  Lemma sll_cstep_meas_lt :
    forall (rm     : rhs_map)
           (sp sp' : sll_subparser)
           (sps'   : list sll_subparser)
           (vi vi' : NtSet.t),
      sll_sp_pushes_from_keyset rm sp
      -> sll_cstep rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> lex_nat_pair (sll_meas rm vi' sp') (sll_meas rm vi sp).
  Proof.
    intros rm sp sp' sps' vi vi' ha hs hi.
    unfold sll_cstep in hs; dmeqs h; tc; inv hs; try solve [inv hi].
    - red; repeat red in ha; sis.
      apply in_singleton_eq in hi; subst.
      eapply meas_lt_after_return; eauto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; sis.
      eapply meas_lt_after_push; eauto.
      + apply not_mem_iff; auto.
      + eapply rhss_for_key_set; eauto.
      + eapply rhss_for_all_rhss; eauto.
  Defined.

  (** Transfers well-foundedness accessibility from the current subparser to a successor after one sll_cstep. *)
  Lemma acc_after_sll_step :
    forall rm sp sp' sps' vi vi',
      sll_sp_pushes_from_keyset rm sp
      -> sll_cstep rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> Acc lex_nat_pair (sll_meas rm vi sp)
      -> Acc lex_nat_pair (sll_meas rm vi' sp').
  Proof.
    intros rm sp sp' sps' vi vi' hk heq hi ha.
    eapply Acc_inv; eauto.
    eapply sll_cstep_meas_lt; eauto.
  Defined.
  
  (** Computes the SLL closure of a single subparser, using sim_return for cached returns and sll_cstep otherwise. *)
  Fixpoint sllc (rm : rhs_map)
                (cm : closure_map)
                (vi : NtSet.t)
                (sp : sll_subparser)
                (hk : sll_sp_pushes_from_keyset rm sp)
                (a  : Acc lex_nat_pair (sll_meas rm vi sp))
    : closure_result sll_subparser :=
    match sim_return cm sp with
    | Some sps' => inr sps'
    | None      =>
      match sll_cstep rm vi sp as r return sll_cstep rm vi sp = r -> _ with
      | cstep_done       => fun _  => inr [sp]
      | cstep_error e    => fun _  => inl e
      | cstep_k vi' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hi =>
                                  sllc rm cm vi' sp'
                                       (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                       (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
          in  aggr_closure_results crs
      end eq_refl
    end.

  (** Unfolding lemma for sllc, exposing the sim_return/sll_cstep case split. *)
  Lemma sllc_unfold :
    forall rm cm vi sp hk a,
      sllc rm cm vi sp hk a =
      match sim_return cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sll_cstep rm vi sp as r return sll_cstep rm vi sp = r -> _ with
        | cstep_done       => fun _  => inr [sp]
        | cstep_error e    => fun _  => inl e
        | cstep_k vi' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hi =>
                                    sllc rm cm vi' sp'
                                         (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                          (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
            in  aggr_closure_results crs
        end eq_refl
      end.
  Proof.
    intros rm cm vi sp hk a; destruct a; auto.
  Qed.

  (** Raw case analysis on the result of sllc given a fixed sll_cstep witness. *)
  Lemma sllc_cases' :
    forall (rm  : rhs_map)
           (cm  : closure_map)
           (vi  : NtSet.t)
           (sp  : sll_subparser)
           (hk  : sll_sp_pushes_from_keyset rm sp)
           (a   : Acc lex_nat_pair (sll_meas rm vi sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result sll_subparser)
           (heq : sll_cstep rm vi sp = sr),
      match sim_return cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sr as r return sll_cstep rm vi sp = r -> closure_result sll_subparser with
        | cstep_done       => fun _  => inr [sp]
        | cstep_error e    => fun _  => inl e
        | cstep_k vi' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hi => sllc rm cm vi' sp'
                                                     (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                                       (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
            in  aggr_closure_results crs
        end heq
      end = cr
      -> match cr with
         | inl e =>
           sim_return cm sp = None 
           /\ (sr = cstep_error e
               \/ exists (sps : list sll_subparser)
                         (vi' : NtSet.t)
                         (hs  : sll_cstep rm vi sp = cstep_k vi' sps)
                         (crs : list (closure_result sll_subparser)),
                  crs = dmap sps (fun sp' hi => 
                                    sllc rm cm vi' sp'
                                         (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                         (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                  /\ aggr_closure_results crs = inl e)
         | inr sps =>
           sim_return cm sp = Some sps
           \/ sim_return cm sp = None
              /\ ((sr = cstep_done /\ sps = [sp])
                  \/ exists (sps' : list sll_subparser)
                            (vi'  : NtSet.t)
                            (hs   : sll_cstep rm vi sp = cstep_k vi' sps')
                            (crs  : list (closure_result sll_subparser)),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc rm cm vi' sp'
                                             (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                             (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                     /\ aggr_closure_results crs = inr sps)
         end.
  Proof.
    intros rm cm vi sp hk a sr cr heq.
    dms; tc; intros heq'; try solve [inv heq'; eauto | eauto 10].
  Qed.
  
  (** Case analysis on the result of sllc: characterizes all success and error outcomes. *)
  Lemma sllc_cases :
    forall (rm : rhs_map)
           (cm : closure_map)
           (sp : sll_subparser)
           (vi : NtSet.t)
           (hk : sll_sp_pushes_from_keyset rm sp)
           (a  : Acc lex_nat_pair (sll_meas rm vi sp))
           (cr : closure_result sll_subparser),
      sllc rm cm vi sp hk a = cr
      -> match cr with
         | inl e => 
           sim_return cm sp = None
           /\ (sll_cstep rm vi sp = cstep_error e
               \/ exists (sps : list sll_subparser)
                         (vi' : NtSet.t)
                         (hs  : sll_cstep rm vi sp = cstep_k vi' sps)
                         (crs : list (closure_result sll_subparser)),
                  crs = dmap sps (fun sp' hi => 
                                    sllc rm cm vi' sp'
                                         (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                         (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                  /\ aggr_closure_results crs = inl e)
         | inr sps =>
           sim_return cm sp = Some sps
           \/ sim_return cm sp = None
              /\ ((sll_cstep rm vi sp = cstep_done /\ sps = [sp])
                  \/ exists (sps' : list sll_subparser)
                            (vi'  : NtSet.t)
                            (hs   : sll_cstep rm vi sp = cstep_k vi' sps')
                            (crs  : list (closure_result sll_subparser)),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc rm cm vi' sp'
                                             (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                             (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                     /\ aggr_closure_results crs = inr sps)
                  end.
  Proof.
    intros rm cm vi sp hk a cr hs; subst.
    rewrite sllc_unfold.
    eapply sllc_cases'; eauto.
  Qed.

  (** Specializes sllc_cases to the success outcome, listing all ways sllc can return inr sps. *)
  Lemma sllc_success_cases :
    forall rm cm vi sp hk a sps,
      sllc rm cm vi sp hk a = inr sps
      -> sim_return cm sp = Some sps
         \/ sim_return cm sp = None
            /\ ((sll_cstep rm vi sp = cstep_done /\ sps = [sp])
                \/ exists (sps' : list sll_subparser)
                          (vi'  : NtSet.t)
                          (hs   : sll_cstep rm vi sp = cstep_k vi' sps')
                          (crs  : list (closure_result sll_subparser)),
                   crs = dmap sps' (fun sp' hi => 
                                      sllc rm cm vi' sp'
                                           (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                           (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                   /\ aggr_closure_results crs = inr sps).
  Proof.
    intros ? ? ? ? ? ? sps ?; apply sllc_cases with (cr := inr sps); auto.
  Qed.

  (** Specializes sllc_cases to the error outcome, listing all ways sllc can return inl e. *)
  Lemma sllc_error_cases :
    forall rm cm sp vi hk a e,
      sllc rm cm vi sp hk a = inl e
      -> sim_return cm sp = None
         /\ (sll_cstep rm vi sp = cstep_error e
             \/ exists (sps : list sll_subparser)
                       (vi' : NtSet.t)
                       (hs  : sll_cstep rm vi sp = cstep_k vi' sps)
                       (crs : list (closure_result sll_subparser)),
                crs = dmap sps (fun sp' hi => 
                                  sllc rm cm vi' sp'
                                       (sll_cstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                       (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                /\ aggr_closure_results crs = inl e).
  Proof.
    intros rm cm sp vi hk a e hs; apply sllc_cases with (cr := inl e); auto.
  Qed.

  (** Internal inductive version: sllc does not change any subparser's prediction on success. *)
  Lemma sllc_preserves_prediction' :
    forall rm cm pair (a : Acc lex_nat_pair pair) vi sp sp' sps' hk a',
      pair = sll_meas rm vi sp
      -> sllc rm cm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros rm cm pair a.
    induction a as [pair hlt IH]; intros vi sp sp' sps' hk a' heq hs hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs heq] | [sps'' [av' [hs [crs [heq heq']]]]]]]]; subst.
    - eapply sim_return_preserves_prediction; eauto. 
    - apply in_singleton_eq in hi; subst; auto.
    - (* lemma *)
      eapply aggr_closure_results_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      + apply sll_cstep_preserves_prediction with (sp' := sp'') in hs; auto.
        rewrite hs; auto.
      + eapply sll_cstep_meas_lt; eauto.
  Qed.

  (** sllc preserves predictions: every output subparser has the same prediction as the input. *)
  Lemma sllc_preserves_prediction :
    forall rm cm vi sp sp' sps' hk (a : Acc lex_nat_pair (sll_meas rm vi sp)),
      sllc rm cm vi sp hk a = inr sps'
      -> In sp' sps'
      -> sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros; eapply sllc_preserves_prediction'; eauto.
  Qed.

  (** Internal inductive version: sllc output subparsers all satisfy the keyset push invariant. *)
  Lemma sllc_preserves_pki' :
    forall rm cm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sps',
      pair = sll_meas rm vi sp
      -> sllc rm cm vi sp hk ha' = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sps'' heq hc; subst.
    pose proof hc as hc'; apply sllc_success_cases in hc.
    destruct hc as [hr | [hr [[hc heq] | [sps' [vi' [hc [crs [heq heq']]]]]]]]; subst; intros sp''' hi.
    - eapply sim_return_pki; eauto. 
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggr_closure_results_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      eapply sll_cstep_meas_lt; eauto.
  Qed.

  (** sllc output subparsers all satisfy the keyset push invariant. *)
  Lemma sllc_preserves_pki :
    forall rm cm vi sp sps' hk ha,
      sllc rm cm vi sp hk ha = inr sps'
      -> sll_sp_pushes_from_keyset rm sp
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros; eapply sllc_preserves_pki'; eauto.
  Qed.

  (** Computes the SLL closure of a list of subparsers by running sllc on each and aggregating results. *)
  Definition sll_closure (rm  : rhs_map)
                        (cm  : closure_map)
                        (sps : list sll_subparser)
                        (hk  : all_sll_sp_pushes_from_keyset rm sps) :
                        sum prediction_error (list sll_subparser) :=
    aggr_closure_results (dmap sps (fun sp hi =>
                                    sllc rm cm NtSet.empty sp
                                         (sll_pki_list__pki_mem _ _ sp hk hi)
                                         (lex_nat_pair_wf _))).

  (** Each output subparser of sll_closure has a matching input subparser with the same prediction. *)
  Lemma sll_closure_preserves_prediction :
    forall rm cm sps hk sp' sps',
      sll_closure rm cm sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sll_pred sp' = sll_pred sp.
  Proof.
    intros rm cm sps hk sp' sps' hc hi.
    eapply aggr_closure_results_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi''' [_ hs]]].
    eexists; split; eauto.
    eapply sllc_preserves_prediction; eauto.
  Qed.

  (** sll_closure output subparsers all satisfy the keyset push invariant. *)
  Lemma sll_closure_preserves_pki :
    forall rm cm sps hk sps',
      sll_closure rm cm sps hk = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm sps hk sps'' hc ha sp' hi.
    eapply aggr_closure_results_succ_in_input in hc; eauto.
    destruct hc as [sps' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eapply sllc_preserves_pki; eauto.
  Qed.

  (** Ordered type structure for SLL subparsers, used to build finite sets and maps keyed on subparsers. *)
  Module SllSubparserAsUOT <: UsualOrderedType.

    Module L := ListAsUOT SllFrAsUOT.
    Module P := PairAsUOT GammaAsUOT L.

    Definition t := sll_subparser.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition lt (x y : sll_subparser) : Prop :=
      match x, y with
      | sll_sp pred (fr, frs), sll_sp pred' (fr', frs') =>
        P.lt (pred, fr :: frs) (pred', fr' :: frs')
      end.

    Lemma lt_trans :
      forall x y z,
        lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros [p (f, fs)] [p' (f', fs')] [p'' (f'', fs'')];
        apply P.lt_trans.
    Qed.

    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros [p (f, fs)] [p' (f', fs')] hl he; inv he.
      eapply P.lt_not_eq; eauto.
    Qed.

    Definition compare (x y : sll_subparser) : Compare lt eq x y.
      refine (match x, y with
              | sll_sp pred (fr, frs), sll_sp pred' (fr', frs') =>
                match P.compare (pred, fr :: frs) (pred', fr' :: frs') with
                | LT hl => LT _
                | GT he => GT _
                | EQ hl => EQ _
                end
              end); red; tc.
    Defined.

    Definition eq_dec (x y : sll_subparser) : {x = y} + {x <> y}.
      refine (match x, y with
              | sll_sp pred (fr, frs), sll_sp pred' (fr', frs') =>
                match P.eq_dec (pred, fr :: frs) (pred', fr' :: frs') with
                | left he  => left _
                | right hn => right _
                end
              end); tc.
    Defined.

  End SllSubparserAsUOT.

  (* Physical-identity fast path: sll_subparser values are built purely
     functionally and never mutated in place, so pointer-equal arguments
     are trivially structurally equal. Crane extracts this functor's body
     once as a C++ template shared across all grammar instantiations, so
     the guard is placed here (on the functor-internal definition) rather
     than on any single grammar's monomorphized copy. *)
  Crane Guard Compare SllSubparserAsUOT.compare => EQ.

  Module SllSpSet := FSetList.Make SllSubparserAsUOT.

  (** Converts a list of SLL subparsers into a finite set (deduplicating). *)
  Definition setify (sps : list sll_subparser) : SllSpSet.t :=
    fold_right SllSpSet.add SllSpSet.empty sps.

  (** A cache key is a pair of (current subparser list, next terminal) used to memoize target computations. *)
  Definition cache_key := (list sll_subparser * terminal)%type.

  (** Ordered type structure for cache keys, enabling the AVL-tree map implementation. *)
  Module CacheKeyAsUOT <: UsualOrderedType.

    Module L := ListAsUOT SllSubparserAsUOT.
    Module P := PairAsUOT L TAsUOT.

    Definition t := cache_key.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    (* Try flipping the order of the pair,
       in case that leads to fail fast behavior *)
    Definition lt (x y : cache_key) : Prop :=
      P.lt x y.

    Lemma lt_trans :
      forall x y z,
        lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros (sps, a) (sps', a') (sps'', a''); apply P.lt_trans.
    Qed.

    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros (sps, a) (sps', a') hl he; inv he.
      eapply P.lt_not_eq; eauto.
    Qed.

    Definition compare : forall x y : cache_key, Compare lt eq x y :=
      P.compare.

    Definition eq_dec : forall x y : cache_key, {x = y} + {x <> y} :=
      P.eq_dec.

  End CacheKeyAsUOT.

  (* Same physical-identity fast path as SllSubparserAsUOT.compare above:
     cache_key values are purely functional and immutable, so pointer-equal
     arguments are trivially structurally equal. *)
  Crane Guard Compare CacheKeyAsUOT.compare => EQ.

  Module Cache      := FMapAVL.Make CacheKeyAsUOT.
  Module CacheFacts := FMapFacts.Facts Cache.

  (* Bisecting a hang under global `Set Crane Arena`: the memoization cache
     is a persistent AVL map that grows via path-copying, so its internal
     nodes are heavily aliased across many distinct top-level cache values
     over the life of one parse (unlike `Defs.tree`, which is built once and
     never re-derived from itself). This is a strong suspect for the hang,
     so it's opted out of arena mode here while the rest of global arena is
     bisected. See project_crane_arena_ambient memory. *)
  Crane NoArena Cache.Raw.tree.
  
  (* A cache is a finite map with (list subparser * terminal) keys
     and (list subparser) values *)
  (** The type of the SLL prediction cache mapping (subparser list, terminal) to target subparser lists. *)
  Definition cache : Type := Cache.t (list sll_subparser).

  (** The initial empty cache containing no memoized SLL target results. *)
  Definition empty_cache : cache := Cache.empty (list sll_subparser).
  
  (** Computes the SLL target: applies sll_move on terminal a then sll_closure on the result. *)
  Definition sll_target (rm   : rhs_map)
                       (cm   : closure_map)
                       (a    : terminal)
                       (sps  : list sll_subparser)
                       (hk   : all_sll_sp_pushes_from_keyset rm sps) :
                       sum prediction_error (list sll_subparser) :=
    match sll_move a sps as m return sll_move a sps = m -> _ with
    | inl e    => fun _ => inl e
    | inr sps' =>
      fun hm =>
        match sll_closure rm cm sps' (sll_move_preserves_pki rm a sps sps' hk hm) with
        | inl e     => inl e
        | inr sps'' => inr sps''
        end
    end eq_refl.

  (** Raw case analysis on sll_target given a fixed sll_move witness. *)
  Lemma sll_target_cases' :
    forall rm cm a sps hk mr (heq : sll_move a sps = mr) tr,
      match mr as m return sll_move a sps = m -> _ with
      | inl e    => fun _ => inl e
      | inr sps' =>
        fun hm =>
          match sll_closure rm cm sps' (sll_move_preserves_pki rm a sps sps' hk hm) with
          | inl e     => inl e
          | inr sps'' => inr sps''
          end
      end heq = tr
      -> match tr with
         | inl e =>
           sll_move a sps = inl e
           \/ (exists sps' hk',
                  sll_move a sps = inr sps' /\ sll_closure rm cm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', sll_move a sps = inr sps'
                            /\ sll_closure rm cm sps' hk' = inr sps''
         end.
  Proof.
    intros rm cm a sps hk mr heq tr.
    destruct mr as [e' | sps']; intros ?; subst; auto.
    destruct (sll_closure _ _ _ _) eqn:hc; eauto.
  Qed.

  (** Case analysis on sll_target: either move fails, closure fails, or both succeed. *)
  Lemma sll_target_cases :
    forall rm cm a sps hk tr,
      sll_target rm cm a sps hk = tr
      -> match tr with
         | inl e =>
           sll_move a sps = inl e
           \/ (exists sps' hk',
                  sll_move a sps = inr sps' /\ sll_closure rm cm sps' hk' = inl e) 
         | inr sps'' =>
           (exists sps' hk',
               sll_move a sps = inr sps' /\ sll_closure rm cm sps' hk' = inr sps'')
         end.
  Proof.
    intros rm cm a sps hk tr ht; eapply sll_target_cases'; eauto.
  Qed.

  (** Every output subparser of a successful sll_target traces back to an input subparser with the same prediction. *)
  Lemma sll_target_preserves_prediction :
    forall rm cm a sps hk sp' sps',
      sll_target rm cm a sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sll_pred sp = sll_pred sp'.
  Proof.
    intros rm cm a sps hk sp' sps'' hs hi.
    apply sll_target_cases in hs.
    destruct hs as [sps' [hk' [hm hc]]].
    eapply sll_closure_preserves_prediction in hc; eauto.
    destruct hc as [sp'' [hi'' heq]]; rewrite heq.
    eapply sll_move_preserves_prediction in hm; eauto.
    destruct hm as [? [? ?]]; eauto.
  Qed.

  (** sll_target output subparsers satisfy the keyset push invariant. *)
  Lemma sll_target_preserves_pki :
    forall rm cm a sps hk sps',
      sll_target rm cm a sps hk = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm a sps hk sps'' ht ha.
    apply sll_target_cases in ht.
    destruct ht as [sps' [hk' [hm hc]]].
    eapply sll_closure_preserves_pki; eauto.
  Qed.

  (** The cache invariant: every stored result is a genuine sll_target success for some keyset proof. *)
  Definition cache_stores_target_results rm cm ca :=
    forall sps a sps',
      Cache.find (sps, a) ca = Some sps'
      -> exists hk, sll_target rm cm a sps hk = inr sps'.
  
  (** Adding a fresh sll_target result to the cache preserves the cache invariant. *)
  Lemma sll_target_add_preserves_cache_invar :
    forall rm cm ca sps a sps' hk,
      cache_stores_target_results rm cm ca
      -> sll_target rm cm a sps hk = inr sps'
      -> cache_stores_target_results rm cm (Cache.add (sps, a) sps' ca).
  Proof.
    intros rm cm ca sps a sps' hk hc ht ka kb v hf.
    destruct (CacheKeyAsUOT.eq_dec (ka, kb) (sps, a)) as [he | hn].
    - inv he; rewrite CacheFacts.add_eq_o in hf; inv hf; eauto.
    - rewrite CacheFacts.add_neq_o in hf; auto.
  Qed.

  (** A cached result satisfies the keyset push invariant, because it was computed by sll_target. *)
  Lemma cache_lookup_preserves_pki :
    forall rm cm sps a ca sps',
      cache_stores_target_results rm cm ca
      -> Cache.find (sps, a) ca = Some sps'
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm sps a ca sps' hc hf.
    apply hc in hf.
    destruct hf as [hk ht].
    eapply sll_target_preserves_pki; eauto.
  Qed.

  (** Returns true iff the subparser has reached a final configuration (empty stack, no callers). *)
  Definition sll_final_config (sp : sll_subparser) : bool :=
    match sp with
    | sll_sp _ (sll_fr None [], []) => true
    | _ => false
    end.

  (** If a subparser is in final config, its stack is precisely the empty bottom stack. *)
  Lemma sll_final_config_empty_stack :
    forall sp pred stk,
      sp = sll_sp pred stk
      -> sll_final_config sp = true
      -> stk = (sll_fr None [], []).
  Proof.
    intros sp pred stk ? hf; subst; unfold sll_final_config in hf; dms; tc.
  Qed.

  (** Collects final-config subparsers and returns pred_succ if all agree, pred_ambig if they disagree, pred_reject if none. *)
  Definition sll_handle_final_subparsers (sps : list sll_subparser) : prediction_result :=
    match filter sll_final_config sps with
    | []         => pred_reject
    | sp :: sps' => 
      if all_predictions_equal_b beq_gamma sll_pred sp sps' then
        pred_succ sp.(sll_pred)
      else
        pred_ambig sp.(sll_pred)
    end.

  (** A pred_succ result from sll_handle_final_subparsers implies a final-config subparser with the predicted rhs. *)
  Lemma sll_handle_final_subparsers_succ_facts :
    forall sps rhs,
      sll_handle_final_subparsers sps = pred_succ rhs
      -> exists sp o,
        In sp sps
        /\ sp.(sll_pred) = rhs
        /\ sp.(sll_stk) = (sll_fr o [], []).
  Proof.
    intros sps rhs hh.
    unfold sll_handle_final_subparsers in hh.
    destruct (filter _ _) as [| sp sps'] eqn:hf; tc.
    destruct (all_predictions_equal_b _ _ _ _); tc; inv hh.
    assert (hin : In sp (filter sll_final_config sps)).
    { rewrite hf; apply in_eq. }
    apply filter_In in hin.
    destruct hin as [hin ht]; subst.
    unfold sll_final_config in ht.
    destruct sp as [pred ([o suf], frs)]; dms; tc.
    repeat eexists; eauto.
  Qed.

  (** A pred_ambig result implies some subparser in the list carries the ambiguous prediction. *)
  Lemma sll_handle_final_subparsers_ambig_from_subparsers :
    forall sps gamma,
      sll_handle_final_subparsers sps = pred_ambig gamma
      -> exists sp, In sp sps /\ sp.(sll_pred) = gamma.
  Proof.
    intros sps gamma hh.
    unfold sll_handle_final_subparsers in hh.
    dmeqs h; tc; inv hh.
    eexists; split; eauto.
    eapply filter_cons_in; eauto.
  Qed.
  
  (** The main SLL prediction loop: consumes tokens one at a time, short-circuits if all predictions agree, uses the cache for repeated configurations. *)
  Fixpoint sll_predict' (rm  : rhs_map)
                       (cm  : closure_map)
                       (sps : list sll_subparser)
                       (ts  : list token)
                       (ca  : cache)
                       (hk  : all_sll_sp_pushes_from_keyset rm sps)
                       (hc  : cache_stores_target_results rm cm ca) :
                       prediction_result * cache :=
    match ts with
    | []            => (sll_handle_final_subparsers sps, ca)
    | @existT _ _ a _ :: ts' =>
      match sps with
      | []          => (pred_reject, ca)
      | sp' :: sps' =>
        if all_predictions_equal_b beq_gamma sll_pred sp' sps' then
          (pred_succ sp'.(sll_pred), ca)
        else
          match Cache.find (sps, a) ca as f
                return Cache.find (sps, a) ca = f -> _ with 
          | Some sps'' =>
            fun hf =>
               sll_predict' rm cm sps'' ts' ca
                          (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc
          | None =>
            fun _ =>
              match sll_target rm cm a sps hk as t
                    return sll_target rm cm a sps hk = t -> _ with
              | inl e     => fun _ => (pred_error e, ca)
              | inr sps'' =>
                fun ht => 
                  let ca' := Cache.add (sps, a) sps'' ca
                  in  sll_predict' rm cm sps'' ts' ca'
                                  (sll_target_preserves_pki _ _ _ _ _ _ ht hk)
                                  (sll_target_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht)
              end eq_refl
          end eq_refl
      end
    end.

  (** Case analysis for the continuation step of sll_predict': covers cache-hit and cache-miss paths. *)
  Lemma sll_predict'_cont_cases :
    forall rm cm sps a ts' ca hk hc fr tr pr
           (heq : Cache.find (sps, a) ca = fr)
           (heq' : sll_target rm cm a sps hk = tr),
      match fr as f return Cache.find (sps, a) ca = f -> _ with 
      | Some sps'' =>
        fun hf =>
          sll_predict' rm cm sps'' ts' ca
                      (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc
      | None =>
        fun _ =>
          match tr as t return sll_target rm cm a sps hk = t -> _ with
          | inl e     => fun _ => (pred_error e, ca)
          | inr sps'' =>
            fun ht => 
              let ca' := Cache.add (sps, a) sps'' ca
              in  sll_predict' rm cm sps'' ts' ca'
                              (sll_target_preserves_pki _ _ _ _ _ _ ht hk)
                              (sll_target_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht)
          end heq'
      end heq = pr
      -> match pr with
         | (pred_succ ys, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sll_predict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (pred_succ ys, ca'))
           \/ (exists sps'' (ht : sll_target rm cm a sps hk = inr sps''),
                  sll_predict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sll_target_preserves_pki _ _ _ _ _ _ ht hk)
                              (sll_target_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (pred_succ ys, ca'))
         | (pred_ambig ys, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sll_predict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (pred_ambig ys, ca'))
           \/ (exists sps'' (ht : sll_target rm cm a sps hk = inr sps''),
                  sll_predict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sll_target_preserves_pki _ _ _ _ _ _ ht hk)
                              (sll_target_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (pred_ambig ys, ca'))
         | (pred_reject, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sll_predict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (pred_reject, ca'))
           \/ (exists sps'' (ht : sll_target rm cm a sps hk = inr sps''),
                  sll_predict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sll_target_preserves_pki _ _ _ _ _ _ ht hk)
                              (sll_target_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (pred_reject, ca'))
         | (pred_error e, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sll_predict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (pred_error e, ca'))
           \/ sll_target rm cm a sps hk = inl e
           \/ (exists sps'' (ht : sll_target rm cm a sps hk = inr sps''),
                  sll_predict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sll_target_preserves_pki _ _ _ _ _ _ ht hk)
                              (sll_target_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (pred_error e, ca'))
         end.
  Proof.
    intros rm cm sps a ts' ca hk hc fr tr pr heq heq';
      dms; intros heq''; inv heq''; eauto.
  Qed.

  (** A successful sll_predict' run produces a cache that still satisfies the cache invariant. *)
  Lemma sll_predict'_succ_preserves_cache_invar :
    forall rm cm ts sps ca hk hc ys ca',
      sll_predict' rm cm sps ts ca hk hc = (pred_succ ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros rm cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca hk hc ys ca' hs; sis.
    - dms; tc; inv hs; auto.
    - dm; tc; dm; try solve [inv hs; auto].
      apply sll_predict'_cont_cases in hs.
      destruct hs as [[sps'' [hf hs]] | [sps'' [ht hs]]]; eauto.
  Qed.

  (** A successful sll_predict' result ys corresponds to some initial subparser's prediction. *)
  Lemma sll_predict'_success_result_in_original_subparsers :
    forall rm cm ts sps ca hk hc ys ca',
      sll_predict' rm cm sps ts ca hk hc = (pred_succ ys, ca')
      -> exists sp, In sp sps /\ sp.(sll_pred) = ys.
  Proof.
    intros rm cm ts. 
    induction ts as [| (a,l) ts IH]; intros sps ca hk hc ys ca' hp; sis.
    - injection hp; intros _ hh. 
      apply sll_handle_final_subparsers_succ_facts in hh.
      destruct hh as (sp' & _ & hi & heq & _); eauto.
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall.
      + inv hp; exists sp'; split; auto; apply in_eq.
      + apply sll_predict'_cont_cases in hp.
        destruct hp as [[sps'' [hf hp]] | [sps'' [ht hp]]].
        * apply IH in hp; auto; destruct hp as [sp'' [hi heq]]; subst.
          apply hc in hf; destruct hf as [hk' ht].
          eapply sll_target_preserves_prediction; eauto.
        * apply IH in hp.
          destruct hp as [sp'' [hi ?]]; subst.
          eapply sll_target_preserves_prediction; eauto.
  Qed.
  
  (** Creates the initial SLL subparsers for nonterminal x: one per production, each predicting its own rhs. *)
  Definition sll_init_sps (rm : rhs_map) (x : nonterminal) : list sll_subparser :=
    map (fun rhs => sll_sp rhs (sll_fr (Some x) rhs, []))
        (rhss_for x rm).

  (** Every initial SLL subparser's prediction is a known rhs for nonterminal x. *)
  Lemma sll_init_sps_prediction_in_rhss_for :
    forall rm x sp,
      In sp (sll_init_sps rm x)
      -> In sp.(sll_pred) (rhss_for x rm).
  Proof.
    intros rm x sp hi; unfold sll_init_sps in hi.
    apply in_map_iff in hi; firstorder; subst; auto.
  Qed.

  (** The initial SLL subparsers for x all satisfy the keyset push invariant. *)
  Lemma sll_init_sps_pki :
    forall rm x,
      all_sll_sp_pushes_from_keyset rm (sll_init_sps rm x).
  Proof.
    intros rm x sp hi.
    apply in_map_iff in hi; destruct hi as [? [heq hi]]; subst.
    repeat red; auto.
  Qed.

  (** Computes the SLL start state for x: closure of all initial subparsers for x. *)
  Definition sll_start_state (rm : rhs_map)
                           (cm : closure_map)
                           (x  : nonterminal) :
                           sum prediction_error (list sll_subparser) :=
    sll_closure rm cm (sll_init_sps rm x) (sll_init_sps_pki rm x).

  (** Every subparser produced by sll_start_state has a prediction that is a valid rhs for x. *)
  Lemma sll_start_state_sp_prediction_in_rhss_for :
    forall rm cm x sp' sps',
      sll_start_state rm cm x = inr sps'
      -> In sp' sps'
      -> In sp'.(sll_pred) (rhss_for x rm).
  Proof.
    intros rm cm x sp' sps' hs hi.
    unfold sll_start_state in hs.
    eapply sll_closure_preserves_prediction in hs; eauto.
    destruct hs as [sp [hi' heq]]; rewrite heq.
    apply sll_init_sps_prediction_in_rhss_for; auto.
  Qed.

  (** The SLL start state subparsers all satisfy the keyset push invariant. *)
  Lemma sll_start_state_pki :
    forall rm cm x sps,
      sll_start_state rm cm x = inr sps
      -> all_sll_sp_pushes_from_keyset rm sps.
  Proof.
    intros rm cm x sps hs sp hi.
    eapply sll_closure_preserves_pki; eauto.
    apply sll_init_sps_pki.
  Qed.
  
  (** Top-level SLL prediction for nonterminal x on token stream ts, using the closure map and cache. *)
  Definition sll_predict (rm : rhs_map)
                        (cm : closure_map)
                        (x  : nonterminal)
                        (ts : list token)
                        (ca : cache)
                        (hc : cache_stores_target_results rm cm ca) :
                        prediction_result * cache :=
    match sll_start_state rm cm x as s return sll_start_state rm cm x = s -> _ with
    | inl msg => fun _  => (pred_error msg, ca)
    | inr sps => fun hs => sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc
    end eq_refl.

  (** Raw case analysis on sll_predict given a fixed start-state witness. *)
  Lemma sll_predict_cases' :
    forall rm cm x ts ca hc cr pr (heq : sll_start_state rm cm x = cr),
      match cr as s return sll_start_state rm cm x = s -> _ with
      | inl msg => fun _  => (pred_error msg, ca)
      | inr sps => fun hs => sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc
      end heq = pr
      -> match pr with
         | (pred_succ ys, ca') =>
           (exists sps (hs : sll_start_state rm cm x = inr sps),
               sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_succ ys, ca'))
         | (pred_ambig ys, ca') =>
           (exists sps (hs : sll_start_state rm cm x = inr sps),
               sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_ambig ys, ca'))
         | (pred_reject, ca') =>
           (exists sps (hs : sll_start_state rm cm x = inr sps),
               sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_reject, ca'))
         | (pred_error e, ca') =>
           sll_start_state rm cm x = inl e
           \/ (exists sps (hs : sll_start_state rm cm x = inr sps),
                  sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_error e, ca'))
         end.
  Proof.
    intros rm cm x ts ca hc cr pr heq; dms; intros heq'; inv heq'; eauto.
  Qed.

  (** Case analysis on sll_predict: the start state either errors or passes control to sll_predict'. *)
  Lemma sll_predict_cases :
    forall rm cm x ts ca hc pr,
      sll_predict rm cm x ts ca hc = pr
      -> match pr with
         | (pred_succ ys, ca') =>
           (exists sps (hs : sll_start_state rm cm x = inr sps),
               sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_succ ys, ca'))
         | (pred_ambig ys, ca') =>
           (exists sps (hs : sll_start_state rm cm x = inr sps),
               sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_ambig ys, ca'))
         | (pred_reject, ca') =>
           (exists sps (hs : sll_start_state rm cm x = inr sps),
               sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_reject, ca'))
         | (pred_error e, ca') =>
           sll_start_state rm cm x = inl e
           \/ (exists sps (hs : sll_start_state rm cm x = inr sps),
                  sll_predict' rm cm sps ts ca (sll_start_state_pki _ _ _ _ hs) hc = (pred_error e, ca'))
         end.
  Proof.
    intros; eapply sll_predict_cases'; eauto.
  Qed.

  (** A successful sll_predict result is always one of x's right-hand sides in the rhs map. *)
  Lemma sll_predict_succ_in_rhss_for :
    forall rm cm x ts ca hc ys ca',
      sll_predict rm cm x ts ca hc = (pred_succ ys, ca')
      -> In ys (rhss_for x rm).
  Proof.
    intros rm cm x ts ca hc ys ca' hs.
    apply sll_predict_cases in hs.
    destruct hs as [sps [hs hp]].
    eapply sll_predict'_success_result_in_original_subparsers in hp; eauto.
    destruct hp as [sp [hi heq]]; subst.
    eapply sll_start_state_sp_prediction_in_rhss_for; eauto.
  Qed.

  (** A successful sll_predict produces a cache that still satisfies the cache invariant. *)
  Lemma sll_predict_succ_preserves_cache_invar :
    forall rm cm x ts ca hc ys ca',
      sll_predict rm cm x ts ca hc = (pred_succ ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros rm cm x ts ca hc ys ca' hs.
    apply sll_predict_cases in hs.
    destruct hs as [sps [hs hp]].
    eapply sll_predict'_succ_preserves_cache_invar; eauto.
  Qed.
      
  (** Adaptive prediction: runs SLL first, falls back to LL only if SLL returns pred_ambig. *)
  Definition adaptive_predict
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (cm  : closure_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame)
             (ts  : list token)
             (ca  : cache)
             (hc  : cache_stores_target_results rm cm ca)
             (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)) :
    prediction_result * cache :=
    let sll_res := sll_predict rm cm x ts ca hc
    in  match sll_res with
        | (pred_ambig _, _) => (ll_predict g hw rm pre vs x suf frs ts hk, ca)
        | _                => sll_res
        end.
  
  (** A successful adaptive_predict result is always one of x's right-hand sides in the rhs map. *)
  Lemma adaptive_predict_succ_in_rhss_for :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      adaptive_predict g hw rm cm pre vs x suf frs ts ca hc hk = (pred_succ ys, ca')
      -> In ys (rhss_for x rm).
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' ha.
    unfold adaptive_predict in ha; dmeqs h; tc; inv ha.
    - eapply sll_predict_succ_in_rhss_for; eauto.
    - eapply ll_predict_succ_in_rhss_for; eauto.
  Qed.
  
  (** A successful adaptive_predict result (x, ys) is a production in the grammar. *)
  Lemma adaptive_predict_succ_in_grammar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      rhs_map_correct rm g
      -> adaptive_predict g hw rm cm pre vs x suf frs ts ca hc hk = (pred_succ ys, ca')
      -> PM.In (x, ys) g.
  Proof.
    intros.
    eapply rhss_for_in_iff; eauto.
    eapply adaptive_predict_succ_in_rhss_for; eauto.
  Qed.

  (** An ambiguous adaptive_predict result (x, ys) is still a production in the grammar. *)
  Lemma adaptive_predict_ambig_in_grammar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      rhs_map_correct rm g
      -> adaptive_predict g hw rm cm pre vs x suf frs ts ca hc hk = (pred_ambig ys, ca')
      -> PM.In (x, ys) g.
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' hp ha.
    unfold adaptive_predict in ha; dms; tc; inv ha.
    eapply ll_predict_ambig_in_grammar; eauto.
  Qed.

  (** A successful adaptive_predict produces a cache still satisfying the cache invariant. *)
  Lemma adaptive_predict_succ_preserves_cache_invar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      adaptive_predict g hw rm cm pre vs x suf frs ts ca hc hk = (pred_succ ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' ha.
    unfold adaptive_predict in ha; dmeqs H; inv ha; auto.
    eapply sll_predict_succ_preserves_cache_invar; eauto.
  Qed.

  (** An ambiguous adaptive_predict result also preserves the cache invariant. *)
  Lemma adaptive_predict_ambig_preserves_cache_invar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      adaptive_predict g hw rm cm pre vs x suf frs ts ca hc hk = (pred_ambig ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' ha.
    unfold adaptive_predict in ha; dmeqs H; inv ha; auto.
  Qed.
  
End SllPredictionFn. 
