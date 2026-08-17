(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Arith Bool FMaps Lia List MSets PeanoNat Program.Wf String.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Termination.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.
Open Scope list_scope.

(* Key functions defined in this module:

   move
   LLclosure
   LLtarget
   LLpredict'
   initSps
   startState
   LLpredict
   
*)

Module LLPredictionFn (Import D : Defs.T).

  Module Export Term := TerminationFn D.

  (* result_error values that the prediction mechanism can return *)
  (** result_error codes that can arise during LL prediction: invalid stack state or detected left recursion. *)
  Inductive prediction_error :=
  | sp_invalid_state  : prediction_error
  | sp_left_recursion : nonterminal -> prediction_error.

  (** Converts a prediction error to a human-readable string for diagnostics. *)
  Definition show_prediction_error (e : prediction_error) : string :=
    match e with
    | sp_invalid_state    => "sp_invalid_state"
    | sp_left_recursion x => "sp_left_recursion " ++ showNT x
    end.
  
  (* "move" operation *)

  (** Result type for advancing a single subparser over a terminal token. *)
  Inductive subparser_move_result {A : Type} : Type :=
  | move_succ   : A -> subparser_move_result 
  | move_reject : subparser_move_result 
  | move_error  : prediction_error -> subparser_move_result.

  (** Injectivity of [move_succ]: equal results imply equal subparsers. *)
  Lemma inv_move_succ_eq :
    forall (sp sp' : subparser),
      move_succ sp = move_succ sp' -> sp = sp'.
  Proof.
    intros sp sp' heq; inv heq; auto.
  Qed.
  
  (** Advances a single subparser by consuming token [t], matching the next terminal symbol. *)
  Definition move_sp (t  : token) (sp : subparser) : subparser_move_result :=
    match t with
    | @existT _ _ a' v' =>
      match sp with
      | Sp pred stk =>
        match stk with
        (* stack is exhausted *)
        | (Fr _ _ [], [])         => move_reject
        (* impossible case *)
        | (Fr _ _ [], _ :: _)     => move_error sp_invalid_state
        (* impossible case *)
        | (Fr _ _ (NT _ :: _), _) => move_error sp_invalid_state
        (* try to consume a token *)
        | (Fr pre v (T a :: suf), frs) =>
          if t_eq_dec a' a then
            move_succ (Sp pred (Fr (T a' :: pre) (v', v) suf, frs))
          else
            move_reject
        end
      end
    end.

  (** Moving a subparser does not change its prediction (the chosen RHS). *)
  Lemma move_sp_preserves_prediction :
    forall t sp sp',
      move_sp t sp = move_succ sp'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros t sp sp' hm; unfold move_sp in hm.
    dms; tc; subst; inv hm; auto.
  Qed.

  (** Explicit characterization of [move_sp] success: a terminal-headed frame advances by one symbol. *)
  Lemma move_sp_succ_step :
    forall sp sp' pre a v v' suf frs pred,
      sp = Sp pred (Fr pre v (T a :: suf), frs)
      -> sp' = Sp pred (Fr (T a :: pre) (v', v) suf, frs)
      -> move_sp (@existT _ _ a v') sp = move_succ sp'.
  Proof.
    intros; subst; unfold move_sp; dms; tc.
  Qed.
  
  (** [move_sp] preserves the keyset invariant: all pushes come from nonterminals in the rhs_map. *)
  Lemma move_sp_preserves_pki :
    forall rm a sp sp',
      sp_pushes_from_keyset rm sp
      -> move_sp a sp = move_succ sp'
      -> sp_pushes_from_keyset rm sp'.
  Proof.
    intros rm a sp sp' hk hm.
    unfold move_sp in hm; dms; tc; inv hm; sis.
    red; red in hk; sis.
    eapply consume_preserves_keyset_invar; eauto.
  Qed.
  
  (** Result type for a batch move operation: either an error or a list of advanced subparsers. *)
  Definition move_result (A : Type) := sum prediction_error (list A).

  (* consider refactoring to short-circuit in case of error *)
  (** Aggregates a list of individual move results, propagating the first error or collecting successes. *)
  Fixpoint aggr_move_results {A : Type} (rs : list (@subparser_move_result A)) : (move_result A) :=
    match rs with
    | []       => inr []
    | r :: rs' =>
      match (r, aggr_move_results rs') with
      | (move_error e, _)       => inl e
      | (_, inl e)             => inl e
      | (move_succ sp, inr sps) => inr (sp :: sps)
      | (move_reject, inr sps)  => inr sps
      end
    end.

  (** Every subparser in the aggregated success list came from a [move_succ] entry in the input. *)
  Lemma aggr_move_results_succ_in_input :
    forall (A   : Type)
           (rs  : list (@subparser_move_result A))
           (sp  : A)
           (sps : list A),
      aggr_move_results rs = inr sps
      -> In sp sps
      -> In (move_succ sp) rs.
  Proof.
    intros A rs sp.
    induction rs as [| r rs' IH]; intros sps ha hi; sis.
    - inv ha; inv hi.
    - destruct r as [sp' | | e];
        destruct (aggr_move_results rs') as [e' | sps']; tc; inv ha.
      + inv hi; firstorder.
      + firstorder.
  Qed.

  (** If aggregation returns an error, that error appears as [move_error] in the input list. *)
  Lemma aggr_move_results_error_in_input :
    forall (A : Type)
           (smrs : list (@subparser_move_result A))
           (e    : prediction_error),
      aggr_move_results smrs = inl e
      -> In (move_error e) smrs.
  Proof.
    intros A smrs e ha.
    induction smrs as [| smr smrs' IH]; sis; tc.
    destruct smr as [sp' | | e'];
      destruct (aggr_move_results smrs') as [e'' | sps']; tc; inv ha; eauto.
  Qed.

  (** Backward direction: each result subparser traces back to some input via [f]. *)
  Lemma aggr_move_results_map_backwards :
    forall A (f : A -> subparser_move_result) (sp' : A) sps sps',
      aggr_move_results (map f sps) = inr sps'
      -> In sp' sps'
      -> exists sp,
          In sp sps
          /\ f sp = move_succ sp'.
  Proof.
    intros A f sp' sps; induction sps as [| sp sps IH]; intros sps' ha hi.
    - inv ha; inv hi.
    - simpl in ha.
      dmeq hf; tc.
      + dmeq ha'; tc.
        inv ha.
        destruct hi as [hh | ht]; subst.
        * eexists; split; [apply in_eq | auto].
        * apply IH in ht; auto.
          destruct ht as [sp'' [hi heq]].
          eexists; split; [apply in_cons; eauto | auto].
      + dmeq ha'; tc.
        inv ha.
        apply IH in hi; auto.
        destruct hi as [sp'' [hi heq]].
        eexists; split; [apply in_cons; eauto | auto].
  Qed.
  
  (** Advances all subparsers in [sps] over token [t], collecting successes and propagating errors. *)
  Definition move (t : token) (sps : list subparser) : (move_result subparser) :=
    aggr_move_results (map (move_sp t) sps).

  (** Unfolds the definition of [move] for use in proofs. *)
  Lemma move_unfold :
    forall t sps,
      move t sps = aggr_move_results (map (move_sp t) sps).
  Proof. 
    auto. 
  Qed.

  (** Every subparser produced by [move] has the same prediction as some input subparser. *)
  Lemma move_preserves_prediction :
    forall t sp' sps sps',
      move t sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
  Proof.
    intros t sp' sps sps' hm hi.
    unfold move in hm.
    eapply aggr_move_results_succ_in_input in hm; eauto.
    eapply in_map_iff in hm; destruct hm as [sp [hmsp hi']].
    eexists; split; eauto.
    eapply move_sp_preserves_prediction; eauto.
  Qed.

  (** If one subparser in [sps] moves to [sp'], then [sp'] appears in the aggregated result. *)
  Lemma aggr_move_results_succ_all_sps_step :
    forall t sp sps sp' sps',
      In sp sps
      -> move_sp t sp = move_succ sp'
      -> aggr_move_results (map (move_sp t) sps) = inr sps'
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

  (** [move] correctly maps [move_sp]: if [sp] moves to [sp'], then [sp'] is in [move]'s output. *)
  Lemma move_maps_move_sp :
    forall t sp sp' sps sps',
      In sp sps
      -> move_sp t sp = move_succ sp'
      -> move t sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros t sp sp' sps sps' hi hm hm'.
    eapply aggr_move_results_succ_all_sps_step; eauto.
  Qed.

  (** Concrete instance: a terminal-headed subparser produces the expected post-move subparser. *)
  Lemma move_succ_all_sps_step :
    forall sp sp' pred pre v a suf v' frs sps sps',
      sp = Sp pred (Fr pre v (T a :: suf), frs)
      -> sp' = Sp pred (Fr (T a :: pre) (v', v) suf, frs)
      -> In sp sps
      -> move (@existT _ _ a v') sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros; subst.
    eapply move_maps_move_sp; eauto.
    eapply move_sp_succ_step; eauto.
  Qed.

  (** [move] preserves the keyset invariant across all surviving subparsers. *)
  Lemma move_preserves_pki :
    forall rm a sps sps',
      all_sp_pushes_from_keyset rm sps
      -> move a sps = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm a sps sps' hk hm sp' hi'.
    eapply aggr_move_results_map_backwards in hm; eauto.
    destruct hm as [sp [hi hm]].
    eapply move_sp_preserves_pki; eauto.
  Qed.

  (* "closure" operation *)

  (** Result type for a single epsilon-closure step: done (stable), continue with new subparsers, or error. *)
  Inductive subparser_closure_step_result {A : Type} :=
  | cstep_done   : subparser_closure_step_result
  | cstep_k      : NtSet.t -> list A -> subparser_closure_step_result
  | cstep_error  : prediction_error -> subparser_closure_step_result.

  (** Performs one closure step: return to caller (reduce), halt on a terminal head, or push for a nonterminal head. *)
  Definition cstep
             (gr : grammar)
             (hw : grammar_wf gr)
             (rm : rhs_map)
             (vi : NtSet.t)
             (sp : subparser) :
    subparser_closure_step_result :=
    match sp with
    | Sp pred (fr, frs) =>
      match fr with
      (* return case *)
      | Fr pre vs [] =>
        match frs with
        (* stack is exhausted *)
        | [] => cstep_done
        (* return to caller frame *)
        | Fr pre_cr vs_cr (NT x :: suf_cr) :: frs' =>
          let pre' := rev pre in
          let vs'  := rev_tuple pre vs in
          match find_predicate_and_action (x, pre') gr hw with
          (* check semantic predicate and reduce *)
          | Some (p, f) =>
            if p vs' then
              let stk' := (Fr (NT x :: pre_cr) (f vs', vs_cr) suf_cr, frs')
              in  cstep_k (NtSet.remove x vi) [Sp pred stk']
            else
              (* failed semantic predicate *)
              cstep_k NtSet.empty []
          | None =>
            (* impossible case *)
            cstep_error sp_invalid_state
          end
        | _ => cstep_error sp_invalid_state
        end
      (* consume case *)
      | Fr _ _ (T _ :: _) => cstep_done
      (* push case *)
      | Fr pre v (NT x :: suf) =>
        if NtSet.mem x vi then
          (* unreachable for a left-recursive grammar *)
          match NM.find x rm with
          | Some _ => cstep_error (sp_left_recursion x)
          | None   => cstep_k NtSet.empty []
          end
        else
          let sps' := map (fun rhs => Sp pred (Fr [] tt rhs, fr :: frs))
                          (rhss_for x rm)
          in  cstep_k (NtSet.add x vi) sps' 
      end
    end.
  
  (** A closure step does not change the prediction label of any spawned subparser. *)
  Lemma cstep_preserves_prediction :
    forall g hw rm sp sp' sps' vi vi',
      cstep g hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g hw rm sp sp' sps' vi vi' hs hi.
    unfold cstep in hs; dms; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst; auto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; auto.
  Qed.

  (** A closure step preserves the keyset invariant for each newly produced subparser. *)
  Lemma cstep_preserves_pki :
    forall g hw rm sp sp' sps' vi vi',
      sp_pushes_from_keyset rm sp
      -> cstep g hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> sp_pushes_from_keyset rm sp'.
  Proof.
    intros g hw rm sp sp' sps' vi vi' hk hs hi; red in hk.
    unfold cstep in hs; dms; tc; inv hs; red; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      red; red in hk; sis.
      eapply return_preserves_keyset_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      red; red in hk; sis.
      eapply push_preserves_keyset_invar; eauto.
      eapply rhss_for_key_set; eauto.
  Qed.

  (** Result type for the epsilon-closure of a subparser: error or a list of stable subparsers. *)
  Definition closure_result (A : Type) := sum prediction_error (list A).

  (* consider refactoring to short-circuit in case of error *)
  (** Aggregates a list of closure results by concatenating success lists or propagating the first error. *)
  Fixpoint aggr_closure_results {A B} (crs : list (sum A (list B))) : sum A (list B) :=
    match crs with
    | [] => inr []
    | cr :: crs' =>
      match (cr, aggr_closure_results crs') with
      | (inl e, _)          => inl e
      | (inr _, inl e)      => inl e
      | (inr sps, inr sps') => inr (sps ++ sps')
      end
    end.

  (** Every subparser in the aggregated closure result came from some [inr] entry in the input list. *)
  Lemma aggr_closure_results_succ_in_input:
    forall (A : Type)
           (crs : list (closure_result A))
           (sp  : A)
           (sps : list A),
      aggr_closure_results crs = inr sps 
      -> In sp sps 
      -> exists sps',
          In (inr sps') crs
          /\ In sp sps'.
  Proof.
    intros A crs; induction crs as [| cr crs IH]; intros sp sps ha hi; simpl in ha.
    - inv ha; inv hi.
    - destruct cr as [e | sps'];
        destruct (aggr_closure_results crs) as [e' | sps'']; tc; inv ha.
      apply in_app_or in hi.
      destruct hi as [hi' | hi''].
      + eexists; split; eauto.
        apply in_eq.
      + apply IH in hi''; auto.
        destruct hi'' as [sps [hi hi']].
        eexists; split; eauto.
        apply in_cons; auto.
  Qed.

  (** If aggregation returns an error, that error appears as [inl] in the input list. *)
  Lemma aggr_closure_results_error_in_input:
    forall (A : Type)
           (crs : list (closure_result A))
           (e   : prediction_error),
      aggr_closure_results crs = inl e
      -> In (inl e) crs.
  Proof.
    intros A crs e ha; induction crs as [| cr crs IH]; sis; tc.
    destruct cr as [e' | sps].
    - inv ha; auto.
    - destruct (aggr_closure_results crs) as [e' | sps']; tc; auto.
  Qed.

  (** Forward: if [sp] is in [sps] and [f sp] succeeds, its results land in the aggregated output. *)
  Lemma aggr_closure_results_map_succ_elt_succ :
    forall A (sp : A) (f : A -> closure_result A) (sps : list A) sps'',
      In sp sps
      -> aggr_closure_results (map f sps) = inr sps''
      -> exists sps',
          f sp = inr sps'
          /\ forall sp', In sp' sps' -> In sp' sps''.
  Proof.
    intros A sp f sps; induction sps as [| hd tl IH]; intros sps'' hi ha.
    - inv hi.
    - destruct hi as [hh | ht]; subst; sis.
      + dms; tc; inv ha; eexists; split; eauto.
        intros; apply in_or_app; auto.
      + destruct (f hd)                 as [? | sps ]; tc.
        destruct (aggr_closure_results _) as [? | sps']; tc; inv ha.
        apply IH with (sps'' := sps') in ht; auto.
        destruct ht as [sp' [heq hall]]; eexists; split; eauto.
        intros; apply in_or_app; auto.
  Qed.

  (** Backward: each result subparser traces back to some input via [f]. *)
  Lemma aggr_closure_results_map_backwards :
    forall A sp'' (f : A -> closure_result A) (sps sps'' : list A),
      aggr_closure_results (map f sps) = inr sps''
      -> In sp'' sps''
      -> exists sp sps',
          In sp sps
          /\ f sp = inr sps'
          /\ In sp'' sps'.
  Proof.
    intros A sp'' f sps; induction sps as [| sp sps IH]; intros sps'' ha hi.
    - sis; inv ha; inv hi.
    - simpl in ha.
      destruct (f sp) as [? | hd_sps] eqn:hf; tc.
      destruct (aggr_closure_results _) as [? | tl_sps] eqn:ha'; tc.
      inv ha.
      apply in_app_or in hi; destruct hi as [hhd | htl].
      + exists sp; exists hd_sps; repeat split; auto.
        apply in_eq.
      + apply IH in htl; auto.
        destruct htl as [sp' [sps' [? [? ?]]]]; subst.
        exists sp'; exists sps'; repeat split; auto.
        apply in_cons; auto.
  Qed.

  (** Dependent-map variant: if [sp] is in [sps] and [f sp hi] succeeds, its output lands in the aggregate. *)
  Lemma aggr_closure_results_dmap_succ_elt_succ :
    forall A sp (sps : list A) (f : forall sp, In sp sps -> closure_result A) sps'',
      In sp sps
      -> aggr_closure_results (dmap sps f) = inr sps''
      -> exists hi sps',
          f sp hi = inr sps'
          /\ forall sp', In sp' sps' -> In sp' sps''.
  Proof.
    intros A sp sps; induction sps as [| hd tl IH]; intros f sps'' hi ha.
    - inv hi.
    - destruct hi as [hh | ht]; subst.
      + simpl in ha.
        dmeq hsp; tc.
        dmeq hag; tc.
        inv ha.
        repeat eexists; eauto.
        intros sp' hi; apply in_or_app; auto.
      + simpl in ha.
        dmeq hsp; tc.
        dmeq hag; tc.
        inv ha.
        unfold eq_rect_r in hag; simpl in hag.
        apply IH in hag; auto.
        destruct hag as [hi [sps' [heq hall]]].
        repeat eexists; eauto.
        intros sp' hi'.
        apply in_or_app; auto.
  Qed.

  (** Dependent-map backward: each result subparser traces back to some input element via [f]. *)
  Lemma aggr_closure_results_dmap_backwards :
    forall A (sp'' : A) (sps : list A) f (sps'' : list A),
      @aggr_closure_results prediction_error _ (dmap sps f) = inr sps''
      -> In sp'' sps''
      -> exists sp hi sps',
          In sp sps
          /\ f sp hi = inr sps'
          /\ In sp'' sps'.
  Proof.
    intros A sp'' sps f; induction sps as [| sp sps IH]; intros sps'' ha hi.
    - inv ha; inv hi.
    - simpl in ha.
      dmeq hf; tc.
      dmeq ha'; tc.
      inv ha.
      apply in_app_or in hi.
      destruct hi as [hh | ht].
      + repeat eexists; eauto.
        apply in_eq.
      + apply IH in ha'; auto.
        destruct ha' as [sp' [hi [sps' [hi' [heq hi'']]]]].
        unfold eq_rect_r in heq; simpl in heq.
        repeat eexists; eauto.
        apply in_cons; auto.
  Qed.

  (** Lexicographic termination measure for closure: (stack_score, stack_height) decreases at each step. *)
  Definition ll_meas (rm : rhs_map) (vi : NtSet.t) (sp : subparser) : nat * nat :=
    match sp with
    | Sp _ sk => meas rm vi (stack_suffixes sk)
    end.

  (** Each closure step strictly decreases [ll_meas], ensuring well-founded recursion. *)
  Lemma cstep_meas_lt :
    forall (g      : grammar)
           (hw     : grammar_wf g)
           (rm     : rhs_map)
           (sp sp' : subparser)
           (sps'   : list subparser)
           (vi vi' : NtSet.t),
      sp_pushes_from_keyset rm sp
      -> cstep g hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> lex_nat_pair (ll_meas rm vi' sp') (ll_meas rm vi sp).
  Proof.
    intros g hw rm sp sp' sps' vi vi' ha hs hi. 
    unfold cstep in hs; dmeqs h; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      eapply meas_lt_after_return; sis; eauto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst.
      eapply meas_lt_after_push; sis; eauto.
      + apply not_mem_iff; auto.
      + eapply rhss_for_key_set; eauto.
      + eapply rhss_for_all_rhss; eauto. 
  Defined.

  (** A closure step transfers the accessibility witness to each produced subparser, enabling recursion. *)
  Lemma acc_after_step :
    forall g hw rm sp sp' sps' vi vi',
      sp_pushes_from_keyset rm sp
      -> cstep g hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> Acc lex_nat_pair (ll_meas rm vi sp)
      -> Acc lex_nat_pair (ll_meas rm vi' sp').
  Proof.
    intros g hw rm sp sp' sps' vi vi' hk heq hi ha.
    eapply Acc_inv; eauto.
    eapply cstep_meas_lt; eauto.
  Defined.

  (** Core epsilon-closure fixpoint: iteratively expands a single subparser until it reaches a stable configuration. *)
  Fixpoint llc
           (g  : grammar)
           (hw : grammar_wf g)
           (rm : rhs_map)
           (vi : NtSet.t)
           (sp : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (ha : Acc lex_nat_pair (ll_meas rm vi sp)) : closure_result subparser :=
    match cstep g hw rm vi sp as r return cstep g hw rm vi sp = r -> _ with
    | cstep_done       => fun _  => inr [sp]
    | cstep_error e    => fun _  => inl e
    | cstep_k vi' sps' => 
      fun hs => 
        let crs := dmap sps' (fun sp' hi =>
                                llc g hw rm vi' sp'
                                    (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                    (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
        in  aggr_closure_results crs
    end eq_refl.

  (** Unfolding lemma for [llc], used to reason about the fixpoint without unrolling the recursion manually. *)
  Lemma llc_unfold :
    forall g hw rm vi sp hk ha,
      llc g hw rm vi sp hk ha =
      match cstep g hw rm vi sp as r return cstep g hw rm vi sp = r -> _ with
      | cstep_done       => fun _  => inr [sp]
      | cstep_error e    => fun _  => inl e
      | cstep_k vi' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hi =>
                           llc g hw rm vi' sp'
                               (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                               (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          in  aggr_closure_results crs
      end eq_refl.
  Proof.
    intros g hw rm vi sp hk ha; destruct ha; auto.
  Qed.

  (** Internal case analysis for [llc] results given a particular step result [sr]. *)
  Lemma llc_cases' :
    forall (g   : grammar)
           (hw  : grammar_wf g)
           (rm  : rhs_map)
           (vi  : NtSet.t)
           (sp  : subparser)
           (hk  : sp_pushes_from_keyset rm sp)
           (ha  : Acc lex_nat_pair (ll_meas rm vi sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result subparser)
           (heq : cstep g hw rm vi sp = sr),
      match sr as r return cstep g hw rm vi sp = r -> closure_result subparser with
      | cstep_done       => fun _  => inr [sp]
      | cstep_error e    => fun _  => inl e
      | cstep_k vi' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hi => llc g hw rm vi' sp'
                                            (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                            (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          in  aggr_closure_results crs
      end heq = cr
      -> match cr with
         | inl e => 
           sr = cstep_error e
           \/ exists (sps : list subparser)
                     (vi' : NtSet.t)
                     (hs  : cstep g hw rm vi sp = cstep_k vi' sps)
                     (crs : list (closure_result subparser)),
               crs = dmap sps (fun sp' hi => 
                                 llc g hw rm vi' sp'
                                     (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                     (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggr_closure_results crs = inl e
         | inr sps => 
           (sr = cstep_done /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (vi'  : NtSet.t)
                     (hs   : cstep g hw rm vi sp = cstep_k vi' sps')
                     (crs  : list (closure_result subparser)),
               crs = dmap sps' (fun sp' hi => 
                                  llc g hw rm vi' sp'
                                      (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                      (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggr_closure_results crs = inr sps
         end.
  Proof.
    intros g hw rm vi sp hk ha sr cr heq.
    destruct sr as [| sps | e];
    destruct cr as [e' | sps']; intros heq'; tc;
    try solve [inv heq'; eauto | eauto 8].
  Qed.

  (** Case analysis for [llc] results: the result is either done, an error, or a recursive aggregate. *)
  Lemma llc_cases :
    forall (g  : grammar)
           (hw : grammar_wf g)
           (rm : rhs_map)
           (vi : NtSet.t)
           (sp : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (ha : Acc lex_nat_pair (ll_meas rm vi sp))
           (cr : closure_result subparser),
      llc g hw rm vi sp hk ha = cr
      -> match cr with
         | inl e => 
           cstep g hw rm vi sp = cstep_error e
           \/ exists (sps : list subparser)
                     (vi' : NtSet.t)
                     (hs  : cstep g hw rm vi sp = cstep_k vi' sps)
                     (crs : list (closure_result subparser)),
               crs = dmap sps (fun sp' hi => 
                                 llc g hw rm vi' sp'
                                     (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                     (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggr_closure_results crs = inl e
         | inr sps =>
           (cstep g hw rm vi sp = cstep_done /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (vi'  : NtSet.t)
                     (hs   : cstep g hw rm vi sp = cstep_k vi' sps')
                     (crs  : list (closure_result subparser)),
               crs = dmap sps' (fun sp' hi => 
                                  llc g hw rm vi' sp'
                                      (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                      (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggr_closure_results crs = inr sps
         end.
  Proof.
    intros g hw rm vi sp hk ha cr hs; subst.
    rewrite llc_unfold.
    eapply llc_cases'; eauto.
  Qed.

  (** Specialization of [llc_cases] to the success case: either done immediately or recursively aggregated. *)
  Lemma llc_success_cases :
    forall g hw rm vi sp hk ha sps,
      llc g hw rm vi sp hk ha = inr sps
      -> (cstep g hw rm vi sp = cstep_done /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (vi'  : NtSet.t)
                   (hs   : cstep g hw rm vi sp = cstep_k vi' sps')
                   (crs  : list (closure_result subparser)),
          crs = dmap sps' (fun sp' hi => 
                             llc g hw rm vi' sp'
                                 (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                 (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          /\ aggr_closure_results crs = inr sps.
  Proof.
    intros g hw rm vi sp hk ha sps hs; apply llc_cases with (cr := inr sps); auto.
  Qed.

  (** Specialization of [llc_cases] to the error case: either a direct step error or a recursive error. *)
  Lemma llc_error_cases :
    forall g hw rm vi sp hk ha e,
      llc g hw rm vi sp hk ha = inl e
      -> cstep g hw rm vi sp = cstep_error e
         \/ exists (sps : list subparser)
                   (vi' : NtSet.t)
                   (hs  : cstep g hw rm vi sp = cstep_k vi' sps)
                   (crs : list (closure_result subparser)),
          crs = dmap sps (fun sp' hi => 
                            llc g hw rm vi' sp'
                                (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          /\ aggr_closure_results crs = inl e.
  Proof.
    intros g hw rm vi sp hk ha e hs; apply llc_cases with (cr := inl e); auto.
  Qed.

  (** Inductive auxiliary: [llc] preserves the prediction label, proved by well-founded induction on the measure. *)
  Lemma llc_preserves_prediction' :
    forall g hw rm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sp' sps',
      pair = ll_meas rm vi sp
      -> llc g hw rm vi sp hk ha' = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros g hw rm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sp' sps' heq hs hi; subst.
    pose proof hs as hs'; apply llc_success_cases in hs.
    destruct hs as [[hs heq] | [sps'' [av' [hs [crs [heq heq']]]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggr_closure_results_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      + apply cstep_preserves_prediction with (sp' := sp'') in hs; auto.
        rewrite hs; auto.
      + eapply cstep_meas_lt; eauto.
  Qed.

  (** [llc] does not alter the prediction label of any subparser it produces. *)
  Lemma llc_preserves_prediction :
    forall g hw rm vi sp sp' sps' hk ha,
      llc g hw rm vi sp hk ha = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros; eapply llc_preserves_prediction'; eauto.
  Qed.

  (** Inductive auxiliary: [llc] preserves the keyset invariant, proved by well-founded induction. *)
  Lemma llc_preserves_pki' :
    forall g hw rm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sps',
      pair = ll_meas rm vi sp
      -> llc g hw rm vi sp hk ha' = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros g hw rm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sps'' heq hc; subst.
    pose proof hc as hc'; apply llc_success_cases in hc.
    destruct hc as [[hc heq] | [sps' [vi' [hc [crs [heq heq']]]]]]; subst; intros sp''' hi.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggr_closure_results_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      eapply cstep_meas_lt; eauto.
  Qed.

  (** [llc] preserves the keyset invariant for all subparsers it produces. *)
  Lemma llc_preserves_pki :
    forall g hw rm vi sp hk ha sps sps',
      all_sp_pushes_from_keyset rm sps
      -> llc g hw rm vi sp hk ha = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros; eapply llc_preserves_pki'; eauto.
  Qed.
  
  (** Computes the epsilon-closure of a list of subparsers by running [llc] on each from an empty visited set. *)
  Definition ll_closure
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (sps : list subparser)
             (hk  : all_sp_pushes_from_keyset rm sps) :
    sum prediction_error (list subparser) :=
    aggr_closure_results (dmap sps (fun sp hi =>
                                    llc g hw rm NtSet.empty sp
                                        (pki_list__pki_mem _ _ sp hk hi)
                                        (lex_nat_pair_wf _))).

  (** [ll_closure] preserves the prediction label: each output subparser traces back to a same-prediction input. *)
  Lemma ll_closure_preserves_prediction :
    forall g hw rm sps (hk : all_sp_pushes_from_keyset rm sps) sps' sp',
      ll_closure g hw rm sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
  Proof.
    intros g hw rm sps hk sps' sp' hl hi.
    eapply aggr_closure_results_succ_in_input in hl; eauto.
    destruct hl as [sps'' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eexists; split; eauto.
    eapply llc_preserves_prediction; eauto.
  Qed.

  (** [ll_closure] preserves the keyset invariant for all subparsers it produces. *)
  Lemma ll_closure_preserves_pki :
    forall g hw rm sps sps' (hk : all_sp_pushes_from_keyset rm sps),
      ll_closure g hw rm sps hk = inr sps'
      -> all_sp_pushes_from_keyset rm sps'. 
  Proof.
    intros g hw rm sps spss' hk hc sp' hi.
    eapply aggr_closure_results_succ_in_input in hc; eauto.
    destruct hc as [sps' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eapply llc_preserves_pki; eauto.
  Qed.
    
  (** Computes the target subparser set after consuming token [a]: move then close. *)
  Definition ll_target g hw rm a sps
                      (hk : all_sp_pushes_from_keyset rm sps) :
                      sum prediction_error (list subparser) :=
    match move a sps as m return move a sps = m -> _ with
    | inl e    => fun _ => inl e
    | inr sps' =>
      fun hm =>
        match ll_closure g hw rm sps' (move_preserves_pki _ _ _ _ hk hm) with
        | inl e     => inl e
        | inr sps'' => inr sps''
        end
    end eq_refl.

  (** Internal case-split for [ll_target] given a particular move result [mr]. *)
  Lemma ll_target_cases' :
    forall g hw rm a sps mr hk (heq : move a sps = mr) cr,
      match mr as mr' return move a sps = mr' -> move_result subparser with
      | inl e    => fun _ => inl e
      | inr sps' =>
        fun hm =>
          match ll_closure g hw rm sps' (move_preserves_pki _ _ _ _ hk hm) with
          | inl e     => inl e
          | inr sps'' => inr sps''
          end
      end heq = cr
      -> match cr with
         | inl e =>
           move a sps = inl e
           \/ (exists sps' hk',
                  move a sps = inr sps' /\ ll_closure g hw rm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', move a sps = inr sps' /\ ll_closure g hw rm sps' hk' = inr sps''
         end.
  Proof.
    intros g hw rm a sps mr hk heq cr.
    destruct mr as [e' | sps']; destruct cr as [e'' | sps'']; intros heq'; tc.
    - inv heq'; auto.
    - destruct (ll_closure _ _ _) eqn:hc; inv heq'; eauto.
    - destruct (ll_closure _ _ _) eqn:hc; inv heq'; eauto.
  Qed.

  (** Case analysis for [ll_target]: the result comes from either a move error or a move-then-close chain. *)
  Lemma ll_target_cases :
    forall g hw rm a sps hk cr,
      ll_target g hw rm a sps hk = cr
      -> match cr with
         | inl e =>
           move a sps = inl e
           \/ (exists sps' hk',
                  move a sps = inr sps' /\ ll_closure g hw rm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', move a sps = inr sps' /\ ll_closure g hw rm sps' hk' = inr sps''
         end.
  Proof.
    intros; eapply ll_target_cases'; eauto.
  Qed.

  (** [ll_target] always returns either an error or a subparser list; useful for exhaustive case analysis. *)
  Lemma ll_target_destruct :
    forall g hw rm a sps hk,
      (exists e, ll_target g hw rm a sps hk = inl e)
      \/ (exists sps', ll_target g hw rm a sps hk = inr sps').
  Proof.
    intros g hw rm a sps hk.
    remember (ll_target g hw rm a sps hk) as tr eqn:heq.
    destruct tr; eauto.
  Qed.    
  
  (** Success case of [ll_target]: decomposes a successful result into a move followed by a closure. *)
  Lemma ll_target_succ_case :
    forall g hw rm a sps hk sps'',
      ll_target g hw rm a sps hk = inr sps''
      -> (exists sps' hk',
             move a sps = inr sps'
             /\ ll_closure g hw rm sps' hk' = inr sps'').
  Proof.
    intros g hw rm a sps hk sps'' ht; apply ll_target_cases in ht; auto.
  Qed.

  (** [ll_target] preserves the keyset invariant for the produced subparser list. *)
  Lemma ll_target_preserves_pki :
    forall g hw rm a sps sps' hk,
      ll_target g hw rm a sps hk = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros g hw rm a sps sps'' hk ht.
    apply ll_target_succ_case in ht.
    destruct ht as [sps' [hk' [hmhc]]].
    eapply ll_closure_preserves_pki; eauto.
  Qed.

  (* LL prediction *)

  (** Outcome of LL prediction: success (unique RHS), ambiguity, rejection, or error. *)
  Inductive prediction_result :=
  | pred_succ   : list symbol      -> prediction_result
  | pred_ambig  : list symbol      -> prediction_result
  | pred_reject :                     prediction_result
  | pred_error  : prediction_error -> prediction_result.

  (** Returns [true] iff the subparser's stack is fully consumed: empty suffix and no caller frames. *)
  Definition final_config (sp : subparser) : bool :=
    match sp with
    | Sp _ (Fr _ _ [], []) => true
    | _ => false
    end.

  (** A subparser in final configuration has an empty suffix and no caller frames. *)
  Lemma final_config_empty_stack :
    forall sp pred stk,
      sp = Sp pred stk
      -> final_config sp = true
      -> exists pre v, stk = (Fr pre v [], []).
  Proof.
    intros sp pred stk ? hf; subst; unfold final_config in hf; dms; tc; eauto.
  Qed.

  (** Boolean check: all elements of [xs] agree with [x] on [f], using [beq] for equality. *)
  Definition all_predictions_equal_b {A B} (beq : B -> B -> bool) (f : A -> B) (x : A) (xs : list A) : bool :=
    all_equal _ beq (f x) (map f xs). 

  (** If [all_predictions_equal] holds for [sp :: sps], then it holds for the head and tail separately. *)
  Lemma all_predictions_equal_b_inv_cons :
    forall A B beq (f : A -> B) sp' sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> all_predictions_equal_b beq f sp' (sp :: sps) = true
      -> f sp' = f sp
         /\ all_predictions_equal_b beq f sp' sps = true.
  Proof.
    unfold all_predictions_equal_b; intros.
    apply all_equal_inv_cons; auto.
  Qed.

  (** Any element in [sps] agrees on [f] with [sp] when [all_predictions_equal] holds. *)
  Lemma all_predictions_equal_b_in_tl :
    forall A B beq (f : A -> B) sp sp' sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> all_predictions_equal_b beq f sp sps = true
      -> In sp' sps
      -> f sp' = f sp. 
  Proof.
    unfold all_predictions_equal_b; intros.
    eapply all_equal_in_tl; eauto.
    apply in_map_iff; eauto.
  Qed.

  (** When [all_predictions_equal] is false, there exists a witness in [sps] that disagrees with [sp] on [f]. *)
  Lemma all_predictions_equal_b_false_exists_diff_rhs :
    forall A B beq (f : A -> B) sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> all_predictions_equal_b beq f sp sps = false
      -> exists sp',
        In sp' sps
        /\ f sp' <> f sp. 
  Proof.
    unfold all_predictions_equal_b; intros A B beq f sp sps hd ha. 
    apply all_equal_false_exists_diff_rhs in ha; auto.
    destruct ha as [ys [hi hn]].
    apply in_map_iff in hi.
    destruct hi as [sp' [heq hi]]; subst; eauto.
  Qed.

  (* propositional spec for all_predictions_equal *)
  (** Propositional version of [all_predictions_equal]: every element of [sps] maps to the same value as [sp] under [f]. *)
  Definition all_predictions_equal {A B : Type} (f : A -> B) sp sps :=
    forall sp', In sp' sps -> f sp' = f sp.

  (** [all_predictions_equal] is monotone: it holds for the tail if it holds for the cons. *)
  Lemma ape_tail :
    forall A B (f : A -> B) sp sp' sps,
      all_predictions_equal f sp (sp' :: sps)
      -> all_predictions_equal f sp sps.
  Proof.
    firstorder.
  Qed.

  (** Extending [all_predictions_equal] to include [sp] itself is trivially valid. *)
  Lemma ape_cons_head_eq :
    forall A B (f : A -> B) sp sps,
      all_predictions_equal f sp sps
      -> all_predictions_equal f sp (sp :: sps).
  Proof.
    intros A B f sp sps ha sp' hi; firstorder; subst; auto.
  Qed.
  
  (** The boolean [all_predictions_equal] implies the propositional [all_predictions_equal]. *)
  Lemma all_predictions_equal_prop :
    forall A B beq (f : A -> B) sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> all_predictions_equal_b beq f sp sps = true
      -> all_predictions_equal f sp sps.
  Proof.
    intros A B beq f sp sps hd ha sp' hi. 
    unfold all_predictions_equal_b, all_equal in ha.
    eapply forallb_forall with (x := f sp') in ha; eauto.
    - firstorder. 
    - apply in_map_iff; eauto.
  Qed.

  (** Negation of [all_predictions_equal] implies [all_predictions_equal] returns [false]. *)
  Lemma ape_false__all_predictions_equal_false :
    forall A B beq (f : A -> B) sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> ~ all_predictions_equal f sp sps
      -> all_predictions_equal_b beq f sp sps = false.
  Proof.
    intros A B beq f sp sps hd hn; unfold not in hn.
    destruct (all_predictions_equal_b _ _ sp sps) eqn:ha; auto.
    exfalso; apply hn; eapply all_predictions_equal_prop; auto.
  Qed.

  (** [all_predictions_equal] is preserved when restricting to a filtered sublist. *)
  Lemma all_predictions_equal_filter :
    forall A B sp sps sps' f (f' : A -> B),
      all_predictions_equal f' sp sps
      -> filter f sps = sps'
      -> all_predictions_equal f' sp sps'.
  Proof.
    intros A B sp sps sps' f f' ha hf sp' hi; subst.
    apply filter_In in hi; firstorder.
  Qed.

  (** [ll_target] preserves prediction uniformity: if all subparsers agree, so do their targets. *)
  Lemma ll_target_preserves_ape:
    forall g hw rm a x sps sps' (hk : all_sp_pushes_from_keyset rm sps),
    all_predictions_equal prediction x sps
    -> ll_target g hw rm a sps hk = inr sps'
    -> all_predictions_equal prediction x sps'.
  Proof.
    intros g hw rm a x sps sps'' hk ha hl sp'' hi''.
    red in ha.
    (* lemma about ll_target preserving prediction *)
    apply ll_target_succ_case in hl.
    destruct hl as [sps' [hk' [hm hc]]].
    eapply ll_closure_preserves_prediction in hc; eauto.
    destruct hc as [sp' [hi' heq']]; rewrite heq'.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [sp [hi heq]]; rewrite heq; firstorder.
  Qed.
      
  (** Inspects end-of-input subparsers: returns success if all final ones agree on a prediction, ambiguity otherwise. *)
  Definition handle_final_subparsers (sps : list subparser) : prediction_result :=
    match filter final_config sps with
    | []         => pred_reject
    | sp :: sps' => 
      if all_predictions_equal_b beq_gamma prediction sp sps' then
        pred_succ sp.(prediction)
      else
        pred_ambig sp.(prediction)
    end.

  (** Success from [handle_final_subparsers] implies some subparser in [sps] is in final configuration with that RHS. *)
  Lemma handle_final_subparsers_succ_facts :
    forall sps rhs,
      handle_final_subparsers sps = pred_succ rhs
      -> exists sp pre v,
        In sp sps
        /\ sp.(prediction) = rhs
        /\ sp.(stack) = (Fr pre v [], []).
  Proof.
    intros sps rhs hh.
    unfold handle_final_subparsers in hh.
    destruct (filter _ _) as [| sp sps'] eqn:hf; tc.
    destruct (all_predictions_equal_b _ _); tc; inv hh.
    assert (hin : In sp (filter final_config sps)).
    { rewrite hf; apply in_eq. }
    apply filter_In in hin.
    destruct hin as [hin ht]; subst.
    unfold final_config in ht.
    destruct sp as [pred ([o suf], frs)]; dms; tc.
    repeat eexists; eauto.
  Qed.

  (** Ambiguity from [handle_final_subparsers] implies some subparser in [sps] carries the ambiguous prediction. *)
  Lemma handle_final_subparsers_ambig_from_subparsers :
    forall sps gamma,
      handle_final_subparsers sps = pred_ambig gamma
      -> exists sp, In sp sps /\ sp.(prediction) = gamma.
  Proof.
    intros sps gamma hh.
    unfold handle_final_subparsers in hh.
    dmeqs h; tc; inv hh.
    eexists; split; eauto.
    eapply filter_cons_in; eauto.
  Qed.

  (** Main prediction loop: consumes tokens one by one, pruning subparsers, until input is exhausted or a winner is clear. *)
  Fixpoint ll_predict'
           (g   : grammar)
           (hw  : grammar_wf g)
           (rm  : rhs_map)
           (sps : list subparser)
           (ts  : list token)
           (hk  : all_sp_pushes_from_keyset rm sps) : prediction_result :=
    match ts with
    | []            => handle_final_subparsers sps
    | t :: ts' =>
      match sps with
      | []          => pred_reject
      | sp' :: sps' =>
        if all_predictions_equal_b beq_gamma prediction sp' sps' then
          pred_succ sp'.(prediction)
        else
          match ll_target g hw rm t sps hk as t' return ll_target g hw rm t sps hk = t' -> _ with
          | inl e     => fun _ => pred_error e
          | inr sps'' =>
            fun ht =>
              ll_predict' g hw rm sps'' ts' (ll_target_preserves_pki _ _ _ _ _ _ hk ht)
          end eq_refl
      end
    end.

  (** Case analysis for the continuation branch of [ll_predict']: decomposes the result by the target computation. *)
  Lemma ll_predict'_cont_cases :
    forall g hw rm a sps hk ts' pr t (heq : ll_target g hw rm a sps hk = t),
      match t as t' return ll_target g hw rm a sps hk = t' -> _ with
      | inl e     => fun _ => pred_error e
      | inr sps'' =>
        fun ht =>
          ll_predict' g hw rm sps'' ts' (ll_target_preserves_pki _ _ _ _ _ _ hk ht)
      end heq = pr
      -> match pr with
         | pred_succ ys =>
           (exists sps'' (heq' : ll_target g hw rm a sps hk = inr sps''),
               ll_predict' g hw rm sps'' ts' (ll_target_preserves_pki _ _ _ _ _ _ hk heq') = pred_succ ys)
         | pred_ambig ys =>
           (exists sps'' (heq' : ll_target g hw rm a sps hk = inr sps''),
               ll_predict' g hw rm sps'' ts' (ll_target_preserves_pki _ _ _ _ _ _ hk heq') = pred_ambig ys)
         | pred_reject =>
           (exists sps'' (heq' : ll_target g hw rm a sps hk = inr sps''),
               ll_predict' g hw rm sps'' ts' (ll_target_preserves_pki _ _ _ _ _ _ hk heq') = pred_reject)         
         | pred_error e =>
           ll_target g hw rm a sps hk = inl e
           \/ (exists sps'' (heq' : ll_target g hw rm a sps hk = inr sps''),
               ll_predict' g hw rm sps'' ts' (ll_target_preserves_pki _ _ _ _ _ _ hk heq') = pred_error e)
         end.
  Proof.
    intros g hw rm a sps hk ts' pr t heq; dms; intros heq'; inv heq'; eauto.
  Qed.

  (** A successful prediction by [ll_predict'] corresponds to a subparser in the initial list. *)
  Lemma ll_predict'_success_result_in_original_subparsers :
    forall g hw rm ts gamma sps hk ,
      ll_predict' g hw rm sps ts hk = pred_succ gamma
      -> exists sp, In sp sps /\ (prediction sp) = gamma.
  Proof.
    intros g hw rm ts gamma.
    induction ts as [| (a, l) ts IH]; intros sps hk hl; sis.
    - apply handle_final_subparsers_succ_facts in hl.
      destruct hl as [sp [pre [v [hi [heq heq']]]]]; eauto.
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall; subst.
      + inv hl; exists sp'; split; auto.
        apply in_eq.
      + apply ll_predict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]].
        pose proof ht as ht'.
        apply ll_target_succ_case in ht'.
        destruct ht' as [sps''' [hk' [hm hc]]].
        apply IH in hl; destruct hl as [? [hi heq]]; subst.
        eapply ll_closure_preserves_prediction in hc; eauto.
        destruct hc as [? [? heq]]; rewrite heq.
        eapply move_preserves_prediction in hm; eauto.
        destruct hm as [? [? ?]]; eauto.
  Qed.

  (** An ambiguous prediction by [ll_predict'] corresponds to a subparser in the initial list. *)
  Lemma ll_predict'_ambig_result_in_original_subparsers :
    forall g hw rm ts gamma sps hk,
      ll_predict' g hw rm sps ts hk  = pred_ambig gamma
      -> exists sp, In sp sps /\ (prediction sp) = gamma.
  Proof.
    intros g hw rm ts gamma.
    induction ts as [| (a, l) ts IH]; intros sps hk hl; sis.
    - apply handle_final_subparsers_ambig_from_subparsers in hl; auto. 
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall; subst.
      + inv hl.
      + apply ll_predict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]].
        pose proof ht as ht'.
        apply ll_target_succ_case in ht'.
        destruct ht' as [sps''' [hk' [hm hc]]].
        apply IH in hl; destruct hl as [? [hi heq]]; subst.
        eapply ll_closure_preserves_prediction in hc; eauto.
        destruct hc as [? [? heq]]; rewrite heq.
        eapply move_preserves_prediction in hm; eauto.
        destruct hm as [? [? ?]]; eauto.
  Qed.

  (* to do : this lemma is an example of why some invariants
     aren't required when it's assumed that ll_predict' succeeds.
    There might be other places where I can remove these 
    hypotheses. *)
  (** When all subparsers agree on a prediction and [ll_predict'] succeeds, the result equals that common prediction. *)
  Lemma ll_predict'_succ__eq_all_predictions_equal :
    forall g hw rm sp ys ts sps hk,
(*      no_left_recursion g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps *)
      all_predictions_equal prediction sp sps
      -> ll_predict' g hw rm sps ts hk = pred_succ ys
      -> ys = prediction sp.
  Proof.
    intros g hw rm sp ys ts; induction ts as [| (a, l) ts IH];
      intros sps hk ha hl; sis.
    - unfold handle_final_subparsers in hl.
      destruct (filter _ _) as [| sp' sps'] eqn:hf; tc.
      dm; tc; inv hl.
      eapply all_predictions_equal_filter in hf; eauto.
      red in hf; firstorder.
    - destruct sps as [| sp' sps']; tc.
      destruct (all_predictions_equal_b _ _ sp' sps').
      + inv hl; apply ha; apply in_eq.
      + apply ll_predict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]].
        apply IH in hl; auto.
        eapply ll_target_preserves_ape; eauto.
  Qed.

  (** Unanimous subparsers preclude ambiguity: [ll_predict'] cannot return [pred_ambig] when all predictions agree. *)
  Lemma all_predictions_equal__ll_predict'_neq_ambig :
    forall g hw rm sp ys ts sps hk,
      all_predictions_equal prediction sp sps
      -> ll_predict' g hw rm sps ts hk <> pred_ambig ys.
  Proof.
    intros g hw rm sp ys ts; induction ts as [| (a, l) ts IH]; intros sps hk ha hl; sis.
    - (* lemma *)
      unfold handle_final_subparsers in hl.
      destruct (filter _ _) as [| sp' sps'] eqn:hf; tc.
      destruct (all_predictions_equal_b _ _) eqn:ha'; tc; inv hl.
      apply all_predictions_equal_b_false_exists_diff_rhs in ha'.
      destruct ha' as [sp'' [hi hneq]].
      apply hneq. apply eq_trans with (y := prediction sp).
      + apply ha.
        eapply filter_In; rewrite hf; apply in_cons; auto.
      + symmetry; apply ha.
        eapply filter_In; rewrite hf; apply in_eq.
      + apply beq_gamma_eq_iff.
    - destruct sps as [| sp' sps']; tc.
      destruct (all_predictions_equal_b _ _); tc.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      apply IH in hl; auto.
      eapply ll_target_preserves_ape; eauto.
  Qed. 

  (** Creates the initial subparser set for prediction on nonterminal [x]: one subparser per alternative in the grammar. *)
  Definition ll_init_sps
             (rm  : rhs_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame) : list subparser :=
    let cr := Fr pre vs (NT x :: suf)
    in  map (fun rhs => Sp rhs (Fr [] tt rhs, cr :: frs))
            (rhss_for x rm).

  (** The prediction of every initial subparser is a right-hand side of [x] in the rhs_map. *)
  Lemma ll_init_sps_prediction_in_rhss_for :
    forall rm pre vs x suf frs sp,
      In sp (ll_init_sps rm pre vs x suf frs)
      -> In sp.(prediction) (rhss_for x rm).
  Proof.
    intros rm pre vs x suf frs sp hi; unfold ll_init_sps in hi.
    eapply in_map_iff in hi; firstorder; subst; auto.
  Qed.

  (** Every grammar production for [x] yields a corresponding subparser in [ll_init_sps]. *)
  Lemma ll_init_sps_result_incl_all_rhss :
    forall g rm pre vs x suf rhs frs,
      rhs_map_correct rm g
      -> PM.In (x, rhs) g
      -> In (Sp rhs (Fr [] tt rhs, Fr pre vs (NT x :: suf) :: frs)) 
            (ll_init_sps rm pre vs x suf frs).
  Proof.
    intros g rm pre vs x suf rhs frs hc hi.
    apply in_map_iff; exists rhs; split; auto.
    eapply rhss_for_in_iff; eauto.
  Qed.

  (** [ll_init_sps] preserves the keyset invariant when the caller's stack already satisfies it. *)
  Lemma ll_init_sps_preserves_pki :
    forall rm pre vs x suf frs,
      stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)
      -> all_sp_pushes_from_keyset rm (ll_init_sps rm pre vs x suf frs).
  Proof.
    intros rm pre vs x suf frs hk sp hi.
    unfold ll_init_sps in hi.
    apply in_map_iff in hi. 
    destruct hi as [ys [heq hi]]; subst.
    red in hk; sis.
    eapply push_preserves_keyset_invar; eauto.
    eapply rhss_for_key_set; eauto.
  Qed.
    
  (** Computes the initial closed subparser set for [x]: initialize with all alternatives, then close. *)
  Definition ll_start_state
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame)
             (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)) :
    sum prediction_error (list subparser) :=
    ll_closure g hw rm (ll_init_sps rm pre vs x suf frs) (ll_init_sps_preserves_pki _ _ _ _ _ _ hk).
  
  (** Every subparser produced by [ll_start_state] has its prediction in the rhs_map for [x]. *)
  Lemma ll_start_state_sp_prediction_in_rhss_for :
    forall g hw rm pre vs x suf frs hk sp' sps',
      ll_start_state g hw rm pre vs x suf frs hk = inr sps'
      -> In sp' sps'
      -> In sp'.(prediction) (rhss_for x rm).
  Proof.
    intros g hw rm pre vs x suf frs hk sp' sps' hf hi. 
    unfold ll_start_state in hf.
    eapply ll_closure_preserves_prediction in hf; eauto.
    destruct hf as [sp [hin heq]]; rewrite heq.
    eapply ll_init_sps_prediction_in_rhss_for; eauto.
  Qed.

  (** [ll_start_state] preserves the keyset invariant for all subparsers it produces. *)
  Lemma ll_start_state_preserves_pki :
    forall g hw rm pre vs x suf frs hk sps',
      ll_start_state g hw rm  pre vs x suf frs hk = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros g hw rm pre vs x suf frs hk sps' hl. 
    eapply ll_closure_preserves_pki; eauto.
  Qed.
  
  (** Top-level LL prediction entry point: computes the start state for [x], then runs the prediction loop. *)
  Definition ll_predict
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame)
             (ts  : list token)
             (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)) : prediction_result :=
    match ll_start_state g hw rm pre vs x suf frs hk as s return ll_start_state g hw rm pre vs x suf frs hk = s -> _ with
    | inl msg => fun _   => pred_error msg
    | inr sps => fun heq => ll_predict' g hw rm sps ts
                                       (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq)
    end eq_refl.

  (** Internal case analysis for [ll_predict] given a particular start-state result [cr]. *)
  Lemma ll_predict_cases' :
    forall g hw rm pre vs x suf frs ts hk cr (heq : ll_start_state g hw rm pre vs x suf frs hk = cr) pr,
      match cr as s return ll_start_state g hw rm pre vs x suf frs hk = s -> _ with
      | inl msg => fun _   => pred_error msg
      | inr sps => fun heq => ll_predict' g hw rm sps ts
                                         (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq)
      end heq = pr
      -> match pr with
         | pred_succ ys =>
           (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
               ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_succ ys)
         | pred_ambig ys =>
           (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
               ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_ambig ys)
         | pred_reject =>
           (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk= inr sps),
               ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_reject)
         | pred_error e =>
           ll_start_state g hw rm pre vs x suf frs hk = inl e
           \/ (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
                  ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_error e)
         end.
  Proof.
    intros g hw rm pre vs x suf frs ts hk cr heq pr. 
    dms; intros heq'; inv heq'; eauto.
  Qed.

  (** Case analysis for [ll_predict]: decomposes any result into start-state error or prediction-loop outcome. *)
  Lemma ll_predict_cases :
    forall g hw rm pre vs x suf frs ts hk pr,
      ll_predict g hw rm pre vs x suf frs ts hk = pr
      -> match pr with
         | pred_succ ys =>
           (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
               ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_succ ys)
         | pred_ambig ys =>
           (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
               ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_ambig ys)
         | pred_reject =>
           (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
               ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_reject)
         | pred_error e =>
           ll_start_state g hw rm pre vs x suf frs hk = inl e
           \/ (exists sps (heq : ll_start_state g hw rm pre vs x suf frs hk = inr sps),
                  ll_predict' g hw rm sps ts (ll_start_state_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = pred_error e)
         end.
  Proof.
    intros; eapply ll_predict_cases'; eauto.
  Qed.

  (** A successful [ll_predict] prediction is always a right-hand side of [x] in the rhs_map. *)
  Lemma ll_predict_succ_in_rhss_for :
    forall g hw rm pre vs x suf frs ts hk gamma,
      ll_predict g hw rm pre vs x suf frs ts hk = pred_succ gamma
      -> In gamma (rhss_for x rm).
  Proof.
    intros g hw rm pre vs x suf frs ts hk gamma hp.
    apply ll_predict_cases in hp.
    destruct hp as [sps [heq hp]].
    apply ll_predict'_success_result_in_original_subparsers in hp.
    destruct hp as [sp [hin heq']]; subst.
    eapply ll_start_state_sp_prediction_in_rhss_for; eauto.
  Qed.
  
  (** An ambiguous [ll_predict] prediction is always a right-hand side of [x] in the rhs_map. *)
  Lemma ll_predict_ambig_in_rhss_for :
    forall g hw rm pre vs x suf frs ts hk gamma,
      ll_predict g hw rm pre vs x suf frs ts hk = pred_ambig gamma
      -> In gamma (rhss_for x rm).
  Proof.
    intros g hw rm pre vs x suf frs ts hk gamma hp.
    apply ll_predict_cases in hp.
    destruct hp as [sps [heq hp]].
    apply ll_predict'_ambig_result_in_original_subparsers in hp.
    destruct hp as [sp [hin heq']]; subst.
    eapply ll_start_state_sp_prediction_in_rhss_for; eauto.
  Qed.

  (** A successful prediction corresponds to an actual production [(x, ys)] in the grammar. *)
  Lemma ll_predict_succ_in_grammar :
    forall g hw rm pre vs x suf frs ts hk ys,
      rhs_map_correct rm g
      -> ll_predict g hw rm pre vs x suf frs ts hk = pred_succ ys
      -> PM.In (x, ys) g.
  Proof.
    intros; eapply rhss_for_in_iff; eauto.
    eapply ll_predict_succ_in_rhss_for; eauto.
  Qed.

  (** An ambiguous prediction also corresponds to an actual production [(x, ys)] in the grammar. *)
  Lemma ll_predict_ambig_in_grammar :
    forall g hw rm pre vs x suf frs ts hk ys,
      rhs_map_correct rm g
      -> ll_predict g hw rm pre vs x suf frs ts hk = pred_ambig ys
      -> PM.In (x, ys) g.
  Proof.
    intros; eapply rhss_for_in_iff; eauto.
    eapply ll_predict_ambig_in_rhss_for; eauto.
  Qed.

  (* A WELL-FORMEDNESS PREDICATE OVER A SUFFIX STACK *)

  (* The stack predicate is defined in terms of the following
   predicate over a list of locations *)

  (** Inductively well-formed frame lists: each frame's symbols correspond to a valid grammar production. *)
  Inductive frames_wf (g : grammar) : list parser_frame -> Prop :=
  | wf_empty :
      frames_wf g []
  | wf_bottom_init :
      forall (x : nonterminal),
        frames_wf g [Fr [] tt [NT x]]
  | wf_bottom_final :
      forall (x : nonterminal) (v : nt_semty x),
        frames_wf g [Fr [NT x] (v, tt) []]
  | wf_upper :
      forall x pre pre' vs vs' suf suf' frs,
        PM.In (x, rev pre' ++ suf') g
        -> frames_wf g (                    Fr pre vs (NT x :: suf) :: frs)
        -> frames_wf g (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs).

  Hint Constructors frames_wf : core.

  (* invert a frames_wf judgment *)
  Ltac inv_fwf hw  hi hw' :=
    inversion hw as [ | ? | ? ? | ? ? ? ? ? ? ? ? hi hw']; subst; clear hw.

  Ltac wf_upper_nil := eapply wf_upper with (pre' := []); sis; eauto.

  (** Performing a return step (popping a frame) preserves the [frames_wf] invariant. *)
  Lemma return_preserves_frames_wf_invar :
    forall g frs x pre pre' vs vs' suf (f : symbols_semty (rev pre') -> nt_semty x),
      frames_wf g (Fr pre' vs' [] :: Fr pre vs (NT x :: suf) :: frs)
      -> frames_wf g (Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf :: frs).
  Proof.
    intros g frs x pre pre' vs vs' suf f hw; sis.
    inv_fwf hw hi hw'; rew_anr.
    inv_fwf hw' hi' hw''.
    - destruct vs; auto.
    - rewrite app_cons_group_l in hi'; auto.
  Qed.

  (** Pushing a new frame for a grammar production preserves the [frames_wf] invariant. *)
  Lemma push_preserves_frames_wf_invar :
    forall g pre vs x suf frs rhs,
      PM.In (x, rhs) g
      -> frames_wf g (Fr pre vs (NT x :: suf) :: frs)
      -> frames_wf g (Fr [] tt rhs :: Fr pre vs (NT x :: suf) :: frs).
  Proof.
    intros g pre vs x suf frs rhs hi hw.
    constructor; auto.
  Qed.

  (** Consuming a terminal symbol from a frame preserves the [frames_wf] invariant. *)
  Lemma consume_preserves_frames_wf_invar :
    forall g pre vs a suf vs' frs,
      frames_wf g (Fr pre vs (T a :: suf) :: frs)
      -> frames_wf g (Fr (T a :: pre) vs' suf :: frs).
  Proof.
    intros g pre vs a suf vs' frs hw; sis.
    inv_fwf hw hi hw'.
    rewrite app_cons_group_l in hi; auto.
  Qed.

  (* The parser stack well-formedness predicate *)
  (** Lifts [frames_wf] to a full parser stack. *)
  Definition stack_wf (g : grammar) (stk : parser_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_wf g (fr :: frs)
    end.

  (* Lift the predicate to a list of subparsers *)
  (** Requires [stack_wf] for every subparser in a list. *)
  Definition all_stacks_wf (g : grammar) (sps: list subparser) : Prop :=
    forall sp, In sp sps -> stack_wf g sp.(stack).

(*
  Definition frame_wf (g : grammar) (fr : parser_frame) :=
    match fr with
    | Fr x pre vs suf => PM.In (x, rev pre ++ suf) g
    end.
  
  Definition frames_wf (g : grammar) (frs : list parser_frame): Prop :=
    Forall (fun fr =>
              match fr with
              | Fr x pre vs suf => PM.In (x, rev pre ++ suf) g
              end) frs.
 *)

  (* The stack well-formedness predicate *)
(*  Definition stack_wf (g : grammar) (stk : parser_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_wf g (reconstr (fr :: frs))
    end.

  (* Lift the predicate to a list of subparsers *)
  Definition all_stacks_wf (g : grammar) (sps: list subparser) : Prop :=
    forall sp, In sp sps -> stack_wf g sp.(stack).
 *)

  (** A closure step preserves [stack_wf] for each newly produced subparser. *)
  Lemma cstep_preserves_stack_wf_invar :
    forall g hw rm sp sp' sps' vi vi',
      rhs_map_correct rm g
      -> stack_wf g sp.(stack)
      -> cstep g hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> stack_wf g sp'.(stack).
  Proof.
    intros g hw rm sp sp' sps' vi vi' hc hw' hs hi.
    unfold cstep in hs; dms; tc; sis; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst; sis.
      eapply return_preserves_frames_wf_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
      apply push_preserves_frames_wf_invar; auto.
      eapply rhss_for_in_iff; eauto.
  Qed.

  (** The initial subparser set inherits [stack_wf] from the caller's frame. *)
  Lemma ll_init_sps_preserves_stack_wf_invar :
    forall g rm fr pre vs x suf frs,
      rhs_map_correct rm g
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_wf g (fr, frs)
      -> all_stacks_wf g (ll_init_sps rm pre vs x suf frs).
  Proof.
    intros g rm fr pre vs x suf frs hc ? hw sp hi; subst; unfold ll_init_sps in hi.
    apply in_map_iff in hi.
    destruct hi as [rhs [? hi]]; subst; sis.
    apply push_preserves_frames_wf_invar; eauto.
    eapply rhss_for_in_iff; eauto.
  Qed.    

  (* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

  (* Auxiliary definition *)
  (** Frames form a chain where each pushed frame is reachable via a nullable path in the grammar. *)
    Inductive frames_repr_nullable_path (g : grammar) : list parser_frame -> Prop :=
  | fr_direct :
      forall x pre pre' vs vs' suf suf',
        PM.In (x, rev pre' ++ suf') g
        -> nullable_gamma g (rev pre')
        -> frames_repr_nullable_path g [Fr pre' vs' suf' ; Fr pre vs (NT x :: suf)]
  | fr_indirect :
      forall x pre pre' vs vs' suf suf' frs,
        PM.In (x, rev pre' ++ suf') g
        -> nullable_gamma g (rev pre')
        -> frames_repr_nullable_path g (                    Fr pre vs (NT x :: suf) :: frs)
        -> frames_repr_nullable_path g (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs).

  Hint Constructors frames_repr_nullable_path : core.

  Ltac inv_frnp hf hi hn hf' :=
    inversion hf as [? ? ? ? ? ? ? hi hn | ? ? ? ? ? ? ? ? hi hn hf']; subst; clear hf.

  (** Strips the top frame of a nullable-path chain, preserving the rest. *)
  Lemma frnp_inv_two_head_frames :
    forall g fr fr' fr'' frs,
      frames_repr_nullable_path g (fr'' :: fr' :: frs ++ [fr])
      -> frames_repr_nullable_path g (fr' :: frs ++ [fr]).
  Proof.
    intros g fr fr'' fr''' frs hf.
    destruct frs as [| fr' frs]; sis; inv hf; auto.
  Qed.

  (** The second frame in a nullable-path chain must have a nonterminal at the head of its suffix. *)
  Lemma frnp_second_frame_nt_head :
    forall g fr fr' frs,
      frames_repr_nullable_path g (fr' :: fr :: frs)
      -> exists pre vs x suf,
        fr = Fr pre vs (NT x :: suf).
  Proof.
    intros g fr fr' frs hf; inv hf; eauto.
  Qed.

  (** Shifting a nullable prefix into the processed portion of a frame preserves the nullable-path invariant. *)
  Lemma frnp_shift_head_frame :
    forall g pre vs suf suf' vs' frs,
      nullable_gamma g suf
      -> frames_repr_nullable_path g (Fr pre vs (suf ++ suf') :: frs)
      -> frames_repr_nullable_path g (Fr (rev suf ++ pre) vs' suf' :: frs).
  Proof.
    intros g pre vs suf suf' vs' frs hn hf; destruct frs as [| fr frs]; inv_frnp hf hi hn' hf'.
    - rewrite app_assoc in hi; constructor.
      + rewrite rev_app_distr.
        rewrite rev_involutive; auto.
      + rewrite rev_app_distr.
        rewrite rev_involutive.
        apply nullable_app; auto.
    - rewrite app_assoc in hi; constructor; auto.
      + rewrite rev_app_distr.
        rewrite rev_involutive; auto.
      + rewrite rev_app_distr.
        rewrite rev_involutive.
        apply nullable_app; auto.
  Qed.

  (** A nullable-path chain from [y]'s frame to [x]'s frame witnesses a nullable path from [x] to [y] in the grammar. *)
  Lemma frnp_grammar_nullable_path :
    forall g frs fr fr_cr x y pre pre' vs vs' suf suf',
      fr       = Fr pre' vs' (NT y :: suf')
      -> fr_cr = Fr pre vs (NT x :: suf)
      -> frames_repr_nullable_path g (fr :: frs ++ [fr_cr])
      -> nullable_path g (NT x) (NT y).
  Proof.
    intros g frs.
    induction frs as [| fr' frs IH];
      intros fr fr_cr x y pre pre' vs vs' suf suf' ? ? hf; subst; sis.
    - inv_frnp hf hi hn hf'.
      + eapply direct_path; eauto.
      + inv hf'.
    - pose proof hf as hf'; apply frnp_second_frame_nt_head in hf'.
      destruct hf' as [pre'' [vs'' [y'' [suf'' ?]]]]; subst. 
      apply nullable_path_trans with (y := NT y'').
      + apply frnp_inv_two_head_frames in hf; eauto.
      + inv_frnp hf hi hn hf'; eauto.
  Qed.
      
  (** If the callee's suffix is nullable and the chain holds, then the called nonterminal [x] is nullable. *)
  Lemma frnp_caller_nt_nullable :
    forall g x pre pre' vs vs' suf suf' frs,
      frames_repr_nullable_path g (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs)
      -> nullable_gamma g suf'
      -> nullable_sym g (NT x).
  Proof.
    intros g x pre pre' vs vs' suf suf' frs hf hng. 
    inv_frnp hf hi hn hf'.
    - econstructor; eauto.
      apply nullable_app; auto.
    - econstructor; eauto.
      apply nullable_app; auto.
  Qed.

  (* The invariant itself *)
  (** Every nonterminal in [vi] corresponds to an open call frame reachable via a nullable path in [stk]. *)
  Definition unavailable_nts_are_open_calls g vi stk : Prop :=
    match stk with
    | (fr, frs) =>
      forall (x : nonterminal),
        NtSet.In x (all_nts g)
        -> NtSet.In x vi
        -> exists frs_pre fr_cr frs_suf pre vs suf,
            frs = frs_pre ++ fr_cr :: frs_suf
            /\ fr_cr = Fr pre vs (NT x :: suf)
            /\ frames_repr_nullable_path g (fr :: frs_pre ++ [fr_cr])
    end.

  (* Lift the invariant to a subparser *)
  (** Lifts [unavailable_nts_are_open_calls] to a subparser. *)
  Definition unavailable_nts_invar g vi sp :=
    match sp with
    | Sp _ stk => unavailable_nts_are_open_calls g vi stk
    end.

  (* Lift the invariant to a list of subparsers *)
  (** Requires [unavailable_nts_invar] for every subparser in a list. *)
  Definition sps_unavailable_nts_invar g vi sps : Prop :=
    forall sp, In sp sps -> unavailable_nts_invar g vi sp.

  (** A return step removes [x] from [vi], maintaining the unavailable-nts invariant after popping. *)
  Lemma return_preserves_unavailable_nts_invar :
    forall g vi pr fr cr cr' x pre pre' vs vs' vs'' suf frs,
      fr     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) vs'' suf
      -> unavailable_nts_invar g vi (Sp pr (fr, cr :: frs))
      -> unavailable_nts_invar g (NtSet.remove x vi) (Sp pr (cr', frs)). 
  Proof.
    intros g vi pr fr cr cr' x' pre pre' vs vs' vs'' suf frs ? ? ? hu; subst. 
    intros x hi hn.
    assert (hn' : NtSet.In x vi) by ND.fsetdec.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & heq & ? & hf); subst; sis.
    destruct frs_pre as [| fr' frs_pre]; inv heq.
    - ND.fsetdec. 
    - pose proof hf as hf'.
      apply frnp_inv_two_head_frames in hf.
      eapply frnp_shift_head_frame with (suf := [NT x']) in hf; eauto 9.
      constructor; auto.
      apply frnp_caller_nt_nullable in hf'; auto.
  Qed.

  (** A push step adds [x] to [vi], maintaining the unavailable-nts invariant after pushing. *)
  Lemma push_preserves_unavailable_nts_invar :
    forall g cr ce vi pr pre vs x suf rhs frs,
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> PM.In (x, rhs) g
      -> unavailable_nts_invar g vi (Sp pr (cr, frs))
      -> unavailable_nts_invar g (NtSet.add x vi) (Sp pr (ce, cr :: frs)).
  Proof.
    intros g cr ce vi pr pre vs x' suf rhs frs ? ? hi hu; subst. 
    intros x hi' hn.
    destruct (NF.eq_dec x' x); subst.
    - exists []; repeat eexists; eauto; sis.
      eapply fr_direct with (pre' := []); sis; auto.
    - assert (hn' : NtSet.In x vi) by ND.fsetdec.
      apply hu in hn'; simpl in hn'; clear hu; auto.
      destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & ? & ? & hf); subst; sis.
      exists (Fr pre vs (NT x' :: suf) :: frs_pre); repeat eexists; sis; eauto.
  Qed.

  (** A closure step preserves the unavailable-nts invariant for each produced subparser. *)
  Lemma cstep_preserves_unavailable_nts_invar :
    forall g hw rm sp sp' sps' vi vi',
      rhs_map_correct rm g
      -> unavailable_nts_invar g vi sp
      -> cstep g hw rm vi sp = cstep_k vi' sps'
      -> In sp' sps'
      -> unavailable_nts_invar g vi' sp'.
  Proof.
    intros g hw rm sp sp' sps' vi vi' hc hu hs hi.
    unfold cstep in hs; dmeqs h; inv hs; tc; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      eapply return_preserves_unavailable_nts_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply push_preserves_unavailable_nts_invar; eauto.
      eapply rhss_for_in_iff; eauto.
  Qed.

  (** The invariant holds trivially when the visited set is empty, since no nonterminal is marked unavailable. *)
  Lemma unavailable_nts_empty :
    forall g pred stk,
      unavailable_nts_invar g NtSet.empty (Sp pred stk).
  Proof.
    intros g pred (fr, frs); repeat red; intros; ND.fsetdec.
  Qed.
  
End LLPredictionFn.
