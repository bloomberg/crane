(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import FMaps PeanoNat String.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import SLLPredictionComplete.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Termination.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Module ParserFn (Import D : Defs.T).

  Module Export SLLPC := SllPredictionCompleteFn D.

  (** Errors the parser can encounter: invalid internal state, left recursion detected, or a prediction failure. *)
  Inductive parse_error :=
  | invalid_state    : parse_error
  | left_recursion   : nonterminal -> parse_error
  | prediction_err : prediction_error -> parse_error.

  (* For validation *)
  (** Converts a [parse_error] to a human-readable string for diagnostic output. *)
  Definition show_parse_error (e : parse_error) : string :=
    match e with
    | invalid_state      => "invalid_state"
    | left_recursion x   => "left_recursion " ++ showNT x
    | prediction_err e => "prediction_err (" ++ show_prediction_error e ++ ")"
    end.
 
  (** The outcome of a single parsing step: acceptance, rejection, continuation with a new state, or an error. *)
  Inductive step_result : Type :=
  | step_accept : forall (x : nonterminal), nt_semty x -> step_result
  | step_reject : string -> step_result
  | step_k      : parser_stack -> list token -> NtSet.t -> bool -> cache -> step_result
  | step_error  : parse_error -> step_result.

  (** Witnesses that the stack-pushes-from-keyset invariant is preserved when the top frame has a nonterminal head. *)
  Lemma lhss_invar_eqs :
    forall rm sk pre vs suf x suf' frs,
      stack_pushes_from_keyset rm sk
      -> sk = (Fr pre vs suf, frs)
      -> suf = NT x :: suf'
      -> stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf'), frs).
  Proof.
    intros; subst; auto.
  Qed.
  
  (** Builds the rejection message when the stack is exhausted but tokens remain. *)
  Definition empty_stack_msg (t : token) : string :=
    "parser stack exhausted but tokens remain\n " ++
    "next token: " ++ show_token t.

  (** Builds the rejection message when the input is empty but a terminal is expected. *)
  Definition empty_input_msg (a : terminal) : string :=
    "empty input while trying to match terminal " ++ showT a.

  (** Builds the rejection message when the next parser terminal does not match the next input token. *)
  Definition mismatch_msg (a : terminal) (t : token) : string :=
    "terminal mismatch, next parser terminal: " ++ showT a ++
    ", next input token: " ++ show_token t.

  (** Builds the rejection message when a nonterminal has no entry in the grammar. *)
  Definition not_found_msg (x : nonterminal) : string :=
    showNT x ++ " is not a left-hand side in the grammar".

  (** Builds the rejection message when SLL prediction finds no viable right-hand side for a nonterminal. *)
  Definition failed_prediction_msg (x : nonterminal) (ts : list token) : string :=
    "prediction found no viable right-hand sides for " ++ showNT x ++
    match ts with
    | []     => ""
    | t :: _ => ", next token: " ++ show_token t
    end.

  (** Performs one parsing step: returns/reduces if the frame suffix is empty, consumes a terminal token, or calls [adaptive_predict] to push a new frame for a nonterminal. *)
  Definition step
             (gr : grammar)
             (hw : grammar_wf gr)
             (rm : rhs_map)
             (cm : closure_map)
             (sk : parser_stack)
             (ts : list token)
             (vi : NtSet.t)
             (un : bool) 
             (ca : cache)
             (hc : cache_stores_target_results rm cm ca)
             (hk : stack_pushes_from_keyset rm sk) : step_result :=
    match sk as sk' return sk = sk' -> _ with
    | (Fr pre vs suf, frs) =>
      fun hsk =>
        match suf as suf' return suf = suf' -> _ with
        (* no more symbols to process in current frame *)
        | [] =>
          fun _ =>
            match frs with
            (* empty stack --> terminate *)
            | [] => 
              match ts with
              | [] =>
                match pre, vs with
                | [NT x], (v, tt) => step_accept x v
                | _, _ => step_error invalid_state
                end
              | t :: _ => step_reject (empty_stack_msg t)
              end
            (* nonempty stack --> return to caller frame *)
            | Fr pre_cr vs_cr (NT x :: suf_cr) :: frs' =>
              let pre' := rev pre in
              let vs'  := rev_tuple pre vs in
              match find_predicate_and_action (x, pre') gr hw with
              (* check predicate and reduce *)
              | Some (p, f) =>
                if p vs' then
                  let sk' := (Fr (NT x :: pre_cr) (f vs', vs_cr) suf_cr, frs')
                  in  step_k sk' ts (NtSet.remove x vi) un ca
                else
                  step_reject "some failed predicate message here"
              (* impossible case *)
              | None =>
                step_error invalid_state
              end
            | _ => step_error invalid_state
            end
        (* terminal case --> consume a token *)
        | T a :: suf' =>
          fun _ => 
            match ts with
            | []             => step_reject (empty_input_msg a)
            | @existT _ _ a' v :: ts' =>
              if t_eq_dec a' a then
                let sk' := (Fr (T a' :: pre) (v, vs) suf', frs)
                in  step_k sk' ts' NtSet.empty un ca
              else
                step_reject (mismatch_msg a (@existT _ _ a' v))
            end
        (* nonterminal case --> push a frame onto the stack *)
        | NT x :: suf' =>
          fun hsuf =>
            if NtSet.mem x vi then
              (* Unreachable for a left-recursive grammar *)
              match NM.find x rm with
              | Some _ => step_error (left_recursion x) 
              | None   => step_reject (not_found_msg x)
              end
            else
              match adaptive_predict gr hw rm cm pre vs x suf' frs ts ca hc
                                    (lhss_invar_eqs _ _ _ _ _ _ _ _ hk hsk hsuf)
              with
              | (pred_succ rhs, ca') =>
                let sk' := (Fr [] tt rhs, Fr pre vs (NT x :: suf') :: frs) in
                step_k sk' ts (NtSet.add x vi) un ca'
              | (pred_ambig rhs, ca') =>
                let sk' := (Fr [] tt rhs, Fr pre vs (NT x :: suf') :: frs) in
                step_k sk' ts (NtSet.add x vi) false ca'
              | (pred_reject, _)  =>
                step_reject (failed_prediction_msg x ts)
              | (pred_error e, _) =>
                step_error (prediction_err e) 
              end
        end eq_refl
    end eq_refl.

  (** If [step] returns [step_accept], then the input is empty and the stack holds exactly the start nonterminal with its computed value. *)
  Lemma step_step_accept_facts :
    forall gr hw rm cm sk ts vi un ca hc hk x v,
      step gr hw rm cm sk ts vi un ca hc hk = step_accept x v
      -> ts = []
         /\ sk = (Fr [NT x] (v, tt) [], []).
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk y v hs.
    unfold step in hs; dms; tc.
    inv hs; auto. 
  Qed.

  (** If [step] raises [left_recursion x], then [x] is in the visited set and appears in the rhs map, confirming an open recursive call. *)
  Lemma step_left_recursion_facts :
    forall gr hw rm cm sk ts vi un ca hc hk x,
      step gr hw rm cm sk ts vi un ca hc hk = step_error (left_recursion x)
      -> NtSet.In x vi
         /\ (exists yss, NM.find x rm = Some yss)
         /\ (exists pre vs suf frs,
             sk = (Fr pre vs (NT x :: suf), frs)). 
  Proof.
    intros gr hw cm rm sk ts vi un ca hc hk x hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis;
      repeat split; eauto.
    apply NF.mem_iff; auto.
  Qed.

  (** A [step_k] result carries over the cache invariant: the updated cache still stores correct target results. *)
  Lemma step_preserves_cache_invar :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hs.
    unfold step in hs; dmeqs H; tc; inv hs; auto.
    - eapply adaptive_predict_succ_preserves_cache_invar;  eauto.
    - eapply adaptive_predict_ambig_preserves_cache_invar; eauto.
  Defined.

  (** A [step_k] result preserves the stack-pushes-from-keyset invariant, so every pushed nonterminal is in the rhs map domain. *)
  Lemma step_preserves_pki :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      rhs_map_correct rm gr
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> stack_pushes_from_keyset rm sk'.
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hr hs.
    unfold step in hs; dmeqs H; tc; inv hs; red; red in hk; sis.
    - eapply return_preserves_keyset_invar; eauto.
    - eapply consume_preserves_keyset_invar; eauto.
    - eapply push_preserves_keyset_invar; eauto.
      eapply rhss_for_key_set.
      eapply adaptive_predict_succ_in_rhss_for; eauto.
    - eapply push_preserves_keyset_invar; eauto.
      eapply rhss_for_key_set.
      eapply ll_predict_ambig_in_rhss_for; eauto.
      eapply adaptive_predict_ambig_ll_predict_ambig; eauto.
  Qed.

  (** Asserts that the bottom frame of the stack contains exactly [NT x] as its sole symbol, tying the stack to the start nonterminal. *)
  Definition bottom_stack_sym_eq_start_sym (sk : parser_stack) (x : nonterminal) : Prop :=
    bottom_frame_syms sk = [NT x].

  (** A [step_k] result preserves the invariant that the bottom frame symbols equal the start nonterminal. *)
  Lemma step_preserves_bfs_invar :
    forall gr hw x rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      bottom_stack_sym_eq_start_sym sk x
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> bottom_stack_sym_eq_start_sym sk' x.
  Proof.
    intros gr hw x rm cm (fr, frs) (fr', frs') ts ts' vi vi' un un' ca ca' hc hk hb hs.
    unfold step in hs; dmeqs H; tc; inv hs; inv hb;
      unfold bottom_stack_sym_eq_start_sym in *; unfold bottom_frame_syms in *; auto.
    - destruct frs'; sis; auto; apps.
    - destruct frs'; sis; auto; apps.
  Qed.

  (** If [step] accepts with nonterminal [x'], and the bottom frame is [x], then [x' = x]. *)
  Lemma step_accept_result_eq_start :
    forall gr hw rm cm sk ts vi un ca hc hk x x' v,
      bottom_stack_sym_eq_start_sym sk x
      -> step gr hw rm cm sk ts vi un ca hc hk = step_accept x' v
      -> x' = x.
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk x x' v hb hs.
    apply step_step_accept_facts in hs.
    destruct hs as (heq & heq'); subst.
    inv hb; auto.
  Qed.
        
  (* termination-related lemmas for the multistep function below *)

  (** The lexicographic termination measure: [input length], then stack score, then stack height. *)
  Definition parser_meas
             (rm : rhs_map)
             (sk : parser_stack)
             (ts : list token)
             (vi :  NtSet.t) : nat * nat * nat :=
    let (stkScore, stkHeight) := meas rm vi (stack_suffixes sk)
    in  (List.length ts, stkScore, stkHeight).

  (** The measure strictly decreases after a return step, because removing a nonterminal from the visited set lowers the stack score. *)
  Lemma parser_meas_lt_after_return :
    forall rm ce cr cr' pre pre' pre'' vs vs' vs'' x suf frs ts vi,
      ce     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr pre'' vs'' suf
      -> stack_pushes_from_keyset rm (ce, cr :: frs)
      -> lex_nat_triple (parser_meas rm (cr', frs) ts (NtSet.remove x vi))
                        (parser_meas rm (ce, cr :: frs) ts vi).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? hk; subst; unfold meas.
    red in hk.
    eapply meas_lt_after_return with (vi := vi) in hk; sis; eauto.
    inversion hk as [ ? ? ? ? hl | ? ? ? hl heq heq']; subst; clear hk.
    - apply triple_snd_lt; auto.
    - unfold parser_meas; sis; rewrite heq'.
      apply triple_thd_lt; auto.
  Defined.

  (** The measure strictly decreases after a push step, because adding [x] to the visited set lowers the stack score by removing high-score right-hand sides. *)
  Lemma parser_meas_lt_after_push :
    forall rm cr ce pre vs x suf rhs frs ts vi,
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> In rhs (rhss_for x rm)
      -> NtSet.mem x vi = false 
      -> lex_nat_triple (parser_meas rm (ce, cr :: frs) ts (NtSet.add x vi))
                        (parser_meas rm (cr, frs) ts vi).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hi hm; subst.
    apply triple_snd_lt.
    eapply stack_score_lt_after_push; sis; auto.
    - eapply rhss_for_key_set; eauto.
    - apply NF.not_mem_iff in hm; auto.
    - eapply rhss_for_all_rhss; eauto.
  Defined.
  
  (** Every [step_k] outcome strictly decreases the lexicographic parsing measure, establishing termination. *)
  Lemma step_parser_meas_lt :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> lex_nat_triple (parser_meas rm sk' ts' vi') (parser_meas rm sk ts vi).
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hs; unfold step in hs.
    destruct sk as ([pre vs suf], frs).
    dmeqs H; tc; inv hs.
    - eapply parser_meas_lt_after_return with (pre'' := NT _ :: _); eauto.
    - apply triple_fst_lt; auto.
    - eapply parser_meas_lt_after_push; eauto.
      eapply adaptive_predict_succ_in_rhss_for; eauto.
    - eapply parser_meas_lt_after_push; eauto.
      eapply ll_predict_ambig_in_rhss_for; eauto.
      eapply adaptive_predict_ambig_ll_predict_ambig; eauto.
  Qed.

  (** Extracts the [Acc] witness for the successor state from the current [Acc] proof, enabling structural recursion in [multistep]. *)
  Lemma step_k_result_acc :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca'
           hc hk (a : Acc lex_nat_triple (parser_meas rm sk ts vi)),
      step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> Acc lex_nat_triple (parser_meas rm sk' ts' vi').
  Proof.
    intros; eapply Acc_inv; eauto.
    eapply step_parser_meas_lt; eauto.
  Defined.

  (** The final outcome of parsing: a unique semantic value, an ambiguous one, a rejection, or an error. *)
  Inductive parse_result (x : nonterminal) : Type :=
  | unique : nt_semty x  -> parse_result x
  | ambig  : nt_semty x  -> parse_result x
  | result_reject : string      -> parse_result x
  | result_error  : parse_error -> parse_result x.
  
  (* For validation *)
  (** Converts a [parse_result] to a human-readable string for diagnostic output. *)
  Definition show_result (x : nonterminal) (pr : parse_result x) : string :=
    match pr with
    | unique _ v => "unique"
    | ambig  _ v => "ambig"
    | result_reject _ s => "result_reject: " ++ s
    | result_error  _ e => "result_error:  " ++ show_parse_error e
    end.

  (** The main parsing loop: repeatedly calls [step] until it reaches an [Accept], [result_reject], or [result_error]; structurally recursive on the accessibility proof. *)
  Fixpoint multistep
           (gr : grammar)
           (hw : grammar_wf gr)
           (rm : rhs_map)
           (hr : rhs_map_correct rm gr)
           (cm : closure_map)
           (x  : nonterminal)
           (sk : parser_stack)
           (ts : list token)
           (vi : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results rm cm ca)
           (hk : stack_pushes_from_keyset rm sk)
           (hb : bottom_stack_sym_eq_start_sym sk x)
           (ha : Acc lex_nat_triple (parser_meas rm sk ts vi))
           {struct ha} : parse_result x :=
    match step gr hw rm cm sk ts vi un ca hc hk as res return step gr hw rm cm sk ts vi un ca hc hk = res -> _ with
    | step_accept x' v' =>
      fun hs  =>
        let v := cast_nt_semty x' x (step_accept_result_eq_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs) v'
        in  if un then unique x v else ambig x v
    | step_reject s              => fun _  => result_reject _ s
    | step_error e               => fun _  => result_error  _ e
    | step_k sk' ts' vi' un' ca' =>
      fun hs => multistep gr hw rm hr cm x sk' ts' vi' un' ca'
                          (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                          (step_preserves_pki _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hr hs)
                          (step_preserves_bfs_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs)
                          (step_k_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
    end eq_refl.

  (** Unfolds one iteration of [multistep] into a [match] on [step], useful for reasoning by cases. *)
  Lemma multistep_unfold :
    forall gr hw rm hr cm x sk ts vi un ca hc hk hb ha,
      multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha =
      match step gr hw rm cm sk ts vi un ca hc hk as res return step gr hw rm cm sk ts vi un ca hc hk = res -> _ with
      | step_accept x' v' =>
        fun hs =>
          let v := cast_nt_semty x' x (step_accept_result_eq_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs) v'
          in  if un then unique x v else ambig x v
      | step_reject s                  => fun _  => result_reject _ s
      | step_error e                   => fun _  => result_error  _ e
      | step_k sk' ts' vi' un' ca' =>
        fun hs => multistep gr hw rm hr cm x sk' ts' vi' un' ca'
                            (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (step_preserves_pki _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hr hs)
                            (step_preserves_bfs_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs)
                            (step_k_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
      end eq_refl.
  Proof.
    intros; destruct ha; auto.
  Qed.
  
  (** Internal case analysis on [multistep]: a given result either arose directly from [step] or from a recursive call after a [step_k]. *)
  Lemma multistep_cases' :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (rm  : rhs_map)
           (hr  : rhs_map_correct rm gr)
           (cm  : closure_map)
           (x   : nonterminal)
           (sk  : parser_stack)
           (ts  : list token)
           (vi  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (hc  : cache_stores_target_results rm cm ca)
           (hk  : stack_pushes_from_keyset rm sk)
           (hb  : bottom_stack_sym_eq_start_sym sk x)
           (ha  : Acc lex_nat_triple (parser_meas rm sk ts vi))
           
           (sr  : step_result)
           (pr  : parse_result x)
           (heq : step gr hw rm cm sk ts vi un ca hc hk = sr),
      match sr as res return (step gr hw rm cm sk ts vi un ca hc hk = res -> parse_result x) with
      | step_accept x' v' =>
        fun hs =>
          let v := cast_nt_semty x' x (step_accept_result_eq_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs) v'
          in  if un then unique x v else ambig x v
      | step_reject s                  => fun _ => result_reject _ s
      | step_error s                   => fun _ => result_error _ s
      | step_k sk' ts' vi' un' ca' =>
        fun hs => multistep gr hw rm hr cm x sk' ts' vi' un' ca'
                            (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (step_preserves_pki _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hr hs)
                            (step_preserves_bfs_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs)
                            (step_k_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
      end heq = pr
      -> match pr with
         | unique _ f => (sr = step_accept x f /\ un = true)
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = step_k sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = unique x f)
         | ambig _ f  => (sr = step_accept x f /\ un = false)
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = step_k sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = ambig x f)
         | result_reject _ s => sr = step_reject s
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = step_k sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = result_reject _ s)
         | result_error _ s  => sr = step_error s
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = step_k sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = result_error _ s)
         end.
  Proof.
    intros gr hw rm hr cm x sk ts vi un ca hc hk hb ha sr pr heq.
    destruct pr; destruct sr; destruct un;
      try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto 12].
    - pose proof heq as heq'.
      eapply step_accept_result_eq_start in heq'; eauto; subst.
      rewrite cast_nt_semty_refl; simpl.
      intros heq'; inv heq'; auto.
    - pose proof heq as heq'.
      eapply step_accept_result_eq_start in heq'; eauto; subst.
      rewrite cast_nt_semty_refl; simpl.
      intros heq'; inv heq'; auto.
  Qed.

  (** Public case analysis on [multistep]: decomposes any [parse_result] into a direct [step] outcome or a continuation. *)
  Lemma multistep_cases :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (rm  : rhs_map)
           (hr  : rhs_map_correct rm gr)
           (cm  : closure_map)
           (sk  : parser_stack)
           (x   : nonterminal)
           (ts  : list token)
           (vi  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (hc  : cache_stores_target_results rm cm ca)
           (hb  : bottom_stack_sym_eq_start_sym sk x)
           (hk  : stack_pushes_from_keyset rm sk)
           (ha  : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (pr  : parse_result x),
      multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha = pr
      -> match pr with
         | unique _ f => (step gr hw rm cm sk ts vi un ca hc hk = step_accept x f /\ un = true)
                         \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                                step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
                                /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = unique x f)
         | ambig _ f  => (step gr hw rm cm sk ts vi un ca hc hk = step_accept x f /\ un = false)
                         \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                                step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
                                /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = ambig x f)
         | result_reject _ s => step gr hw rm cm sk ts vi un ca hc hk = step_reject s
                         \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                                step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = result_reject x s)
         | result_error _ s  => step gr hw rm cm sk ts vi un ca hc hk = step_error s
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = result_error x s)
         end.
  Proof.
    intros gr hw rm hr cm x sk ts vi un ca hc hk hb ha pr hm; subst.
    rewrite multistep_unfold.
    eapply multistep_cases'; eauto.
  Qed.
  
  (** The empty cache trivially satisfies the cache invariant, providing the initial proof for [parse]. *)
  Lemma cache_invar_starts_true :
    forall rm cm,
      cache_stores_target_results rm cm empty_cache.
  Proof.
    intros rm cm sps a sps' hf.
    rewrite CacheFacts.empty_o in hf; tc.
  Defined.

  (** The initial stack [([NT x], [])] satisfies the stack-pushes-from-keyset invariant. *)
  Lemma push_invar_starts_true :
    forall rm x,
      stack_pushes_from_keyset rm (Fr [] tt [NT x], []). 
  Proof.
    intros rm x; repeat red; sis; auto.
  Qed.

  (** The initial stack satisfies the bottom-frame-symbol invariant for start nonterminal [x]. *)
  Lemma bottom_stack_sym_invar_start_true :
    forall x,
      bottom_stack_sym_eq_start_sym (Fr [] tt [NT x], []) x.
  Proof.
    intros x; red; auto.
  Qed.

  (* This curried pattern enables us to partially apply the parser to a grammar
     and compute the closure map once, instead of each time we parse an input *)
  (** Top-level entry point: initialises the rhs map and closure map once, then invokes [multistep] from the start state. *)
  Definition parse (gr : grammar) (hw : grammar_wf gr) : forall (x : nonterminal), list token -> parse_result x := 
    let rm := mk_rhs_map gr         in
    let hr := mk_rhs_map_correct gr in
    let cm := mk_closure_map gr     in
    fun (x : nonterminal) (ts : list token) =>
      let sk0 := (Fr [] tt [NT x], []) in
      multistep gr hw rm hr cm x sk0 ts NtSet.empty true empty_cache
                (cache_invar_starts_true rm cm)
                (push_invar_starts_true _ _)
                (bottom_stack_sym_invar_start_true _)
                (lex_nat_triple_wf _).

End ParserFn.
