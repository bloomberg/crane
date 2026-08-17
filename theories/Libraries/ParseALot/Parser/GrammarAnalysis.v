(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List MSets Relation_Operators Wf_nat.
From Crane.Libraries.ParseALot.Parser Require Import Orders.
From Crane.Libraries.ParseALot.Parser Require Import LLPredictionComplete.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.
From Stdlib Require Import FSets FSets.FMapAVL FSets.FMapFacts.
Require Import CoLoR.Util.FGraph.TransClos.

Module GrammarAnalysisFn (Import D : Defs.T).

  Module Export LLPC := LLPredictionCompleteFn D.
  
  (* The definition of "stability" for SLL stacks *)
  (** An SLL stack is stable when the top frame ends in a terminal or is the empty bottom frame,
      i.e., no epsilon closure step is needed. *)
  Inductive sll_stable_config : sll_stack -> Prop :=
  | sll_sc_empty :
      sll_stable_config (sll_fr None [], [])
  | sll_sc_terminal :
      forall o a suf frs,
        sll_stable_config (sll_fr o (T a :: suf), frs).

  Hint Constructors sll_stable_config : core.
  
  (** Checks that every subparser in a list has a stable SLL stack. *)
  Definition all_stable sps :=
    forall sp, In sp sps -> sll_stable_config sp.(sll_stk).

  (* Graph in which nodes are suffix frames, and edges 
     connect "closure-reachable" frames *)

  (** A directed edge between two SLL frames, used to represent closure reachability. *)
  Definition edge := (sll_frame * sll_frame)%type.

  (** Returns the source frame of an edge. *)
  Definition src (e : edge) : sll_frame := fst e.
  (** Returns the destination frame of an edge. *)
  Definition dst (e : edge) : sll_frame := snd e.

  (** One-step reachability between SLL frames, covering push, return, and initial-push transitions. *)
  Inductive frame_step (g : grammar) :
    sll_frame -> sll_frame -> Prop :=
  | Fstep_final_ret :
      forall x ys,
        PM.In (x, ys) g
        -> frame_step g (sll_fr (Some x) [])
                        (sll_fr  None    [])
  | Fstep_nonfinal_ret :
      forall x y pre suf,
        PM.In (x, pre ++ NT y :: suf) g
        -> frame_step g (sll_fr (Some y) [])
                        (sll_fr (Some x) suf)
  | Fstep_initial_push :
      forall x rhs,
        PM.In (x, rhs) g
        -> frame_step g (sll_fr None     [NT x])
                        (sll_fr (Some x) rhs)
  | Fstep_noninitial_push :
      forall x y pre suf rhs,
        PM.In (x, pre ++ NT y :: suf) g
        -> PM.In (y, rhs) g
        -> frame_step g (sll_fr (Some x) (NT y :: suf))
                        (sll_fr (Some y) rhs).

  Hint Constructors frame_step : core.

  (* Correspondence between closure_multistep and frame_step relations *)

  (** Projects the top LL stack frame onto the corresponding SLL frame representation. *)
  Definition sllify_head (stk : parser_stack) : sll_frame :=
    match stk with
    | (Fr _ _ suf, frs) =>
      match frs with
      | [] => sll_fr None suf
      | Fr _ _ (NT x :: _) :: _ => sll_fr (Some x) suf
      (* impossible for a well-formed stack *)
      | _ => sll_fr None []
      end
    end.
  
  (** A single LL closure step induces a corresponding frame_step on the SLL frame heads. *)
  Lemma closure_step__frame_step :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> stack_wf g (fr, frs)
      -> closure_step g av sp av' sp'
      -> frame_step g (sllify_head (fr, frs)) (sllify_head (fr', frs')). 
  Proof.
    intros g av av' ? ? pr pr' fr fr' frs frs' ? ? hw hc; subst; inv hc; eauto.
    - inv_fwf hw hi hw'; rew_anr.
      inv_fwf hw' hi' hw''; rew_anr; sis; eauto.
    - inv_fwf hw hi hw'; sis; eauto.
  Qed.

  (** Extends closure_step__frame_step to multiple steps, yielding a reflexive-transitive chain. *)
  Lemma closure_multistep__frame_step_trc' :
    forall g av av' sp sp',
      stack_wf g (stack sp)
      -> closure_multistep g av sp av' sp'
      -> (forall pr pr' fr fr' frs frs',
             sp     = Sp pr  (fr, frs)
             -> sp' = Sp pr' (fr', frs')
             -> clos_refl_trans_1n _ (frame_step g) (sllify_head (fr, frs)) (sllify_head (fr', frs'))).
  Proof.
    intros g av av' sp sp' hw hc. 
    induct_cm hc hs hc' IH; intros pr pr' fr fr' ? ? heq heq'; subst.
    - inv heq; inv heq'; apply rt1n_refl.
    - inv heq; inv heq'; apply rt1n_refl.
    - pose proof hs as hs'; inv hs'. 
      + (* return case *)
        eapply closure_step__frame_step in hs; eauto.
        econstructor; eauto.
        eapply IH; eauto.
        apply return_preserves_frames_wf_invar; eauto.
      + (* push case *)
        eapply closure_step__frame_step in hs; eauto.
        econstructor; eauto.
        eapply IH; eauto.
        apply push_preserves_frames_wf_invar; auto.
  Qed.
  
  (** Convenience wrapper: extracts the reflexive-transitive frame_step chain from a closure_multistep. *)
  Lemma closure_multistep__frame_step_trc :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> stack_wf g (stack sp)
      -> closure_multistep g av sp av' sp'
      -> clos_refl_trans_1n _ (frame_step g) (sllify_head (fr,frs)) (sllify_head (fr', frs')).
  Proof.
    intros; eapply closure_multistep__frame_step_trc'; eauto.
  Qed.
  
  (* COMPUTATION OF SINGLE-STEP FRAME CLOSURE EDGES *)

  (** Every edge in the list is a valid single-step frame transition. *)
  Definition step_edges_sound (g : grammar) (es : list edge) :=
    forall x y, In (x, y) es -> frame_step g x y.

  (** Every single-step frame transition is represented in the list. *)
  Definition step_edges_complete (g : grammar) (es : list edge) :=
    forall x y, frame_step g x y -> In (x, y) es.

  (** Multi-step (transitive closure) reachability between SLL frames. *)
  Definition frame_multistep (g : grammar) :
    sll_frame -> sll_frame -> Prop :=
    clos_trans (frame_step g).

  Hint Constructors clos_trans : core.

  (** Every edge in the list is a valid multi-step frame transition. *)
  Definition mstep_edges_sound (g : grammar) (es : list edge) :=
    forall x y, In (x, y) es -> frame_multistep g x y.

  (** Any sound single-step edge list is also a sound multi-step edge list, since steps compose. *)
  Lemma step_edges_sound__mstep_edges_sound :
    forall g es,
      step_edges_sound g es -> mstep_edges_sound g es.
  Proof.
    intros g es hs s d hi; apply t_step; auto.
  Qed.

  (** Every multi-step frame transition is represented in the list. *)
  Definition mstep_edges_complete (g : grammar) (es : list edge) :=
    forall x y, frame_multistep g x y -> In (x, y) es.

  (** An edge list is correct if it is both sound and complete w.r.t. multi-step reachability. *)
  Definition mstep_edges_correct (g : grammar) (es : list edge) :=
    mstep_edges_sound g es /\ mstep_edges_complete g es.

  (** Computes initial-push edges for nonterminal x: one edge per production of x from the initial frame. *)
  Definition initial_push_edges' (ps : list production) (x : nonterminal) : list edge :=
    map (fun rhs => (sll_fr None [NT x], sll_fr (Some x) rhs))
        (rhss_for' ps x).

  (** Every edge produced by initial_push_edges' is a valid frame_step. *)
  Lemma initial_push_edges'_sound :
    forall g s d x,
      In (s, d) (initial_push_edges' (productions g) x)
      -> frame_step g s d.
  Proof.
    intros g s d x hi.
    apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; inv heq.
    eapply rhss_for'_in_iff in hi.
    apply in_productions_iff in hi; auto.
  Qed.

  (** For every production (x, rhs) in g, the corresponding initial-push edge is in the list. *)
  Lemma initial_push_edges'_complete :
    forall g x rhs,
      PM.In (x, rhs) g
      -> In (sll_fr None [NT x], sll_fr (Some x) rhs)
            (initial_push_edges' (productions g) x).
  Proof.
    intros g x rhs hi.
    apply in_map_iff; eexists; split; eauto.
    apply rhss_for'_in_iff.
    apply in_productions_iff; auto.
  Qed.

  (** Collects all initial-push edges for every nonterminal defined in the grammar. *)
  Definition initial_push_edges (ps : list production) : list edge :=
    flat_map (initial_push_edges' ps) (lhss' ps).

  (** Every edge in initial_push_edges is a valid frame_step in g. *)
  Lemma initial_push_edges_sound :
    forall g s d,
      In (s, d) (initial_push_edges (productions g))
      -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [x [hi hi']].
    eapply initial_push_edges'_sound; eauto.
  Qed.

  (** Every Fstep_initial_push transition is captured by initial_push_edges. *)
  Lemma initial_push_edges_complete :
    forall g x rhs,
      PM.In (x, rhs) g
      -> In (sll_fr None [NT x], sll_fr (Some x) rhs) (initial_push_edges (productions g)).
  Proof.
    intros g x rhs hi.
    apply in_flat_map; exists x; split.
    - apply in_productions_iff in hi.
      eapply production_lhs_in_lhss'; eauto.
    - eapply initial_push_edges'_complete; eauto.
  Qed.
  
  (** Computes noninitial push edges arising from NT occurrences in the rhs suffix ys of production (x, _). *)
  Fixpoint push_edges' (ps : list production) (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with 
    | []          => []
    | T _ :: ys'  => push_edges' ps x ys'
    | NT y :: ys' =>
      let es := map (fun rhs => (sll_fr (Some x) ys, sll_fr (Some y) rhs))
                    (rhss_for' ps y)
      in  es ++ push_edges' ps x ys'
    end.

  (** Every edge produced by push_edges' is a valid Fstep_noninitial_push transition. *)
  Lemma push_edges'_sound :
    forall g s d x suf pre,
      PM.In (x, pre ++ suf) g
      -> In (s, d) (push_edges' (productions g) x suf)
      -> frame_step g s d.
  Proof.
    intros g s d x suf. 
    induction suf as [| [a|y] suf IH]; sis; intros pre hi' hi; rew_anr.
    - inv hi.
    - apply IH with (pre := pre ++ [T a]); apps.
    - apply in_app_or in hi; destruct hi as [hi | hi].
      + apply in_map_iff in hi; destruct hi as [rhs [heq hi]].
        inv heq.
        apply rhss_for'_in_iff in hi.
        apply in_productions_iff in hi; eauto.
      + apply IH with (pre := pre ++ [NT y]); apps.
  Qed.

  (** Every Fstep_noninitial_push transition appears in the output of push_edges'. *)
  Lemma push_edges'_complete :
    forall g x y rhs pre suf rhs',
      rhs = pre ++ NT y :: suf
      -> PM.In (y, rhs') g
      -> In (sll_fr (Some x) (NT y :: suf), sll_fr (Some y) rhs')
            (push_edges' (productions g) x rhs).
  Proof.
    intros g x y rhs; induction rhs as [| [a | y'] suf' IH]; intros pre suf rhs' heq hi; sis.
    - apply app_cons_not_nil in heq; inv heq.
    - destruct pre; sis; inv heq; eauto.
    - destruct pre; sis; inv heq; apply in_or_app; eauto.
      left; apply in_map_iff; eexists; split; eauto.
      apply rhss_for'_in_iff. 
      apply in_productions_iff; auto.
  Qed.

  (** Collects all noninitial push edges across every production in the grammar. *)
  Definition push_edges (ps : list production) : list edge :=
    flat_map (fun p => push_edges' ps (lhs' p) (rhs' p)) ps.

  (** Every edge in push_edges is a valid frame_step in g. *)
  Lemma push_edges_sound :
    forall g s d,
      In (s, d) (push_edges (productions g))
      -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [(x, ys) [hi hi']]; sis.
    apply in_productions_iff in hi.
    eapply push_edges'_sound with (pre := []); eauto.
  Qed.

  (** Every Fstep_noninitial_push transition in g appears in push_edges. *)
  Lemma push_edges_complete :
    forall g x y pre suf rhs,
      PM.In (x, pre ++ NT y :: suf) g
      -> PM.In (y, rhs) g
      -> In (sll_fr (Some x) (NT y :: suf), sll_fr (Some y) rhs)
            (push_edges (productions g)).
  Proof.
    intros g x y pre suf rhs hi hi'.
    apply in_productions_iff in hi.
    apply in_flat_map; exists (x, pre ++ NT y :: suf); split; auto; sis.
    eapply push_edges'_complete; eauto.
  Qed.
  
  (** Computes return edges for each NT occurrence in rhs ys of production (x, _): when y completes, return to x's suffix. *)
  Fixpoint return_edges' (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with
    | []          => []
    | T _ :: ys'  => return_edges' x ys'
    | NT y :: ys' =>
      (sll_fr (Some y) [], sll_fr (Some x) ys') :: return_edges' x ys'
    end.

  (** Every edge produced by return_edges' is a valid Fstep_nonfinal_ret transition. *)
  Lemma return_edges'_sound :
    forall g s d x suf pre,
      PM.In (x, pre ++ suf) g
      -> In (s, d) (return_edges' x suf)
      -> frame_step g s d.
  Proof.
    intros g s d x suf. 
    induction suf as [| [a|y] suf IH]; sis; intros pre hi' hi; rew_anr.
    - inv hi.
    - apply IH with (pre := pre ++ [T a]); apps.
    - destruct hi as [hh | ht].
      + inv hh; eauto.
      + apply IH with (pre := pre ++ [NT y]); apps.
  Qed.
  
  (** Every Fstep_nonfinal_ret return transition appears in the output of return_edges'. *)
  Lemma return_edges'_complete :
    forall x y rhs pre suf,
      rhs = pre ++ NT y :: suf
      -> In (sll_fr (Some y) [], sll_fr (Some x) suf)
            (return_edges' x rhs).
  Proof.
    intros x y rhs; induction rhs as [| [a | y'] suf' IH]; intros pre suf heq; sis.
    - apply app_cons_not_nil in heq; inv heq.
    - destruct pre; sis; inv heq; eauto.
    - destruct pre; sis; inv heq; eauto.
  Qed.

  (** Collects all nonfinal return edges across every production in the grammar. *)
  Definition return_edges (ps : list production) : list edge :=
    flat_map (fun p => return_edges' (lhs' p) (rhs' p)) ps.

  (** Every edge in return_edges is a valid frame_step in g. *)
  Lemma return_edges_sound :
    forall g s d,
      In (s, d) (return_edges (productions g)) -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [(x, ys) [hi hi']]; sis.
    apply in_productions_iff in hi.
    eapply return_edges'_sound with (pre := []); eauto.
  Qed.

  (** Every Fstep_nonfinal_ret transition in g appears in return_edges. *)
  Lemma return_edges_complete :
    forall g x y pre suf,
      PM.In (x, pre ++ NT y :: suf) g
      -> In (sll_fr (Some y) [], sll_fr (Some x) suf) (return_edges (productions g)).
  Proof.
    intros g x y pre suf hi.
    apply in_productions_iff in hi.
    apply in_flat_map; eexists; split; eauto; sis.
    eapply return_edges'_complete; eauto.
  Qed.

  (** Computes the final return edges: every nonterminal's completed frame returns to the empty bottom frame. *)
  Definition final_return_edges (ps : list production) : list edge :=
    map (fun x => (sll_fr (Some x) [], sll_fr None [])) (lhss' ps).

  (** Every edge in final_return_edges is a valid Fstep_final_ret transition. *)
  Lemma final_return_edges_sound :
    forall g s d,
      In (s, d) (final_return_edges (productions g)) -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_map_iff in hi.
    destruct hi as [x [heq hi]]; inv heq.
    apply in_lhss'_exists_rhs in hi.
    destruct hi as [ys hi].
    apply in_productions_iff in hi; eauto.
  Qed.

  (** Every Fstep_final_ret transition in g appears in final_return_edges. *)
  Lemma final_return_edges_complete :
    forall g x ys,
      PM.In (x, ys) g
      -> In (sll_fr (Some x) [], sll_fr None []) (final_return_edges (productions g)).
  Proof.
    intros g x ys hi.
    apply in_map_iff; eexists; split; eauto.
    apply in_productions_iff in hi.
    eapply production_lhs_in_lhss'; eauto.
  Qed.
  
  (** The complete set of single-step frame transitions (all push, return, and final-return edges). *)
  Definition epsilon_edges (g : grammar) : list edge :=
    let ps := productions g
    in  initial_push_edges ps ++ push_edges ps ++ return_edges ps ++ final_return_edges ps.

  (** epsilon_edges is sound: every listed edge is a valid single-step frame transition. *)
  Lemma epsilon_edges__step_edges_sound :
    forall g,
      step_edges_sound g (epsilon_edges g).
  Proof.
    intros g s d hi; apply in_app_or in hi; destruct hi as [hi | hprf].
    - apply initial_push_edges_sound; auto. 
    - apply in_app_or in hprf; destruct hprf as [hp | hrf].
      + apply push_edges_sound ; auto.
      + apply in_app_or in hrf; destruct hrf as [hr | hf].
        * apply return_edges_sound      ; auto.
        * apply final_return_edges_sound ; auto.
  Qed.

  (** epsilon_edges is complete: every single-step frame transition in g appears in the list. *)
  Lemma epsilon_edges__step_edges_complete :
    forall g,
      step_edges_complete g (epsilon_edges g).
  Proof.
    intros g s d hs; unfold epsilon_edges; inv hs.
    - do 3 (apply in_or_app; right).
      eapply final_return_edges_complete; eauto.
    - do 2 (apply in_or_app; right); apply in_or_app; left.
      eapply return_edges_complete; eauto.
    - apply in_or_app; left.
      eapply initial_push_edges_complete; eauto.
    - apply in_or_app; right; apply in_or_app; left.
      eapply push_edges_complete; eauto.
  Qed.

  (* transitive closure operation *)

  (** Lifts a single edge into the graph representation expected by the transitive-closure library. *)
  Definition lift_edge (e : edge) : option (sll_frame * list sll_frame) :=
    match e with
    | (s, d) => Some (s, [d])
    end.

  (** Computes the transitive closure of an edge list, represented as a finite map from frames to successor sets. *)
  Definition trans_clos (es : list edge) : FM.t FS.t :=
    TC.trans_clos_list lift_edge es.

  (* soundness of transitive closure operation *)

  (** Soundness invariant for a closure map: every stored reachability fact corresponds to a frame_multistep. *)
  Definition tc_soundness_invar g cm :=
    forall s d, TC.G.rel cm s d -> frame_multistep g s d.

  (** List-based version of tc_soundness_invar, used during the fold over map elements. *)
  Definition tc_soundness_invar_list g prs :=
    forall s d ds, In (s, ds) prs -> FS.In d ds -> frame_multistep g s d.

  (** Dropping the head entry of a sound list preserves the soundness invariant for the tail. *)
  Lemma tc_soundness_invar_list_tail :
    forall g s ds prs,
      tc_soundness_invar_list g ((s, ds) :: prs)
      -> tc_soundness_invar_list g prs.
  Proof.
    intros g s ds prs hs; red; red in hs; intros; eapply hs; eauto.
    apply in_cons; auto.
  Qed.

  (** An element (s, ds) is in the list representation of a map iff the map lookup for s returns ds. *)
  Lemma in_elements_find_iff :
    forall s (ds : FS.t) cm,
      In (s, ds) (FM.elements cm)
      <-> FM.find s cm = Some ds.
  Proof.
    intros s ds cm; split; intros hi.
    - apply FMF.find_mapsto_iff.
      apply FMF.elements_mapsto_iff.
      apply In_InA; auto.
      (* lemma *)
      constructor.
      + repeat red; intros; auto.
      + repeat red; intros x y he; destruct he; auto.
      + repeat red. intros (a, b) (c, d) (e, f) he he'; sis.
        repeat red in he, he'; sis; destruct he; destruct he'; subst; auto.
    - apply FMF.find_mapsto_iff in hi.
      apply FM.elements_1 in hi.
      apply InA_alt in hi.
      destruct hi as [(s', ds') [he hi]].
      repeat red in he; sis; destruct he; subst; auto.
  Qed.

  (** The map-based and list-based soundness invariants are equivalent. *)
  Lemma invars_equiv :
    forall g cm,
      tc_soundness_invar g cm <-> tc_soundness_invar_list g (FM.elements cm).
  Proof.
    intros g cm; split; intros hs.
    - intros s d ds hi hi'.
      apply hs; eexists; split; eauto.
      apply in_elements_find_iff; auto.
    - intros s d hr.
      destruct hr as [ds [hf hi]].
      eapply hs; eauto.
      apply in_elements_find_iff; auto.
  Qed.
      
  (** Adding a sound edge to a sound map yields a sound map. *)
  Lemma add_edge_pres_soundness :
    forall g s d cm,
      frame_multistep g s d
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g (TC.G.add_edge s d cm).
  Proof.
    intros g s d cm hf hs.
    unfold TC.G.add_edge.
    red; intros s' d' hr; red in hr.
    destruct hr as [ds' [hfi hin]].
    destruct (SllFrAsUOT.eq_dec s' s) as [he | hn]; subst.
    - rewrite FMF.add_eq_o in hfi; auto; inv hfi.
      destruct (SllFrAsUOT.eq_dec d' d) as [he' | hn']; subst; auto.
      apply FS.add_3 in hin; auto.
      apply hs; apply TC.G.In_succs_rel; auto.
    - rewrite FMF.add_neq_o in hfi; auto.
      apply hs; red; eauto.
  Qed.

  (** Folding add_edge over a list of sound destinations preserves the soundness invariant. *)
  Lemma fold_add_edge_preserves_soundness :
    forall g s ds cm,
      (forall d, In d ds -> frame_multistep g s d)
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g
                            (fold_left
                               (fun a e =>
                                  TC.G.add_edge s e a)
                               ds cm).
  Proof.
    intros g s ds; induction ds as [| d ds IH]; intros cm ha hs; sis; auto.
    apply IH; auto.
    apply add_edge_pres_soundness; auto.
  Qed.

  (** Membership in the element list of a finite set is equivalent to FS.In membership. *)
  Lemma in_elements_iff_in_FS :
    forall fr s,
      In fr (FS.elements s) <-> FS.In fr s.
  Proof.
    intros fr s; split; intros hi.
    - eapply FSF.elements_iff.
      eapply In_InA; eauto.
    - eapply FSF.elements_iff in hi. 
      eapply InA_alt in hi; destruct hi as [fr' [heq hi]]; subst; auto.
  Qed.
  
  (** An element of FS.add y s is either y or was already in s. *)
  Lemma in_elements_add :
    forall x y zs,
      In x (FS.elements (FS.add y zs))
      -> x = y \/ In x (FS.elements zs).
  Proof.
    intros x y zs hi.
    apply in_elements_iff_in_FS in hi.
    apply FSF.add_iff in hi; destruct hi; auto.
    right; apply in_elements_iff_in_FS; auto.
  Qed.

  (** Adding a predecessor edge and its transitive successors to a sound map preserves soundness. *)
  Lemma add_pred_preserves_soundness :
    forall g cm cm' s s' d ds',
      frame_multistep g s d
      -> (forall d', FS.In d' ds' -> frame_multistep g s' d')
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g cm'
      -> tc_soundness_invar g
                            (TC.add_pred s (FS.add d (TC.G.succs d cm)) s' ds' cm').
  Proof.
    intros g cm cm' s s' d ds' hf ha hs hs'.
    unfold TC.add_pred; dmeq heq; auto.
    rewrite FS.fold_1; apply fold_add_edge_preserves_soundness; auto.
    intros d' hi.
    assert (hf' : frame_multistep g s' d).
    { eapply t_trans; eauto.
      apply ha; apply FSF.mem_iff; auto. }
    apply in_elements_add in hi; destruct hi as [? | hi]; subst; auto.
    eapply t_trans; eauto.
    apply hs; eauto.
    apply TC.G.In_succs_rel; auto.
    apply in_elements_iff_in_FS; auto.
  Qed.

  (** Folding add_pred over a list of predecessor map entries preserves the soundness invariant. *)
  Lemma fold_add_pred_preserves_tc_soundness_invar :
    forall g prs cm cm' s d,
      frame_multistep g s d
      -> tc_soundness_invar_list g prs
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g cm'
      -> tc_soundness_invar g
                            (fold_left
                               (fun a p =>
                                  TC.add_pred s (FS.add d (TC.G.succs d cm))
                                              (fst p) (snd p) a)
                               prs cm').
  Proof.
    intros g prs; induction prs as [| (s', ds') prs IH]; intros cm cm' s d hf hs hs' hs''; sis; auto.
    apply IH; auto.
    - eapply tc_soundness_invar_list_tail; eauto. 
    - eapply add_pred_preserves_soundness; eauto.
      intros d' hi; eapply hs; eauto.
      apply in_eq.
  Qed.
      
  (** Adding one edge together with all induced predecessor updates preserves the soundness invariant. *)
  Lemma trans_add_edge_preserves_tc_soundness_invar :
    forall g cm s d,
      frame_multistep g s d
      -> tc_soundness_invar g cm
    -> tc_soundness_invar g (TC.trans_add_edge s d cm).
  Proof.
    intros g cm s d hf hs.
    unfold TC.trans_add_edge; dm; auto.
    rewrite FM.fold_1.
    apply fold_add_pred_preserves_tc_soundness_invar; auto.
    - apply invars_equiv; auto.
    - (* lemma *)
      rewrite FS.fold_1; apply fold_add_edge_preserves_soundness; auto.
      intros d' hi; apply in_elements_add in hi.
      destruct hi as [? | hi]; subst; auto.
      apply t_trans with (y := d); auto.
      apply hs; apply TC.G.In_succs_rel; apply in_elements_iff_in_FS; auto.
  Qed.
  
  (** Processing an entire sound edge list via trans_add_edge preserves the soundness invariant. *)
  Lemma fold_trans_add_edge_preserves_tc_soundness_invar :
    forall g es cm,
      mstep_edges_sound g es
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g (fold_left (TC.trans_add_edge_list lift_edge) es cm).
  Proof.
    intros g es; induction es as [| (s, d) es IH]; intros cm hs hs'; sis; auto.
    apply IH; clear IH.
    - red; intros; apply hs; apply in_cons; auto.
    - unfold TC.trans_add_edge_list; unfold TC.trans_add_edge'; sis.
      apply trans_add_edge_preserves_tc_soundness_invar; auto.
      apply hs; apply in_eq.
  Qed.

  (** The transitive closure of all grammar epsilon edges is a sound reachability map. *)
  Lemma trans_clos_result_sound :
    forall g,
      tc_soundness_invar g (trans_clos (epsilon_edges g)).
  Proof.
    intros g; unfold trans_clos, TC.trans_clos_list.
    apply fold_trans_add_edge_preserves_tc_soundness_invar. 
    - apply step_edges_sound__mstep_edges_sound.
      apply epsilon_edges__step_edges_sound.
    - (* lemma : invariant starts true *)
      red. intros s d hr.
      red in hr.
      destruct hr as [ds [hf hi]].
      rewrite FMF.empty_o in hf; inv hf.
  Qed.

  (* completeness of transitive closure operation *)

  (** Every edge in es is represented as a reachability fact in the closure map cm. *)
  Definition closure_map_complete_wrt_edges cm es :=
    forall x y, In (x, y) es -> TC.G.rel cm x y.

  (** Existing reachability facts are preserved when a new edge is inserted into the graph. *)
  Lemma add_edge_preserves_old_edges :
    forall x x' y y' cm,
      TC.G.rel cm x y
      -> TC.G.rel (TC.G.add_edge x' y' cm) x y.
  Proof.
    intros x x' y y' cm hr; red; red in hr.
    destruct hr as [ys [hf hi]].
    unfold TC.G.add_edge.
    destruct (SllFrAsUOT.eq_dec x' x) as [he | hn]; subst.
    - destruct (SllFrAsUOT.eq_dec y' y) as [he' | hn']; subst.
      + eexists; split.
        * rewrite FMF.add_eq_o; auto.
        * apply FS.add_1; auto.
      + eexists; split.
        * rewrite FMF.add_eq_o; auto.
        * apply FS.add_2.
          unfold TC.G.succs; rewrite hf; auto.
    - eexists; split; eauto.
      rewrite FMF.add_neq_o; auto.
  Qed.

  (** Inserting edge (x, y) makes y a graph successor of x in the resulting map. *)
  Lemma add_edge_adds_edge :
    forall x y cm,
      TC.G.rel (TC.G.add_edge x y cm) x y.
  Proof.
    intros x y cm; red; unfold TC.G.add_edge.
    eexists; split.
    - rewrite FMF.add_eq_o; eauto.
    - apply FS.add_1; auto.
  Qed.

  (** Transitively adding edge (x, y) extends completeness from es to es ++ [(x, y)]. *)
  Lemma trans_add_edge_preserves_cm_complete_invar :
    forall cm es x y,
      closure_map_complete_wrt_edges cm es
      -> closure_map_complete_wrt_edges (TC.trans_add_edge x y cm) (es ++ [(x, y)]).
  Proof.
    intros cm es x y hc.
    red. intros x' y' hi.
    apply TC.add_edge_incl_trans.
    apply in_app_or in hi; destruct hi as [hi | hi].
    - apply hc in hi.
      apply add_edge_preserves_old_edges; auto.
    - apply in_singleton_eq in hi; inv hi.
      apply add_edge_adds_edge.
  Qed.
  
  (** Processing edge suffix suf preserves completeness for the already-processed prefix pre. *)
  Lemma fold_trans_add_edge_list_keeps_old_edges :
    forall suf pre cm,
      closure_map_complete_wrt_edges cm pre
      -> closure_map_complete_wrt_edges (fold_left (TC.trans_add_edge_list lift_edge) suf cm) (pre ++ suf).
  Proof.
    intros suf; induction suf as [| (x, y) suf IH]; intros pre cm hc; rew_anr; sis; auto.
    rewrite cons_app_singleton; rewrite app_assoc; apply IH.
    unfold TC.trans_add_edge_list; sis.
    unfold TC.trans_add_edge'.
    apply trans_add_edge_preserves_cm_complete_invar; auto.
  Qed.

  (** Every original edge is still a reachability fact in the transitive closure. *)
  Lemma trans_clos_holds_orig_edges :
    forall es x y,
      In (x, y) es
      -> TC.G.rel (trans_clos es) x y.
  Proof.
    intros es x y hi.
    unfold trans_clos, TC.trans_clos_list.
    apply fold_trans_add_edge_list_keeps_old_edges with (pre := []); auto.
    red; intros x' y' hc; inv hc.
  Qed.
  
  (** The transitive closure of epsilon edges is complete: every frame_multistep step is recorded. *)
  Lemma trans_clos_complete :
    forall g s d,
      frame_multistep g s d
      -> TC.G.rel (trans_clos (epsilon_edges g)) s d.
  Proof.
    intros g s d hf; induction hf.
    - apply trans_clos_holds_orig_edges.
      apply epsilon_edges__step_edges_complete; auto.
    - eapply TC.transitive_trans_clos_list; eauto.
  Qed.
  
  (* After performing the transitive closure,
     we keep only the "stable" edges *)

  (** Returns true iff the frame is stable (i.e., is the empty bottom frame or starts with a terminal). *)
  Definition stable (fr : sll_frame) : bool :=
    match fr with
    | sll_fr None []             => true
    | sll_fr _        (T _ :: _) => true
    | _                      => false
    end.

  (** The stable predicate is compatible with equality, enabling its use as a set filter. *)
  Lemma stable_compat_bool :
    compat_bool eq stable.
  Proof.
    repeat red; intros; subst; auto.
  Qed.

  (** A well-formed sll_stable_config stack implies the top frame satisfies the stable predicate. *)
  Lemma stable_config__stable_true :
    forall fr frs,
      sll_stable_config (fr, frs)
      -> stable fr = true.
  Proof.
    intros fr frs hs; inv hs; auto.
    sis; dm; tc.
  Qed.

  (** Filters a frame set to keep only stable frames, returning them as a list. *)
  Definition keep_stable_nodes (s : FS.t) : list sll_frame :=
    FS.elements (FS.filter stable s).

  (** Every frame returned by keep_stable_nodes satisfies the stable predicate. *)
  Lemma keep_stable_nodes_stable :
    forall fr frs,
      In fr (keep_stable_nodes frs)
      -> stable fr = true.
  Proof.
    intros fr frs hi.
    unfold keep_stable_nodes in hi.
    apply in_elements_iff_in_FS in hi.
    eapply FS.filter_2; eauto.
    apply stable_compat_bool.
  Qed.

  (* A closure graph is a map where each key K is a suffix frame 
     (i.e., grammar location), and each value V is a list of frames 
     that are epsilon-reachable from K *)
  (** A precomputed map from SLL frames to their stable epsilon-closure destinations. *)
  Definition closure_map := FM.t (list sll_frame).

  (** Filters the transitive closure graph to retain only edges reaching stable frames. *)
  Definition keep_stable_edges (g : TC.G.graph) : closure_map :=
    FM.map keep_stable_nodes g.

  (** Builds the closure map for a grammar: transitive closure of all epsilon edges, retaining only stable destinations. *)
  Definition mk_closure_map (g : grammar) : closure_map :=
    keep_stable_edges (trans_clos (epsilon_edges g)).

  (** Looks up the stable epsilon-closure destinations for a given frame in the closure map. *)
  Definition dest_frames (fr : sll_frame) (cm : closure_map) : list sll_frame :=
    match FM.find fr cm with
    | Some frs => frs
    | None     => []
    end.

  (* mk_closure_map spec and correctness proofs *)

  (** A closure map is sound if every stored destination is actually reachable and stable. *)
  Definition closure_map_sound g cm :=
    forall fr fr' frs',
      FM.MapsTo fr frs' cm
      -> In fr' frs'
      -> (frame_multistep g fr fr' /\ stable fr' = true).

  (** A closure map is complete if every reachable stable frame appears as a destination. *)
  Definition closure_map_complete g cm :=
    forall fr fr',
      frame_multistep g fr fr'
      -> stable fr' = true
      -> exists frs',
          FM.MapsTo fr frs' cm
          /\ In fr' frs'.

  (** A closure map is correct if it is both sound and complete. *)
  Definition closure_map_correct g cm :=
    closure_map_sound g cm /\ closure_map_complete g cm.
    
  (** The closure map built by mk_closure_map is sound: all stored destinations are genuinely reachable and stable. *)
  Lemma mk_closure_map_sound :
    forall g,
      closure_map_sound g (mk_closure_map g).
  Proof.
    intros g s d ds hm hi; unfold mk_closure_map in hm.
    split.
    - (* lemma about keep_stable_edges *)
      assert (hex : exists ds',
                 FM.MapsTo s ds' (trans_clos (epsilon_edges g))
                 /\ FS.In d ds').
      { apply FMF.map_mapsto_iff in hm.
        destruct hm as [ds' [? hm]]; subst; eauto.
        eexists; split; eauto.
        unfold keep_stable_nodes in hi.
        eapply in_elements_iff_in_FS in hi.
        apply FSF.filter_iff in hi.
        - destruct hi; auto.
        - repeat red; intros; subst; auto. }
      destruct hex as [ds' [hm' hi']].
      apply FMF.find_mapsto_iff in hm'.
      apply trans_clos_result_sound; red; eauto.
    - apply FMF.map_mapsto_iff in hm.
      destruct hm as [ds' [he hm]]; subst.
      eapply keep_stable_nodes_stable; eauto.
  Qed.

  (** The closure map built by mk_closure_map is complete: every reachable stable frame is stored. *)
  Lemma mk_closure_map_complete :
    forall g,
      closure_map_complete g (mk_closure_map g).
  Proof.
    intros g s d hf hs.
    unfold mk_closure_map.
    apply trans_clos_complete in hf.
    red in hf.
    destruct hf as [ds [hf hi]].
    exists (FS.elements (FS.filter stable ds)); split.
    - apply FMF.map_mapsto_iff.
      exists ds; split; auto.
      apply FMF.find_mapsto_iff; auto.
    - apply in_elements_iff_in_FS.
      apply FS.filter_3; auto.
      apply stable_compat_bool.
  Qed.
    
  (** mk_closure_map produces a correct closure map for any grammar. *)
  Theorem mk_closure_map_correct :
    forall g,
      closure_map_correct g (mk_closure_map g).
  Proof.
    intros g; split.
    - apply mk_closure_map_sound.
    - apply mk_closure_map_complete.
  Qed.
  
End GrammarAnalysisFn.
