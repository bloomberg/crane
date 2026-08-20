(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Arith Bool List.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import Parser.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Termination.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module ParserSoundFn (Import D : Defs.T).

  Module Export P := ParserFn D.
  
  (* To do : maybe this can go somewhere else, like error-free termination *)
  (** A [step_k] result preserves the well-formedness of the parser stack with respect to the grammar. *)
  Lemma step_preserves_stack_wf_invar :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      rhs_map_correct rm gr
      -> stack_wf gr sk
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> stack_wf gr sk'.
  Proof.
    intros gr hg rm cm (fr, frs) (fr', frs') ts ts' vi vi'
           un un' ca ca' hc hk hp hw hs; red; red in hw.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_frames_wf_invar; eauto.
    - eapply consume_preserves_frames_wf_invar; eauto. 
    - eapply push_preserves_frames_wf_invar; eauto.
      eapply adaptive_predict_succ_in_grammar; eauto.
    - eapply push_preserves_frames_wf_invar; eauto.
      eapply adaptive_predict_ambig_in_grammar; eauto.
  Qed.

  (** A [step_k] result leaves the bottom-frame symbols unchanged, so the start nonterminal is always reflected at the stack base. *)
  Lemma step_preserves_bottom_frame_syms_invar :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      stack_wf gr sk
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> bottom_frame_syms sk = bottom_frame_syms sk'.
  Proof.
    intros gr hg rm cm (fr, frs) (fr', frs') ts ts' vi vi' un un' ca ca' hc hk hw hs.
    unfold step in hs; dms; inv hs; tc;
      unfold bottom_frame_syms; apps; inv_fwf hw hi hw'; inv hw'; sis; auto.
  Qed.

  (* The stronger parser soundness theorems -- one for unique derivations, one for
   ambiguous derivations, appear below. *)

  (** Relates a frame list to the tokens it has consumed ([wpre]) and those yet to be consumed ([wsuf]), encoding the partial derivation carried by the stack. *)
  Inductive frames_derivation (gr : grammar) :
    list parser_frame -> list token -> list token -> Prop :=
  | fd_nil :
      forall wsuf,
        frames_derivation gr [] [] wsuf
  | fd_bottom  :
      forall pre suf wpre wsuf vs,
        sem_values_derivation gr (rev pre) wpre (rev_tuple _ vs)
        -> frames_derivation gr [Fr pre vs suf] wpre wsuf
  | fd_upper :
      forall pre pre' vs vs' x suf suf' wpre wmid wsuf frs,
        sem_values_derivation gr (rev pre') wmid (rev_tuple _ vs')
        -> frames_derivation gr (                    Fr pre vs (NT x :: suf) :: frs) wpre (wmid ++ wsuf)
        -> frames_derivation gr (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs) (wpre ++ wmid) wsuf.

  Hint Constructors frames_derivation : core.

  Ltac inv_fd hf hf':=
    let hi  := fresh "hi"  in
    let hvs := fresh "hvs" in
    inversion hf as [ ?
                    | ? ? ? ? ? hvs
                    | ? ? ? ? ? ? ? ? ? ? ? hvs hf' ]; subst; clear hf.

  (** Inverts a [frames_derivation] for a non-empty frame list, splitting the consumed word into the part attributed to the tail frames and the part attributed to the head frame. *)
  Lemma fd_inv_cons :
    forall gr pre vs suf w wsuf frs,
      frames_derivation gr (Fr pre vs suf :: frs) w wsuf
      -> exists wpre wmid,
          w = wpre ++ wmid
          /\ sem_values_derivation gr (rev pre) wmid (rev_tuple _ vs)
          /\ frames_derivation gr frs wpre (wmid ++ wsuf).
  Proof.
    intros gr pre vs suf w wsuf frs hf.
    inv hf; ss_inj; eauto.
    exists []; eexists; repeat split; eauto.
  Qed.

  (** A return step (completing a callee frame and resuming the caller) preserves [frames_derivation]. *)
  Lemma return_preserves_frames_derivation :
    forall gr hw ce cr cr' frs pre pre' vs vs' x suf p f wpre wsuf,
      ce     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf
      -> find_predicate_and_action (x, rev pre') gr hw = Some (p, f)
      -> p (rev_tuple _ vs') = true
      -> frames_derivation gr (ce :: cr :: frs) wpre wsuf
      -> frames_derivation gr (cr'      :: frs) wpre wsuf.
  Proof.
    intros gr hw ce cr cr' frs pre pre' vs vs' x suf p f wpre wsuf ? ? ? hl hp hf; subst.
    apply fpaa_mapsto in hl.
    inv_fd hf hf'; repeat ss_inj.
    inv_fd hf' hf''; ss_inj.
    - constructor; sis.
      apply svd_app; auto.
      rew_nil_r wmid.
      constructor; eauto.
    - rewrite <- app_assoc.
      constructor; auto; sis; apps.
      apply svd_app; auto.
      rew_nil_r wmid.
      constructor; eauto.
  Qed.
  
  (** Consuming a terminal token and shifting it into the processed prefix preserves [frames_derivation]. *)
  Lemma consume_preserves_frames_derivation :
    forall gr fr fr' frs pre vs a v suf wpre wsuf,
      fr = Fr pre vs (T a :: suf)
      -> fr' = Fr (T a :: pre) (v, vs) suf
      -> frames_derivation gr (fr :: frs) wpre (@existT _ _ a v :: wsuf )
      -> frames_derivation gr (fr' :: frs) (wpre ++ [@existT _ _ a v]) wsuf.
  Proof.
    intros gr ? ? frs pre vs a v suf wpre wsuf ? ? hf; subst; inv hf; ss_inj.
    - constructor; sis.
      apply svd_app; auto.
      apply svd_app_nil_r_word.
      constructor; auto.
    - rewrite <- app_assoc; constructor; auto; sis; apps.
      apply svd_app; auto.
      apply svd_app_nil_r_word.
      constructor; auto.
  Qed.

  (** Pushing an empty callee frame for a nonterminal preserves [frames_derivation]. *)
  Lemma push_preserves_frames_derivation :
    forall gr cr ce pre vs x suf rhs frs wpre wsuf,
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> frames_derivation gr (      cr :: frs) wpre wsuf
      -> frames_derivation gr (ce :: cr :: frs) wpre wsuf.
  Proof.
    intros gr ? ? pre vs x suf rhs frs wpre wsuf ? ? hd; subst.
    rew_nil_r wpre; eauto.
  Qed.    

  (** The overall stack invariant: the full input [w] splits as [wpre ++ wsuf] where [wpre] is witnessed by [frames_derivation]. *)
  Definition stack_prefix_derivation gr w stk wsuf :=
    match stk with
    | (fr, frs) =>
      exists wpre,
      w = wpre ++ wsuf
      /\ frames_derivation gr (fr :: frs) wpre wsuf
    end.

  (** A [step_k] result preserves [stack_prefix_derivation], so the partial derivation grows correctly with each step. *)
  Lemma step_preserves_stack_prefix_derivation_invar :
    forall gr hw rm cm w sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      rhs_map_correct rm gr
      -> stack_prefix_derivation gr w sk ts
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> stack_prefix_derivation gr w sk' ts'.
  Proof.
    intros gr hw rm cm w (fr, frs) (fr', frs') ts ts' vi vi'
           un un' ca ca' hc hk hp hf hs; red; red in hf.
    destruct hf as (wpre & heq & hf); subst.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eexists; split; eauto.
      eapply return_preserves_frames_derivation; eauto.
      auto.
    - eexists; split.
      + rewrite cons_app_singleton; rewrite app_assoc; eauto.
      + eapply consume_preserves_frames_derivation; eauto.
    - eexists; split; eauto.
      eapply push_preserves_frames_derivation; eauto.
    - eexists; split; eauto.
      eapply push_preserves_frames_derivation; eauto.
  Qed.

  (** The initial stack satisfies [stack_prefix_derivation] with an empty consumed prefix. *)
  Lemma stack_prefix_derivation_start_true :
    forall gr w x,
      stack_prefix_derivation gr w (Fr [] tt [NT x], []) w.
  Proof.
    intros gr w x; red.
    exists []; split; auto.
  Qed.
    
  (* Invariant for proving the "unambiguous" version of the parser soundness
   lemma. The processed stack symbols and the semantic values stored
   in each frame comprise a unique partial derivation for the tokens that
   have been consumed. *)

  (** Strengthened frames-derivation invariant asserting that the partial derivation stored in each frame is the unique one compatible with the consumed tokens and the remaining stack. *)
  Inductive unique_frames_derivation (gr : grammar) :
    list parser_frame -> list token -> list token -> Prop :=
  | ufd_bottom :
      forall pre vs suf wpre wsuf,
        sem_values_derivation gr (rev pre) wpre (rev_tuple _ vs)
        -> (forall wpre' wsuf' pre' vs' (heq : rev pre' = rev pre),
               wpre' ++ wsuf' = wpre ++ wsuf
               -> sem_values_derivation gr (rev pre') wpre' (rev_tuple _ vs')
               -> stack_accepts_suffix gr (Fr pre' vs' suf, []) wsuf'
               -> wpre' = wpre /\ wsuf' = wsuf /\ cast_ss (rev pre') (rev pre) heq (rev_tuple _ vs') = rev_tuple _ vs)
        -> unique_frames_derivation gr [Fr pre vs suf] wpre wsuf
  | ufd_upper :
      forall cr ce frs pre pre' x suf suf' wpre wmid wsuf vs vs',
      Fr pre vs (NT x :: suf) = cr
      -> Fr pre' vs' suf'     = ce
      -> unique_frames_derivation gr (cr :: frs) wpre (wmid ++ wsuf)
      -> PM.In (x, rev pre' ++ suf') gr
      -> sem_values_derivation gr (rev pre') wmid (rev_tuple _ vs')
      -> (forall wmid' wsuf' pre'' vs'' (heq : rev pre'' = rev pre'),
             wmid' ++ wsuf' = wmid ++ wsuf
             -> sem_values_derivation gr (rev pre'') wmid' (rev_tuple _ vs'')
             -> stack_accepts_suffix gr (Fr pre'' vs'' suf', cr :: frs) wsuf'
             -> wmid' = wmid /\ wsuf' = wsuf /\ cast_ss (rev pre'') (rev pre') heq (rev_tuple _ vs'') = rev_tuple _ vs')
      -> (forall wmid' wsuf' pre'' suf'' vs'',
             wmid' ++ wsuf' = wmid ++ wsuf
             -> PM.In (x, rev pre'' ++ suf'') gr
             -> sem_values_derivation gr (rev pre'') wmid' (rev_tuple _ vs'')
             -> stack_accepts_suffix gr (Fr pre'' vs'' suf'', cr :: frs) wsuf'
             -> rev pre'' ++ suf'' = rev pre' ++ suf')
      -> unique_frames_derivation gr (ce :: cr :: frs) (wpre ++ wmid) wsuf.
  
  Hint Constructors unique_frames_derivation : core.
  
  Ltac inv_ufd hu  hv ha hu' hi hvs hpu :=
    inversion hu as [ ? ? ? ? ? hvs ha
                    | ? ? ? ? ? ? ? ? ? ? ? ? ? heq heq' hu' hi hvs ha hpu]; subst; clear hu.

  Ltac t :=
    match goal with
    | |- lower_frames_accept_suffix _ _ (concat_tuple _ _ _ ((cast_action _ _ _ _) _, _)) _ _ =>
      eapply lfas_replace_head; eauto
    | |- concat_tuple ?xs ?ys ?vx ?vy = cast_ss (?xs' ++ ?ys) (?xs ++ ?ys) ?pf (concat_tuple ?xs' ?ys ?vx' ?vy') =>
      eapply concat_tuple_eq with (heq := app_inv_tail  _ _ _ pf)
    | |- concat_tuple ?pre (?s :: ?suf) _ _ = cast_ss _ _ _ (concat_tuple ?pre' ([?s] ++ ?suf) _ _) =>
      eapply concat_tuple_eq
    | |- context[cast_ss ?xs ?xs _ _] =>
      rewrite cast_ss_refl
    | |- (?a, ?b) = (?a', ?b') =>
      apply pair_split_eq
    | |- ?f ?vs = (cast_action _ _ _ ?f) ?vs' =>
      eapply cast_action_eq
    | |- context[concat_tuple (rev (rev ?xs)) []] =>
      erewrite rrt_anr
    | |- (cast_predicate _ _ _ _) _ = true =>
      eapply cast_predicate_eq_true; eauto
    | |- context[concat_tuple (_ ++ [_]) _ (concat_tuple _ [_] _ _) _] => erewrite concat_tuple_assoc'
    | |- context[cast_ss _ _ _ (cast_ss _ _ _ _)] =>
      erewrite <- cast_ss_ins_trans
    | |- context[rev_tuple _ (rev_tuple _ _)] =>
      erewrite rev_tuple_involutive
    | |- PM.MapsTo _ (@existT _ _ _ (cast_predicate _ _ _ _, cast_action _ _ _ _)) _ =>
      eapply mapsto_cast; eauto
    end.

  Ltac t' := repeat t.
  
  (** A return step preserves [unique_frames_derivation]: the uniqueness condition is maintained when folding a completed callee into its caller. *)
  Lemma return_preserves_unique_frames_derivation :
    forall gr hw ce cr cr' frs pre pre' vs vs' x suf p f wpre wsuf,
      ce     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf
      -> find_predicate_and_action (x, rev pre') gr hw = Some (p, f)
      -> p (rev_tuple _ vs') = true
      -> unique_frames_derivation gr (ce :: cr :: frs) wpre wsuf
      -> unique_frames_derivation gr (cr'      :: frs) wpre wsuf.
  Proof.
    intros gr hw ? ? ? frs pre pre' vs vs' x suf p f wpre wsuf ? ? ? hf hp hu; subst.
    inv_ufd hu  hv ha hu' hi hvs hpu;
      inv heq; inv heq'; repeat ss_inj; rew_anr.
    apply fpaa_mapsto in hf.
    inv_ufd hu'  hv' ha' hu'' hi' hvs' hpu'; sis; rew_anr; repeat ss_inj.
    - (* return to initial frame *)
      apply ufd_bottom; sis.
      + apply svd_app; auto.
        rew_nil_r wmid.
        econstructor; eauto.
      + intros wpre' wsuf' pre'' v'' h heq hd hr; subst; sis.
        destruct pre''; try (pose proof h as h'; apply app_cons_not_nil in h'; destruct h').
        sis.
        pose proof h as h'.
        eapply rev_heads_eq_tails_eq__lists_eq
          with (xs := rev pre'') (x := s) (ys := rev pre) (y := NT x) in h'.
        destruct h'; subst.
        apply svd_split in hd.
        destruct hd as (w & w' & v''' & v'''' & ? & heq' & hd & hd'); subst.
        repeat rewrite <- app_assoc in heq.
        apply svd_singleton_nt in hd'.
        destruct hd' as (v & ys & sts & p' & f' & ? & hi' & hd' & ? & ?); subst.
        assert (H' : rev (rev (rev pre'')) = rev pre).
        { rewrite rev_involutive; auto. }
        eapply ha' with (vs' := rev_tuple _ v''')
                        (heq := H') in heq; 
          try rewrite rev_involutive in *; subst; eauto.
        * destruct heq as (? & heq & ?); subst.
          assert (ys = rev pre').
          { rewrite <- heq in hpu.
            pose proof hi' as hm.
            apply pm_mapsto_in in hi'.
            assert (ys = rev (rev ys) ++ []).
            { rewrite rev_involutive.
              apps. }
            rewrite H in hi'.
            eapply hpu with (vs'' := rev_tuple _ sts) in hi'; eauto.
            - rewrite rev_involutive in hi'.
              rew_anr; auto.
            - rew_anr.
              rewrite rev_tuple_involutive with (heq := H).
              eapply svd_eq with (vs := sts) (heq := H); eauto.
            - destruct hr as [w1 [w2 [vs_suf [? [hd'' ?]]]]]; subst.
              exists []; exists w1; exists tt.
              rewrite app_nil_r; sis.
              repeat split; auto.
              exists w1; exists []; exists vs_suf.
              assert ((x, ys) = (x, rev (rev ys) ++ [])).
              { rewrite <- H; auto. }
              exists (cast_predicate (x, ys) (x, rev (rev ys) ++ []) H3 p').
              exists (cast_action (x, ys) (x, rev (rev ys) ++ []) H3 f').
              rewrite app_nil_r; repeat split; auto.
              + eapply mapsto_cast; eauto.
              + erewrite predicate_appl_eq_cast
                  with (heq := H3) (heq' := H) in H1.
                rewrite <- H1.
                f_equal.
                assert (anr' : forall A (xs : list A),
                           xs = xs ++ []).
                { intros. rewrite app_nil_r; auto. }
                assert (foo : forall (xs : list symbol)
                                   (vs : symbols_semty xs),
                           concat_tuple xs [] vs tt =
                           cast_ss xs (xs ++ []) (anr' _ xs) vs).
                { intros xs vs0.
                  apply concat_tuple_nil_r. }
                rewrite foo.
                assert (ri' : forall A (xs : list A),
                           xs = rev (rev xs)).
                { intros. rewrite rev_involutive. auto. }
                assert (bar : forall xs vs,
                           rev_tuple (rev xs) (rev_tuple xs vs) =
                           cast_ss xs (rev (rev xs)) (ri' _ xs) vs).
                { intros.
                  apply rev_tuple_involutive. }
                rewrite bar.
                assert (baz : forall xs ys zs vs
                                     (heq : xs = ys)
                                     (heq' : ys = zs)
                                     (heq'' : xs = zs),
                           cast_ss ys zs heq' (cast_ss xs ys heq vs) = cast_ss xs zs heq'' vs).
                { intros a b c v ? ? ?; subst.
                  unfold cast_ss.
                  unfold eq_rect_r.
                  repeat rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
                  apply GammaAsUOT.eq_dec.
                  apply GammaAsUOT.eq_dec. }
                apply baz.
          }
          subst.
          assert (foo : rev (rev (rev pre')) = rev pre').
          { rewrite rev_involutive; auto. }
          eapply ha with (vs'' := rev_tuple _ sts)
                         (heq  := foo) in heq; 
            try rewrite rev_involutive in *; eauto.
          -- destruct heq as (? & ? & ?); subst; auto.
             repeat split; auto.
             unfold rev_tuple_cons_case.
             unfold eq_rect_r.
             repeat rewrite <- Eqdep_dec.eq_rect_eq_dec;
               try apply GammaAsUOT.eq_dec.
             destruct v''.
             symmetry.
             assert (bar : f' = f).
             { eapply PMF.MapsTo_fun in hf; eauto.
               apply Eqdep_dec.inj_pair2_eq_dec in hf.
               - inv hf; auto.
               - apply ProductionAsUOT.eq_dec. }
             subst.
             unfold rev_tuple_cons_case in heq'.
             unfold eq_rect_r in heq'; sis.
             rewrite heq'.
             assert (rev_tuple pre' vs' = sts).
             { rewrite <- H4.
               pose proof foo as foo'.
               symmetry in foo'.
               rewrite rev_tuple_involutive with (heq := foo').
               rewrite cast_ss_roundtrip; auto. }
             rewrite H.
             assert (bar : forall xs ys zs vs vs' vs''
                                  (heq : ys ++ zs = xs ++ zs)
                                  (heq' : ys = xs),
                        vs = (cast_ss ys xs heq' vs')
                        -> concat_tuple xs zs vs vs'' =
                           cast_ss (ys ++ zs) (xs ++ zs) heq (concat_tuple ys zs vs' vs'')).
             { intros xs ys zs v1 v2 v3 ? ? ?; subst.
               repeat rewrite cast_ss_refl; auto. }
             pose proof H' as H''.
             rewrite rev_involutive in H''.
             eapply bar with (heq' := H'').
             clear ha. clear ha'. clear hpu.
             assert (rev pre'' = rev (rev (rev pre''))).
             { rewrite rev_involutive; auto. }
             erewrite cast_ss_ins_trans with
                 (ys := rev (rev (rev pre'')))
                 (heq := H'')
                 (heq' := H')
                 (heq'' := H3).
             rewrite <- H2.
             erewrite rev_tuple_involutive; eauto.
          -- assert (rev pre' = rev (rev (rev pre'))).
             { rewrite rev_involutive; auto. }
             rewrite rev_tuple_involutive with (heq := H).
             eapply svd_eq; eauto. 
          -- exists []; exists wsuf'; exists tt.
             repeat split; auto.
             destruct hr as [w1 [w2 [vs_suf [? [? ?]]]]]; subst.
             exists w1; exists []; exists vs_suf.
             assert (foo' : (x, rev pre') = (x, rev (rev (rev pre')) ++ [])).
             { rewrite rev_involutive. apps. }
             exists (cast_predicate (x, rev pre') (x, rev (rev (rev pre')) ++ []) foo' p').
             exists (cast_action (x, rev pre') (x, rev (rev (rev pre')) ++ []) foo' f').
             repeat split; auto.
             ++ eapply mapsto_cast with (heq' := foo') in hi'; eauto. 
             ++ pose proof foo' as foo''.
                symmetry in foo''.
                assert (bar : rev (rev (rev pre')) ++ [] = rev pre').
                { rewrite rev_involutive.
                  apps. }
                erewrite predicate_appl_eq_cast with (ys' := rev pre') (heq := foo'') (heq' := bar).
                assert (bar' : rev pre' = rev (rev (rev pre'))).
                { rewrite rev_involutive; auto. }
                rewrite rev_tuple_involutive with (heq := bar').
                assert (rev (rev (rev pre')) = rev (rev (rev pre')) ++ []).
                { rewrite app_nil_r; auto. }
                rewrite concat_tuple_nil_r with (heq := H).
                assert (bar'' : rev (rev (rev pre')) = rev pre').
                { rewrite <- bar'; auto. }
                rewrite <- cast_ss_ins_trans with (heq := bar'').
                rewrite cast_ss_roundtrip.
                rewrite <- cast_predicate_ins_trans with (heq := eq_refl).
                rewrite cast_predicate_refl; auto.
        * assert (rev pre'' = rev (rev (rev pre''))).
          { rewrite rev_involutive; auto. }
          rewrite rev_tuple_involutive with (heq := H).
          eapply svd_eq; eauto.
        * destruct hr as [w1 [w2 [vs_suf [? [? ?]]]]]; subst.
          exists (w' ++ w1); exists []; exists (f' sts, vs_suf).
          repeat split.
          -- apps.
          -- constructor; auto.
             econstructor; eauto.
    - inv heq'; ss_inj.
      rewrite <- app_assoc.
      eapply ufd_upper with (pre' := NT x :: pre); eauto; sis; apps.
      + apply svd_app; auto.
        rew_nil_r wmid.
        econstructor; eauto.
      + intros wpre' wsuf' pre'' v'' h heq hd hr; subst; sis.
        destruct pre''; try (pose proof h as h'; apply app_cons_not_nil in h'; destruct h').
        sis.
        pose proof h as h'.
        eapply rev_heads_eq_tails_eq__lists_eq
          with (xs := rev pre'') (x := s) (ys := rev pre) (y := NT x) in h'.
        destruct h'; subst.
        apply svd_split in hd.
        destruct hd as (w & w' & v''' & v'''' & ? & heq' & hd & hd'); subst.
        repeat rewrite <- app_assoc in heq.
        apply svd_singleton_nt in hd'.
        destruct hd' as (v & ys & sts & p' & f' & ? & hi'' & hd' & ? & ?); subst.
        assert (H' : rev (rev (rev pre'')) = rev pre).
        { rewrite rev_involutive; auto. }
        eapply ha' with (vs'' := rev_tuple _ v''')
                        (heq := H') in heq; 
          try rewrite rev_involutive in *; subst; eauto.
        * destruct heq as (? & heq & ?); subst.
          assert (ys = rev pre').
          { rewrite <- heq in hpu.
            pose proof hi'' as hm.
            apply pm_mapsto_in in hi''.
            assert (ys = rev (rev ys) ++ []).
            { rewrite rev_involutive.
              apps. }
            rewrite H in hi''.
            eapply hpu with (vs'' := rev_tuple _ sts) in hi''; eauto.
            - rewrite rev_involutive in hi''.
              rew_anr; auto.
            - rew_anr.
              rewrite rev_tuple_involutive with (heq := H).
              eapply svd_eq with (vs := sts) (heq := H); eauto.
            - destruct hr as [w1 [w2 [vs_suf [? [hd'' ?]]]]]; subst.
              exists []; exists (w1 ++ w2); exists tt; sis.
              repeat split; auto.
              exists w1; exists w2; exists vs_suf.
              assert ((x, ys) = (x, rev (rev ys) ++ [])).
              { rewrite <- H; auto. }
              exists (cast_predicate (x, ys) (x, rev (rev ys) ++ []) H3 p').
              exists (cast_action (x, ys) (x, rev (rev ys) ++ []) H3 f').
              repeat split; auto.
              + eapply mapsto_cast; eauto.
              + erewrite predicate_appl_eq_cast
                  with (heq := H3) (heq' := H) in H1.
                rewrite <- H1.
                f_equal.
                assert (anr' : forall A (xs : list A),
                           xs = xs ++ []).
                { intros. rewrite app_nil_r; auto. }
                assert (foo : forall (xs : list symbol)
                                   (vs : symbols_semty xs),
                           concat_tuple xs [] vs tt =
                           cast_ss xs (xs ++ []) (anr' _ xs) vs).
                { intros xs vs1.
                  apply concat_tuple_nil_r. }
                rewrite foo.
                assert (ri' : forall A (xs : list A),
                           xs = rev (rev xs)).
                { intros. rewrite rev_involutive. auto. }
                assert (bar : forall xs vs,
                           rev_tuple (rev xs) (rev_tuple xs vs) =
                           cast_ss xs (rev (rev xs)) (ri' _ xs) vs).
                { intros.
                  apply rev_tuple_involutive. }
                rewrite bar.
                assert (baz : forall xs ys zs vs
                                     (heq : xs = ys)
                                     (heq' : ys = zs)
                                     (heq'' : xs = zs),
                           cast_ss ys zs heq' (cast_ss xs ys heq vs) = cast_ss xs zs heq'' vs).
                { intros a b c v ? ? ?; subst.
                  unfold cast_ss.
                  unfold eq_rect_r.
                  repeat rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
                  apply GammaAsUOT.eq_dec.
                  apply GammaAsUOT.eq_dec. }
                apply baz.
              + destruct H4 as [w3 [w4 [vs_suf' [p'' [f'' [? [hd''' [hm'' [hp'' ?]]]]]]]]]; subst.
                exists w3; exists w4; exists vs_suf'.
                assert (qux : (x0, (rev pre'' ++ [NT x]) ++ suf) =
                              (x0, rev pre ++ NT x :: suf)).
                { rewrite <- app_assoc.
                  rewrite H0; sis; auto. }
                exists (cast_predicate _ _ qux p'').
                exists (cast_action _ _ qux f'').
                repeat split; auto.
                * eapply mapsto_cast with (heq' := qux) in hm''; eauto.
                * assert (b : (rev pre'' ++ [NT x]) ++ suf =
                              rev pre ++ NT x :: suf).
                  { inv qux; auto. }
                  eapply cast_predicate_eq_true with (heq := b); eauto.
                  rewrite heq'.
                  assert (c : rev pre'' ++ [NT x] ++ suf = (rev pre'' ++ [NT x]) ++ suf) by apps.
                  rewrite concat_tuple_assoc' with (heq := c); sis.
                  assert (d : rev pre'' ++ NT x :: suf =
                              rev pre   ++ NT x :: suf).
                  { rewrite H0; auto. }
                  rewrite <- cast_ss_ins_trans with (heq := d).
                  unfold concat_tuple_rec_case.
                  unfold eq_rect_r; sis.
                  unfold concat_tuple_nil_case.
                  unfold eq_rect_r; sis.
                  eapply concat_tuple_eq with (heq := H0) (heq' := eq_refl).
                  -- rewrite <- H2.
                     rewrite rev_tuple_involutive with (heq := rr_expand _ _).
                     erewrite <- cast_ss_ins_trans; eauto.
                  -- apply pair_split_eq; auto.
                     symmetry.
                     eapply cast_action_eq with (heq := H).
                     erewrite rrt_anr; eauto.
                * eapply lfas_replace_head; eauto.
                  clear H5.
                  clear hpu.
                  clear ha ha'.
                  assert (qux' : (rev pre'' ++ [NT x]) ++ suf =
                                 rev pre ++ NT x :: suf).
                  { inv qux; auto. }
                  apply cast_action_eq with (heq := qux').
                  rewrite heq'.
                  assert (b : rev pre'' ++ [NT x] ++ suf =
                              (rev pre'' ++ [NT x]) ++ suf) by apps.
                  rewrite concat_tuple_assoc' with (heq := b).
                  assert (c : rev pre'' ++ [NT x] ++ suf =
                              rev pre ++ NT x :: suf) by apps.
                  rewrite <- cast_ss_ins_trans with (heq := c); sis.
                  unfold concat_tuple_rec_case.
                  unfold eq_rect_r; sis.
                  unfold concat_tuple_nil_case.
                  unfold eq_rect_r; sis.
                  apply concat_tuple_eq with
                      (heq := H0)
                      (heq' := eq_refl).
                  -- rewrite <- H2.
                     rewrite rev_tuple_involutive with (heq := rr_expand _ _).
                     erewrite <- cast_ss_ins_trans; eauto.
                  -- rewrite cast_ss_refl.
                     symmetry.
                     rewrite rrt_anr with (heq := rr_anr_expand _ _).
                     apply pair_split_eq; auto.
                     apply cast_action_eq with (heq := rr_anr_expand _ _).
                     auto.
          }
          subst.
          assert (foo : rev (rev (rev pre')) = rev pre').
          { rewrite rev_involutive; auto. }
          eapply ha with (vs'' := rev_tuple _ sts)
                         (heq  := foo) in heq; 
            try rewrite rev_involutive in *; eauto.
          -- destruct heq as (? & ? & ?); subst; auto.
             repeat split; auto.
             unfold rev_tuple_cons_case.
             unfold eq_rect_r.
             repeat rewrite <- Eqdep_dec.eq_rect_eq_dec;
               try apply GammaAsUOT.eq_dec.
             destruct v''.
             symmetry.
             assert (bar : f' = f).
             { eapply PMF.MapsTo_fun in hf; eauto.
               apply Eqdep_dec.inj_pair2_eq_dec in hf.
               - inv hf; auto.
               - apply ProductionAsUOT.eq_dec. }
             subst.
             unfold rev_tuple_cons_case in heq'.
             unfold eq_rect_r in heq'; sis.
             rewrite heq'.
             assert (f (rev_tuple pre' vs') = f sts).
             { rewrite <- H4.
               pose proof foo as foo'.
               symmetry in foo'.
               rewrite rev_tuple_involutive with (heq := foo').
               rewrite cast_ss_roundtrip; auto. }
             rewrite H.
             assert (bar : forall xs ys zs vs vs' vs''
                                  (heq : ys ++ zs = xs ++ zs)
                                  (heq' : ys = xs),
                        vs = (cast_ss ys xs heq' vs')
                        -> concat_tuple xs zs vs vs'' =
                           cast_ss (ys ++ zs) (xs ++ zs) heq (concat_tuple ys zs vs' vs'')).
             { intros xs ys zs v1 v2 v3 ? ? ?; subst.
               repeat rewrite cast_ss_refl; auto. }
             pose proof H' as H''.
             rewrite rev_involutive in H''.
             eapply bar with (heq' := H'').
             clear ha. clear ha'. clear hpu.
             assert (rev pre'' = rev (rev (rev pre''))).
             { rewrite rev_involutive; auto. }
             erewrite cast_ss_ins_trans with
                 (ys := rev (rev (rev pre'')))
                 (heq := H'')
                 (heq' := H')
                 (heq'' := H3).
             rewrite <- H2.
             erewrite rev_tuple_involutive; eauto.
          -- assert (rev pre' = rev (rev (rev pre'))).
             { rewrite rev_involutive; auto. }
             rewrite rev_tuple_involutive with (heq := H).
             eapply svd_eq; eauto. 
          -- exists []; exists wsuf'; exists tt.
             repeat split; auto.
             destruct hr as [w1 [w2 [vs_suf [? [? ?]]]]]; subst.
             destruct H4 as [w3 [w4 [vs_suf' [p'' [f'' [? [? [? [? ?]]]]]]]]].
             exists w1; exists w2; exists vs_suf.
             assert (foo' : (x, rev pre') = (x, rev (rev (rev pre')) ++ [])).
             { rewrite rev_involutive. apps. }
             exists (cast_predicate (x, rev pre') (x, rev (rev (rev pre')) ++ []) foo' p').
             exists (cast_action (x, rev pre') (x, rev (rev (rev pre')) ++ []) foo' f').
             repeat split; auto.
             ++ eapply mapsto_cast; eauto.
             ++ pose proof foo' as foo''.
                symmetry in foo''.
                assert (bar : rev (rev (rev pre')) ++ [] = rev pre').
                { rewrite rev_involutive.
                  apps. }
                erewrite predicate_appl_eq_cast with (ys' := rev pre') (heq := foo'') (heq' := bar).
                rewrite <- cast_predicate_ins_trans with
                    (heq := eq_refl).
                rewrite cast_predicate_refl.
                assert (rev pre' = rev (rev (rev pre'))).
                { rewrite rev_involutive; auto. }
                rewrite rev_tuple_involutive with (heq := H8).
                assert (rev (rev (rev pre')) = rev (rev (rev pre')) ++ []).
                { rew_anr; auto. }
                rewrite concat_tuple_nil_r with (heq := H9).
                assert (rev (rev (rev pre')) = rev pre').
                { rewrite rev_involutive; auto. }
                rewrite <- cast_ss_ins_trans with (heq := H10).
                rewrite cast_ss_roundtrip; auto.
             ++ exists w3; exists w4; exists vs_suf'.
                assert (a : (x0, (rev pre'' ++ [NT x]) ++ suf) =
                            (x0, rev pre ++ NT x :: suf)).
                { rewrite H0. apps. }
                exists (cast_predicate _ _ a p'').
                exists (cast_action _ _ a f''). 
                repeat split; auto.
                ** eapply mapsto_cast with (heq' := a) in H5; eauto.
                ** assert (b : (rev pre'' ++ [NT x ]) ++ suf =
                               rev pre ++ NT x :: suf).
                   { inv a; auto. }
                   eapply cast_predicate_eq_true with (heq := b); eauto.
                   rewrite heq'.
                   rewrite concat_tuple_assoc' with (heq := app_assoc _ _ _); sis.
                   unfold concat_tuple_rec_case.
                   unfold eq_rect_r; sis.
                   unfold concat_tuple_nil_case.
                   unfold eq_rect_r; sis.
                   assert (c : rev pre'' ++ NT x :: suf =
                               rev pre ++ NT x :: suf).
                   { rewrite <- b; apps. }
                   erewrite <- cast_ss_ins_trans with (heq := c).
                   eapply concat_tuple_eq with
                       (heq := H0)
                       (heq' := eq_refl).
                   --- rewrite <- H2.
                       symmetry.
                       assert (d : rev pre'' = rev (rev (rev pre''))).
                       { rewrite rev_involutive; auto. }
                       rewrite rev_tuple_involutive with (heq := d).
                       erewrite <- cast_ss_ins_trans; eauto.
                   --- apply pair_split_eq; auto.
                       symmetry.
                       eapply cast_action_eq with (heq := rr_anr_expand _ _).
                       erewrite rrt_anr; eauto.
                ** eapply lfas_replace_head; eauto.
                   assert (b : (rev pre'' ++ [NT x ]) ++ suf =
                               rev pre ++ NT x :: suf).
                   { inv a; auto. }
                   eapply cast_action_eq with (heq := b); eauto.
                   rewrite heq'.
                   rewrite concat_tuple_assoc' with (heq := app_assoc _ _ _); sis.
                   unfold concat_tuple_rec_case.
                   unfold eq_rect_r; sis.
                   unfold concat_tuple_nil_case.
                   unfold eq_rect_r; sis.
                   assert (c : rev pre'' ++ NT x :: suf =
                               rev pre ++ NT x :: suf).
                   { rewrite <- b; apps. }
                   erewrite <- cast_ss_ins_trans with (heq := c).
                   t.
                   --- rewrite <- H2.
                       erewrite rev_tuple_involutive.
                       erewrite <- cast_ss_ins_trans; eauto.
                   --- symmetry.
                       t'; eauto.
        * assert (rev pre'' = rev (rev (rev pre''))).
          { rewrite rev_involutive; auto. }
          rewrite rev_tuple_involutive with (heq := H).
          eapply svd_eq; eauto.
        * destruct hr as [w1 [w2 [vs_suf [? [? ?]]]]].
          destruct H3 as [w3 [w4 [? [? [? [? [? [? [? ?]]]]]]]]]; subst.
          exists (w' ++ w1); exists (w3 ++ w4); eexists.
          repeat split; auto.
          -- rewrite <- app_assoc.
              rew_anr; auto.
          -- constructor; eauto.
          -- exists w3; exists w4; eexists.
             assert (a : (x0, (rev pre'' ++ [NT x]) ++ suf) =
                         (x0, rev (rev (rev pre'')) ++ NT x :: suf)).
             { rewrite rev_involutive. apps. }
             exists (cast_predicate _ _ a x2).
             exists (cast_action _ _ a x3).
             repeat split; auto.
             ++ eauto.
             ++ t.
             ++ t.
                rewrite heq'.
                t'; eauto; sis.
                repeat unct.
                t'; auto.
             ++ t'.
                rewrite heq'.
                t'; eauto; sis.
                repeat unct.
                t; auto.
                Unshelve.
                all: try auto.
                all: repeat rewrite rev_involutive; apps.
  Qed.

  (** Helper lemma: casting a snoc-shaped symbol tuple distributes over [concat_tuple] when the tail lists are equal. *)
  Lemma cast_ss_snoc' :
    forall (ys zs : list symbol)
           (x : symbol)
           (heq : ys ++ [x] = zs ++ [x])
           (heq' : ys = zs)
           (vs : symbols_semty ys)
           (v : symbol_semty x),
      cast_ss (ys ++ [x]) (zs ++ [x]) heq (concat_tuple ys [x] vs (v, tt)) =
      concat_tuple zs [x] (cast_ss ys zs heq' vs) (v, tt).
  Proof.
    intros ys zs x heq heq' vs v; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (** Consuming a terminal token preserves [unique_frames_derivation]: the uniqueness of the partial derivation is maintained after shifting. *)
  Lemma consume_preserves_ufd :
    forall gr fr fr' pre suf a v vs frs wpre wsuf,
      fr = Fr pre vs (T a :: suf)
      -> fr' = Fr (T a :: pre) (v, vs) suf
      -> unique_frames_derivation gr (fr :: frs) wpre (@existT _ _ a v :: wsuf)
      -> unique_frames_derivation gr (fr' :: frs) (wpre ++ [@existT _ _ a v]) wsuf.
  Proof.
    intros gr fr fr' pre suf a v vs frs w1 w2 ? ? hu; subst.
    inv_ufd hu hv ha hu' hi hvs hpu.
    - constructor; sis; unrt; ss_inj.
      + apply svd_app; auto.
        apply svd_singleton; auto.
      + intros w1''' w2''' pre' vs''' heq' heq hd hr; subst; sis.
        eapply svd_split_eq with (heq := heq') in hd; eauto.
        destruct hd as [w1' [w1'' [vs' [vs'' [? [heq'' [hd hd']]]]]]].
        apply svd_singleton_t in hd'.
        destruct hd' as [v'' [? ?]]; subst.
        repeat rewrite <- app_assoc in heq.
        eapply ha with
            (vs' := rev_tuple _ vs')
            (heq := rev_involutive _)
          in heq; clear ha.
        * destruct heq as [? [hw hvs']]; inv hw; t_inj; sis.
          repeat split; auto.
          rewrite heq''.
          rewrite <- hvs'.
          t'; auto.
        * eapply svd_eq with (xs := rev pre); t'; eauto.
        * destruct hr as [w2' [w2'' [vs_suf [? [hd' ?]]]]]; subst.
          exists ([@existT _ _ _ v''] ++ w2'); exists []; exists (v'', vs_suf).
          repeat split; auto.
    - inv heq'; ss_inj.
      rewrite <- app_assoc in *.
      eapply ufd_upper with (pre' := T a :: pre); sis; eauto; apps; unrt.
      + apply svd_app; auto.
        apply svd_singleton; auto.
      + intros w1''' w2''' pre' vs''' heq' heq hd hr; subst; sis.
        eapply svd_split_eq with (heq := heq') in hd; eauto.
        destruct hd as [w1' [w1'' [vs' [vs'' [? [heq'' [hd hd']]]]]]].
        apply svd_singleton_t in hd'.
        destruct hd' as [v'' [? ?]]; subst.
        repeat rewrite <- app_assoc in heq.
        eapply ha with
            (vs'' := rev_tuple _ vs')
            (heq  := rev_involutive _)
          in heq; clear ha.
        * destruct heq as [? [hw hvs']]; inv hw; t_inj; sis.
          repeat split; auto.
          rewrite heq''.
          rewrite <- hvs'.
          t'; auto.
        * eapply svd_eq with (xs := rev pre); t'; eauto.
        * destruct hr as [w2' [w2'' [vs_suf [? [hd' hex]]]]]; subst.
          destruct hex as [w2''' [w2'''' [vs_suf' [p [f [ ? [hd'' [hm [hp hl]]]]]]]]]; subst.
          exists ([@existT _ _ a v''] ++ w2').
          exists (w2''' ++ w2'''').
          exists (v'', vs_suf).
          repeat split; auto.
          exists w2'''; exists w2''''; exists vs_suf'.
             assert (hcp : (x, rev pre' ++ suf) = (x, rev (rev (rev pre)) ++ T a :: suf)).
             { rewrite rev_involutive.
               rewrite heq'; apps. }
             exists (cast_predicate _ _ hcp p).
             exists (cast_action _ _ hcp f).
             repeat split; t'; auto.
             ++ erewrite concat_tuple_shift_head_l.
                eapply cast_elim_common.
                eapply concat_tuple_eq; eauto.
                ** erewrite <- cast_ss_snoc'.
                   erewrite <- cast_ss_ins_trans.
                   assert (foo :
                             forall xs ys (heq : xs = ys) (heq' : ys = xs) vs vs',
                               cast_ss ys xs heq' vs' = vs
                               -> cast_ss xs ys heq vs =
                                  cast_ss xs ys heq (cast_ss ys xs heq' vs')).
                   { intros; subst.
                     repeat rewrite cast_ss_refl; auto. }
                   erewrite foo; eauto.
                   t'; eauto.
                ** rewrite cast_ss_refl; eauto.
             ++ erewrite concat_tuple_shift_head_l.
                eapply cast_elim_common.
                t'; auto.
                erewrite <- cast_ss_snoc'.
                t'.
                assert (foo :
                          forall xs ys (heq : xs = ys) (heq' : ys = xs) vs vs',
                            cast_ss ys xs heq' vs' = vs
                            -> cast_ss xs ys heq vs =
                               cast_ss xs ys heq (cast_ss ys xs heq' vs')).
                { intros; subst.
                  repeat rewrite cast_ss_refl; auto. }
                erewrite foo; eauto.
                t'; auto.
                Unshelve.
                all: auto.
                all: repeat rewrite rev_involutive; apps.
                all: rewrite heq'; apps.
  Qed.
  
  (** When [adaptive_predict] returns [pred_succ rhs], the current head frame's processed+suffix symbols must equal [rhs], ruling out any other applicable right-hand side. *)
  Lemma adaptive_predict_at_most_one_rhs_applies_shift_head_frame :
    forall gr hw rm cm pre pre' vs vs' x suf suf' frs wmid wsuf ca hc hk rhs ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (Fr pre' vs' suf', Fr pre vs (NT x :: suf) :: frs)
      -> PM.In (x, rhs) gr
      -> sem_values_derivation gr (rev pre') wmid (rev_tuple pre' vs')
      -> stack_accepts_suffix gr (Fr pre' vs' suf', Fr pre vs (NT x :: suf) :: frs) wsuf
      -> adaptive_predict gr hw rm cm pre vs x suf frs (wmid ++ wsuf) ca hc hk = (pred_succ rhs, ca')
      -> rev pre' ++ suf' = rhs.
  Proof.
    intros gr hw rm cm pre pre' vs vs' x suf suf' frs wmid wsuf ca hc hk rhs ca'  hn hr' hc' hw' hi hd hr ha.
    red in hr.
    destruct hr as (w1 & w2 & vs_suf & ? & hd' & hl); subst; sis.
    destruct hl as (w3 & w4 & vs_suf' & p & f & ? & hd'' & hm & hp & hl); subst. 
    eapply adaptive_predict_succ_at_most_one_rhs_applies in ha; eauto.
    - inv hw'; ss_inj; auto.
    - eapply pm_mapsto_in; eauto.
    - red; sis; unct; unrt.
      exists (wmid ++ w1).
      exists (w3 ++ w4).
      exists (concat_tuple _ _ (rev_tuple _ vs') vs_suf).
      repeat split; apps; auto.
      + apply svd_app; auto.
      + exists w3; exists w4; exists vs_suf'; exists p; exists f; auto.
  Qed.

  (** A successful-prediction push preserves [unique_frames_derivation]: the uniqueness condition extends to the new callee frame. *)
  Lemma push_preserves_ufd :
    forall gr cr ce hw rm cm pre vs x suf frs wpre wsuf ca hc hk rhs ca',
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> adaptive_predict gr hw rm cm pre vs x suf frs wsuf ca hc hk = (pred_succ rhs, ca')
      -> unique_frames_derivation gr (cr :: frs) wpre wsuf
      -> unique_frames_derivation gr (ce :: cr :: frs) wpre wsuf.
  Proof.
    intros gr cr ce hw rm cm pre vs x suf frs wpre wsuf ca hc hk rhs ca' ? ? hn hr hc' hw' ha hu; subst.
    assert (heq: wpre = wpre ++ []) by apps; rewrite heq.
    eapply ufd_upper with (pre' := []); eauto.
    - eapply adaptive_predict_succ_in_grammar; eauto.
    - intros wmid' wsuf' pre'' vs'' heq' heq'' hd hr'; sis.
      unrt.
      eapply svd_inv_nil_syms with (heq := heq') in hd; eauto.
      destruct hd as [? heq''']; subst; auto.
    - intros wmid' wsuf' pre'' suf'' vs'' heq' hi hd hr'.
      simpl; simpl in heq'; subst.
      eapply adaptive_predict_at_most_one_rhs_applies_shift_head_frame; eauto.
      + constructor; auto.
      + eapply adaptive_predict_succ_in_grammar; eauto.
  Qed.

  (** The unambiguous-parse invariant: when [un = true], the consumed prefix has a unique derivation via [unique_frames_derivation]. *)
  Definition unique_stack_prefix_derivation gr w sk wsuf un :=
    match sk with
    | (fr, frs) =>
      un = true
      -> exists wpre,
          w = wpre ++ wsuf
          /\ unique_frames_derivation gr (fr :: frs) wpre wsuf
    end.

  (** A [step_k] result preserves [unique_stack_prefix_derivation], propagating unambiguity through each step. *)
  Lemma step_preserves_unique_stack_prefix_derivation_invar :
    forall gr hw w rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr sk
      -> unique_stack_prefix_derivation gr w sk ts un
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> unique_stack_prefix_derivation gr w sk' ts' un'.
  Proof.
    intros gr hw w rm cm (fr, frs) (fr', frs') ts ts' vi vi' un un' ca ca'
           hc hk hn hr hc' hw' hu hs; red; red in hu; intros hu'.
    unfold step in hs; dmeqs h; inv hs; tc;
      destruct hu as (wpre & heq & hu); subst; auto.
    - exists wpre; split; auto.
      eapply return_preserves_unique_frames_derivation; eauto.
      auto.
    - eexists; split.
      + rewrite cons_app_singleton; rewrite app_assoc; eauto.
      + eapply consume_preserves_ufd; eauto.
    - exists wpre; split; auto.
      eapply push_preserves_ufd; eauto.
  Qed.

  (** The initial stack satisfies [unique_stack_prefix_derivation] with an empty consumed prefix and [un = true]. *)
  Lemma unique_stack_prefix_derivation_invar_starts_true :
    forall g ys ts,
      unique_stack_prefix_derivation g ts (Fr [] tt ys, []) ts true. 
  Proof.
    intros g ys ts; red; intros _.
    exists []; split; auto.
    constructor; auto.
    intros wpre' wsuf' pre' vs' heq heq' hd ha; sis; subst.
    eapply svd_inv_nil_syms with (heq := heq) in hd; eauto.
    destruct hd as [? heq']; subst; sis; auto.
  Qed.

  (** Internal induction step for unambiguous soundness: if [multistep] returns [unique x v] and the unique-stack-prefix invariant holds, then [v] is the unique semantic value for [w]. *)
  Lemma multistep_sound_unambig' :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (tri    : nat * nat * nat)
           (ha     : Acc lex_nat_triple tri)
           (w ts   : list token)
           (vi     : NtSet.t)
           (sk     : parser_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (ha'    : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (v      : nt_semty x),
      tri = parser_meas rm sk ts vi
      -> no_left_recursion gr
      -> closure_map_complete gr cm
      -> stack_wf gr sk
      -> unique_stack_prefix_derivation gr w sk ts un
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha' = unique x v
      -> sem_value_derivation gr (NT x) w v 
         /\ (forall v',
                sem_value_derivation gr (NT x) w v'
                -> v' = v).
  Proof.
    intros gr hw rm hr cm x tri ha.
    induction ha as [tri hlt IH].
    intros w ts vi sk un ca hc hk hb ha' v ? hn hc' hw' hu hm; subst.
    apply multistep_cases in hm.
    destruct hm as [[hf hu'] | he]; subst.
    - apply step_step_accept_facts in hf.
      destruct hf as [? ?]; subst.
      red in hu.
      destruct hu as [wpre [? hu]]; subst; auto.
      rew_anr.
      inv_ufd hu hv ha hu' hi hvs hpu; ss_inj; sis; unrt; unct.
      split.
      + apply svd_singleton; auto.
      + intros v' hd.
        eapply svd_singleton in hd.
        assert (foo : forall gr
                             (ys : list symbol)
                             w
                             (vs : symbols_semty ys),
                   sem_values_derivation gr ys w vs
                   -> sem_values_derivation gr (rev (rev ys)) w (rev_tuple _ (rev_tuple _ vs))).
        { intros.
          eapply svd_eq with (heq := rr_expand _ _); eauto.
          erewrite rev_tuple_involutive; eauto. }
        apply foo in hd.
        eapply ha with (heq := rev_involutive _) in hd; eauto.
        * destruct hd as [? [? heq]]; subst.
          rewrite rev_tuple_involutive with (heq := rr_expand _ _) in heq.
          rewrite cast_ss_roundtrip in heq.
          inv heq; auto.
        * exists []; exists []; exists tt; repeat split; auto.
    - destruct he as (sk' & ts' & vi' & un' & ca' & hc'' & hk' & hb' & ha'' & hs & hm).
      eapply IH with (w := w) in hm; eauto.
      + eapply step_parser_meas_lt; eauto.
      + eapply step_preserves_stack_wf_invar; eauto.
      + eapply step_preserves_unique_stack_prefix_derivation_invar; eauto.
  Qed.

  (** If [multistep] returns [unique x v], then [v] is both a valid and the unique semantic value for the full input [w] under nonterminal [x]. *)
  Lemma multistep_sound_unambig :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (x      : nonterminal)
           (cm     : closure_map)
           (w ts   : list token)
           (vi     : NtSet.t)
           (sk     : parser_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (ha     : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (v      : nt_semty x),
      no_left_recursion gr
      -> closure_map_complete gr cm
      -> stack_wf gr sk
      -> unique_stack_prefix_derivation gr w sk ts un
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha = unique x v
      -> sem_value_derivation gr (NT x) w v
         /\ (forall v',
                sem_value_derivation gr (NT x) w v'
                -> v' = v).
  Proof.
    intros; eapply multistep_sound_unambig'; eauto.
  Qed.

  (* now for the ambiguous case *)

  (* Invariant for proving the "ambiguous" version of the parser soundness theorem. *)
  (** Witnesses that the parser stack encodes an ambiguous partial derivation: either two distinct right-hand sides apply at some prediction point, or two distinct forests derive the same consumed segment. *)
  Inductive ambiguous_frames_derivation (g : grammar) :
    list parser_frame -> list token -> list token -> Prop :=
  | afd_push :
      forall cr ce frs pre vs x suf pre' vs' suf' alt_rhs wpre wmid wsuf,
        Fr pre vs (NT x :: suf) = cr
        -> Fr pre' vs' suf'     = ce
        -> frames_derivation g (cr :: frs) wpre (wmid ++ wsuf)
        -> PM.In (x, rev pre' ++ suf') g
        -> sem_values_derivation g (rev pre') wmid (rev_tuple _ vs')
        -> PM.In (x, alt_rhs) g
        -> rev pre' ++ suf' <> alt_rhs
        -> gamma_recognize g (alt_rhs ++ suf ++ unproc_tail_syms frs) (wmid ++ wsuf)
        -> ambiguous_frames_derivation g (ce :: cr :: frs) (wpre ++ wmid) wsuf
  | afd_sem :
      forall fr frs pre vs suf wpre wmid wmid' wsuf wsuf' trs trs',
        Fr pre vs suf = fr
        -> frames_derivation g frs wpre (wmid ++ wsuf)
        -> sem_values_derivation g (rev pre) wmid (rev_tuple _ vs)
        -> forest_derivation g (rev pre) wmid (rev trs)
        -> forest_derivation g (rev pre) wmid' (rev trs')
        (* maybe not necessary? *)
        -> gamma_recognize g (suf ++ unproc_tail_syms frs) wsuf'
        -> wmid' ++ wsuf' = wmid ++ wsuf
        -> rev trs' <> rev trs
        -> ambiguous_frames_derivation g (fr :: frs) (wpre ++ wmid) wsuf
  | afd_tail :
      forall fr frs pre vs suf wpre wmid wsuf,
        Fr pre vs suf = fr 
        -> ambiguous_frames_derivation g frs wpre (wmid ++ wsuf)
        -> sem_values_derivation g (rev pre) wmid (rev_tuple _ vs)
        -> ambiguous_frames_derivation g (fr :: frs) (wpre ++ wmid) wsuf.

  Hint Constructors ambiguous_frames_derivation : core.

  Ltac inv_afd hafd heq heq' hfrd hi hsvd hi' hneq hr hfod hfod' heq hafd' :=
    inversion hafd as
        [ ? ? ? ? ? ? ? ? ? ? ? ? ? ? heq heq' hfrd hi hsvd hi' hneq hr
        | ? ? ? ? ? ? ? ? ? ? ? ? heq hfrd hsvd hfod hfod' hr heq' hneq
        | ? ? ? ? ? ? ? ? heq hafd' hsvd]; subst; clear hafd.

  (** A return step preserves [ambiguous_frames_derivation]: the ambiguity evidence survives folding a completed frame into its caller. *)
  Lemma return_preserves_afd :
    forall gr hw ce cr cr' frs pre vs x suf pre' vs' p f wpre wsuf,
      ce     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf
      -> find_predicate_and_action (x, rev pre') gr hw = Some (p, f)
      -> p (rev_tuple _ vs') = true
      -> ambiguous_frames_derivation gr (ce :: cr :: frs) wpre wsuf
      -> ambiguous_frames_derivation gr (cr' :: frs) wpre wsuf.
  Proof.
    intros gr hw ? ? ? frs pre vs x suf pre' vs' p f wpre wsuf ? ? ? hfpaa hp hafd; subst.
    appl_fpaa.
    pose proof hfpaa as hpin; apply pm_mapsto_in in hpin.
    inv_afd hafd heq heq' hfrd hi hsvd hi' hneq hr hfod hfod' heq hafd'.
    - (* ambig push case *)
      inv heq; inv heq'; repeat ss_inj; rew_anr.
      eapply fd_inv_cons in hfrd; auto.
      destruct hfrd as (wp & wp' & heq & hsvd' & hfrd); subst. 
      apply gamma_recognize_split in hr.
      destruct hr as (w & w' & heq & hr & hr'); subst.
      apply gamma_recognize__exists_forest_derivation in hr.
      destruct hr as (vs_alt & hr).      
      assert (hex : exists trs, forest_derivation gr (rev pre') wmid (rev trs)) by (eapply svd__exists_rev_forest_der; eauto).
      destruct hex as [trs hfod].
      assert (hex : exists trs, forest_derivation gr (rev pre) wp' (rev trs)) by (eapply svd__exists_rev_forest_der; eauto).
      destruct hex as [trs_cr hfod_cr].
      rewrite <- app_assoc.
      eapply afd_sem with
          (pre  := NT x :: pre)
          (vs   := (f (rev_tuple _ vs'), vs))
          (trs  := node x (rev trs) :: trs_cr)
          (trs' := node x vs_alt :: trs_cr); eauto; sis.
      + apps.
      + unrt.
        apply svd_app; auto.
        rew_nil_r wmid; constructor; eauto.
      + apply forest_derivation_app; auto.
        rew_nil_r wmid; eauto.
      + eapply forest_derivation_app; eauto.
      + repeat rewrite <- app_assoc in *.
        rewrite heq; auto.
      + intros heq'.
        apply app_inj_tail in heq'.
        destruct heq' as [_ hh]; inv hh.
        eapply forests_eq__words_eq_rhss_eq with (ys := rev pre') in hr; eauto.
        destruct hr as (? & ? & ?); tc.
    - (* sem case *)
      inv heq; ss_inj; sis. 
      eapply fd_inv_cons in hfrd.
      destruct hfrd as (wp & wp' & heq'' & hf' & hg'); subst.
      rewrite <- app_assoc.
      assert (hex : exists trs_cr, forest_derivation gr (rev pre) wp' (rev trs_cr)) by (eapply svd__exists_rev_forest_der; eauto).
      destruct hex as (trs_cr & hfod'').
      eapply afd_sem with
          (pre   := NT x :: pre)
          (wmid' := wp' ++ wmid')
          (trs   := node x (rev trs) :: trs_cr)
          (trs'  := node x (rev trs') :: trs_cr); eauto; sis; apps.
      + apply svd_app; auto.
        rew_nil_r wmid.
        constructor; eauto.
      + apply forest_derivation_app; auto.
        rew_nil_r wmid; eauto.
      + apply forest_derivation_app; auto.
        rew_nil_r wmid'; eauto.
      + repeat rewrite <- app_assoc.
        rewrite heq'; auto.
      + unfold not; intros heq''.
        apply app_inj_tail in heq''; destruct heq'' as [_ hh]; inv hh; tc.
    - (* tail case *)
      inv heq; ss_inj.
      inv_afd hafd' heq heq' hfrd hi hsvd' hi' hneq hr hfod hfod' heq hafd''; sis.
      + (* caller push case *)
        inv heq'; ss_inj.
        rewrite <- app_assoc.
        eapply afd_push with (pre' := NT x :: pre); eauto; sis; apps.
        apply svd_app; auto.
        rew_nil_r wmid; constructor; eauto.
      + (* caller sem case *)
        inv heq; ss_inj.
        inv_gr hr wmid'' wsuf'' hs hr'.
        inv_sr hs hi hg''.
        apply gamma_recognize__exists_forest_derivation in hg''.
        destruct hg'' as [vs_ys h_vs_ys].
        rewrite <- app_assoc.
        assert (hex : exists trs'', forest_derivation gr (rev pre') wmid (rev trs'')) by (eapply svd__exists_rev_forest_der; eauto).
        destruct hex as (trs'' & hfod'').
        eapply afd_sem with
            (pre   := NT x :: pre)
            (vs    := (f (rev_tuple _ vs'), vs))
            (wmid' := wmid' ++ wmid'')
            (trs   := node x (rev trs'') :: trs)
            (trs'  := node x vs_ys :: trs'); eauto; sis; apps.
        * apply svd_app; auto.
          rew_nil_r wmid.
          constructor; eauto.
        * apply forest_derivation_app; auto.
          rew_nil_r wmid; eauto.
        * apply forest_derivation_app; auto.
          rew_nil_r wmid''; eauto.
        * intros heq''.
          apply app_inj_tail in heq''.
          destruct heq'' as [? ?]; tc.
      + inv heq. 
        rewrite <- app_assoc.
        eapply afd_tail with (pre := NT x :: pre); eauto.
        * rewrite <- app_assoc; auto.
        * apply svd_app; auto.
          rew_nil_r wmid.
          constructor; eauto.
  Qed.

  (** Consuming a terminal token preserves [ambiguous_frames_derivation]: the ambiguity evidence is maintained after shifting. *)
  Lemma consume_preserves_afd :
    forall gr fr fr' pre vs a v suf wpre wsuf frs,
      fr     = Fr pre vs (T a :: suf)
      -> fr' = Fr (T a :: pre) (v, vs) suf
      -> ambiguous_frames_derivation gr (fr :: frs) wpre (@existT _ _ a v :: wsuf )
      -> ambiguous_frames_derivation gr (fr' :: frs) (wpre ++ [@existT _ _ a v]) wsuf.
  Proof.
    intros gr ? ? pre vs a v suf wpre wsuf frs ? ? hafd; subst. inv_afd hafd heq heq' hfrd hi hsvd hi' hneq hr hfod hfod' heq hafd'; sis.
    - (* push case *)
      inv heq'; ss_inj.
      rewrite <- app_assoc. 
      eapply afd_push with (pre' := T a :: pre); eauto; sis; apps.
      apply svd_app; auto.
      apply svd_singleton; auto.
    - (* sem case *)
      inv heq; ss_inj.
      inv_gr hr wmid'' wsuf'' hs hr'.
      inversion hs as [a' l' |]; subst; clear hs.
      rewrite <- app_assoc.
      eapply afd_sem with
          (pre   := T a :: pre)
          (wmid' := wmid' ++ [@existT _ _ a l'])
          (trs   := leaf a :: trs)
          (trs'  := leaf a :: trs'); eauto; sis; apps.
      + apply svd_app; auto.
        apply svd_singleton; auto.
      + apply forest_derivation_app; auto.
        apply terminal_head_forest_derivation; auto.
      + apply forest_derivation_app; auto.
        apply terminal_head_forest_derivation; auto.
      + intros heq''.
        apply app_inj_tail in heq''; destruct heq''; tc.
    - inv heq; ss_inj.
      rewrite <- app_assoc.
      eapply afd_tail with (pre := T a :: pre); eauto; sis; apps.
      apply svd_app; auto.
      apply svd_singleton; auto.
  Qed.

  (* to do : these next lemmas should probably be in Prediction *)

  (* refactor *)
  (** If [ll_predict'] returns [pred_ambig rhs], then two distinct original subparsers both reach a final configuration, witnessing two distinct right-hand sides. *)
  Lemma ll_predict'_ambig_rhs_leads_to_successful_parse' :
    forall gr hw rm orig_sps wsuf wpre curr_sps rhs hk,
      rhs_map_correct rm gr
      -> all_stacks_wf gr orig_sps
      -> subparsers_sound_wrt_originals gr orig_sps wpre curr_sps wsuf
      -> ll_predict' gr hw rm curr_sps wsuf hk = pred_ambig rhs
      -> exists orig_sp final_sp orig_sp' final_sp' rhs',
          In orig_sp orig_sps
          /\ orig_sp.(prediction) = rhs
          /\ move_closure_multistep' gr orig_sp (wpre ++ wsuf) final_sp []
          /\ final_config final_sp = true
          /\ In orig_sp' orig_sps
          /\ orig_sp'.(prediction) = rhs'
          /\ move_closure_multistep' gr orig_sp' (wpre ++ wsuf) final_sp' []
          /\ final_config final_sp' = true
          /\ rhs' <> rhs.
  Proof.
    intros gr hw rm orig_sps wsuf.
    induction wsuf as [| (a,l) wsuf' IH]; intros wpre curr_sps rhs hk hp ha hi hl; sis; tc.
    - (* lemma *)
      unfold handle_final_subparsers in hl.
      destruct (filter _ _) as [| csp' csps'] eqn:hf; tc.
      destruct (all_predictions_equal_b _ _ csp' csps') eqn:ha''; tc.
      inv hl.
      unfold subparsers_sound_wrt_originals in hi.
      pose proof hf as hf'.
      eapply filter_cons_in in hf.
      apply hi in hf.
      destruct hf as [orig_sp [hi' hm]].
      apply all_predictions_equal_b_false_exists_diff_rhs in ha''.
      destruct ha'' as [csp'' [hi'' hn]].
      assert (hi''' : In csp'' curr_sps).
      { eapply filter_tail_in; eauto. }
      apply hi in hi'''.
      destruct hi''' as [orig_sp' [hi''' hm']].
      exists orig_sp; exists csp'; exists orig_sp'; exists csp'';
      exists csp''.(prediction); repeat split; auto.
      + eapply mcms'_preserves_label; eauto.
      + assert (hi'''' : In csp' (filter final_config curr_sps)).
        { rewrite hf'; apply in_eq. }
        eapply filter_In in hi''''; destruct hi''''; auto.
      + eapply mcms'_preserves_label; eauto.
      + assert (hi'''' : In csp'' (filter final_config curr_sps)). 
        { rewrite hf'; apply in_cons; auto. }
        eapply filter_In in hi''''; destruct hi''''; auto.
      + apply beq_gamma_eq_iff.
    - destruct curr_sps as [| csp csps]; tc.
      destruct (all_predictions_equal_b _ _); tc.
      apply ll_predict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      eapply IH with (wpre := wpre ++ [@existT _ _ a l]) in hl; eauto.
      + destruct hl as [osp [fsp [osp' [fsp' [rhs' [hi' [heq [hm' [hf [hi'' [heq' [hm'' [hf' hn]]]]]]]]]]]]]; subst.
        rewrite <- app_assoc in *; sis.
        exists osp; exists fsp; exists osp'; exists fsp';
          exists osp'.(prediction); repeat split; eauto.
      + eapply ll_target_preserves_subparsers_sound_invar; eauto.
   Qed.

  (** If [ll_predict] returns [pred_ambig rhs], then the predicted [rhs] is accepted by the stack and a distinct alternative right-hand side also accepts the suffix. *)
  Lemma ll_predict_ambig_two_rhss_sas:
    forall gr hw rm cr ce pre vs x suf frs w hk rhs,
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> ll_predict gr hw rm pre vs x suf frs w hk = pred_ambig rhs
      -> stack_accepts_suffix gr (ce, cr :: frs) w
         /\ (exists rhs',
                PM.In (x, rhs') gr
                /\ rhs' <> rhs
                /\ stack_accepts_suffix gr (Fr [] tt rhs', cr :: frs) w).
  
  Proof.
    intros gr hw rm cr ce pre vs x suf frs w hk rhs ? ? hn hp hw' hl; subst; sis.
    pose proof hl as hl'; eapply ll_predict_ambig_in_grammar in hl'; eauto.
    apply ll_predict_cases in hl.
    destruct hl as [sps [hss hl]].
    eapply ll_predict'_ambig_rhs_leads_to_successful_parse'
      with (orig_sps := sps) (wpre := []) in hl; sis; eauto.
    - destruct hl as [osp [fsp [osp' [fsp' [rhs' [hi [heq [hm [hf [hi' [heq' [hm' [hf' hn']]]]]]]]]]]]]; subst.
      split.
      + eapply mcms'_final_config in hm; auto.
        eapply closure_ussr_backwards with (sp' := osp) (w := w) in hss; eauto.
        * destruct hss as [init_sp [vi' [hi'' [hc hg]]]].
          (* lemma? *)
          apply in_map_iff in hi''.
          destruct hi'' as [rhs [heq hi'']]; subst; sis.
          apply closure_multistep_preserves_label in hc; sis; subst; auto.
        * (* lemma *)
          red. intros init_sp hi''.
          eapply ll_init_sps_preserves_stack_wf_invar; eauto.
      + exists osp'.(prediction); repeat split; auto.
        * eapply ll_start_state_sp_prediction_in_rhss_for
            with (sp' := osp') in hss; eauto.
          eapply rhss_for_in_iff in hss; eauto.
        * eapply mcms'_final_config in hm'; auto.
          eapply closure_ussr_backwards with (sp' := osp') (w := w) in hss; eauto.
          -- destruct hss as [init_sp [vi' [hi'' [hc hg]]]].
             (* lemma? *)
             apply in_map_iff in hi''.
             destruct hi'' as [rhs [heq hi'']]; subst; sis.
             apply closure_multistep_preserves_label in hc; sis; subst; auto.
          -- red; intros init_sp hi''.
             eapply ll_init_sps_preserves_stack_wf_invar; eauto.
    - eapply ll_start_state_preserves_stacks_wf_invar; eauto. 
    - red. intros sp' hi; sis.
      exists sp'; split; auto.
      eapply closure_func_refines_closure_multistep_backward in hi; eauto.
      + destruct hi as [av'' [sp [hi hc]]].
        assert (hst : stable_config sp'.(stack)).
        { eapply stable_config_after_closure_multistep; eauto.
          eapply ll_init_sps_preserves_stack_wf_invar; eauto. }
        destruct sp' as [pred ([suf'], frs')]; inv hst; auto.
      + intros sp hi'; eapply ll_init_sps_preserves_stack_wf_invar; eauto.
  Qed.

  (** The ambiguous-parse invariant: when [un = false], there is a prefix witnessed by [ambiguous_frames_derivation]. *)
  Definition ambiguous_stack_prefix_derivation gr w sk wsuf un :=
    match sk with
    | (fr, frs) => 
      un = false
      -> exists wpre,
          w = wpre ++ wsuf
          /\ ambiguous_frames_derivation gr (fr :: frs) wpre wsuf
    end.

  (** The initial stack with [un = true] vacuously satisfies [ambiguous_stack_prefix_derivation] since its hypothesis is false. *)
  Lemma ambiguous_stack_prefix_derivation_invar_starts_true :
    forall gr ys ts,
      ambiguous_stack_prefix_derivation gr ts (Fr [] tt ys, []) ts true.
  Proof.
    intros g ys ts hc; inv hc.
  Qed.

  (** If the lower frames accept a suffix via [lower_frames_accept_suffix], then the grammar recognizes the unprocessed tail symbols of those frames on the same suffix. *)
  Lemma lfas_recognize :
    forall gr frs fr ss vs ts,
      frames_wf gr (fr :: frs)
      -> lower_frames_accept_suffix gr ss vs frs ts
      -> gamma_recognize gr (unproc_tail_syms frs) ts.
  Proof.
    intros gr frs.
    induction frs as [| [pre vs suf] frs IH]; intros fr ss vs' ts hw hl; subst; tc.
    - simpl; red in hl; subst; auto.
    - inv hw; ss_inj.
      red in hl.
      destruct hl as (wpre & wsuf & vs_suf & p & f & heq & hd & hm & hp & hl); subst; simpl.
      fold lower_frames_accept_suffix in hl.
      apply gamma_recognize_app.
      + apply svd__exists_forest_der in hd.
        destruct hd as (trs & hfod).
        eapply forest_derivation__gamma_recognize; eauto.
      + eapply IH; eauto.
  Qed.
  
  (** A [step_k] result preserves [ambiguous_stack_prefix_derivation], so ambiguity evidence accumulates correctly through each step. *)
  Lemma step_preserves_ambiguous_stack_prefix_derivation_invar :
    forall gr hw rm cm w sk sk' ts ts' vi vi' un un' ca hc hk ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr sk
      -> stack_prefix_derivation gr w sk ts
      -> ambiguous_stack_prefix_derivation gr w sk ts un
      -> step gr hw rm cm sk ts vi un ca hc hk = step_k sk' ts' vi' un' ca'
      -> ambiguous_stack_prefix_derivation gr w sk' ts' un'.
  Proof.
    intros gr hw rm cm w (fr, frs) (fr', frs') ts ts' vi vi' un un' ca
           hc hk ca' hn hp' hw' hp ha hs; red; red in ha; intros hu.
    unfold step in hs; dmeqs h; inv hs; tc.
    - (* return *)
      destruct ha as (wpre & heq & ha); subst; sis; auto.
      exists wpre.
      eapply return_preserves_afd in ha; eauto.
    - (* consume *)
      destruct ha as (wpre & heq & ha); subst; sis; auto.
      eexists; split.
      + rewrite cons_app_singleton; rewrite app_assoc; eauto.
      + eapply consume_preserves_afd; eauto.
    - (* unambiguous push *)
      destruct ha as (wpre & heq & ha); subst; sis; auto. 
      eexists; split; eauto.
      rew_nil_r wpre; eapply afd_tail with (pre := []); eauto.
    - (* ambiguous push *)
      destruct hp as (wpre & heq & hd); subst.
      exists wpre; split; auto.
      rew_nil_r wpre.
      match goal with
      | H : adaptive_predict _ _ _ _ _ _ _ _ _ _ _ _ _ = (pred_ambig _, _) |- _ =>
        pose proof H as hllp; apply adaptive_predict_ambig_ll_predict_ambig in hllp
      end.
      pose proof hllp as hllp'.
      apply ll_predict_ambig_in_grammar in hllp'; auto.
      eapply ll_predict_ambig_two_rhss_sas in hllp; eauto.
      destruct hllp as (hsas & rhs' & hi & hneq & hsas').
      eapply afd_push with (pre' := []); eauto.
      (* todo -- lemma -- sas --> gamma_recognize *)
      simpl.
      red in hsas'.
      destruct hsas' as (wpre' & wsuf' & vs_suf & heq & hd' & hl); subst.
      red in hl.
      destruct hl as (wsuf'' & wsuf''' & vs_suf' & p & f & heq & hd'' & hm & hp & hl); subst.
      fold lower_frames_accept_suffix in hl; sis.
      apply gamma_recognize_app.
      + apply svd__exists_forest_der in hd'.
        destruct hd' as (trs & hfod).
        eapply forest_derivation__gamma_recognize; eauto.
      + apply gamma_recognize_app.
        * apply svd__exists_forest_der in hd''.
          destruct hd'' as (trs' & hfod').
          eapply forest_derivation__gamma_recognize; eauto.
        * eapply lfas_recognize; eauto.
  Qed.

  (** Internal induction step for ambiguous soundness: if [multistep] returns [ambig x v] and the ambiguous-stack-prefix invariant holds, then [v] is valid and two distinct parse trees exist for [w]. *)
  Lemma multistep_sound_ambig' :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (w wsuf : list token)
           (vi     : NtSet.t)
           (sk     : parser_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (hk     : stack_pushes_from_keyset rm sk)
           (a'     : Acc lex_nat_triple (parser_meas rm sk wsuf vi))
           (v      : nt_semty x),
      tri = parser_meas rm sk wsuf vi
      -> no_left_recursion gr
      -> stack_wf gr sk
      -> stack_prefix_derivation gr w sk wsuf
      -> ambiguous_stack_prefix_derivation gr w sk wsuf un
      -> multistep gr hw rm hr cm x sk wsuf vi un ca hc hk hb a' = ambig x v
      -> sem_value_derivation gr (NT x) w v
         /\ (exists t t' : tree,
                tree_derivation gr (NT x) w t
                /\ tree_derivation gr (NT x) w t'
                /\ t <> t').
  Proof.
    intros gr hw rm hr cm x tri a.
    induction a as [tri hlt IH].
    intros w wsuf vi sk un ca hc hk hb a' v ? hn hw' hd ha hm; subst.
    apply multistep_cases in hm.
    destruct hm as [[hs hu] | he]; subst.
    - apply step_step_accept_facts in hs.
      destruct hs as [? ?]; subst.
      red in ha.
      destruct ha as (wpre & heq & ha); subst; auto; rew_anr.
      clear IH. clear a'. clear hlt.
      inv_afd ha heq heq' hfrd hi hsvd hi' hneq hr' hfod hfod' heq hafd'.
      + rew_anr; subst.
        inv heq; ss_inj.
        inv hfrd; sis.
        inv hr'; rew_anr; sis.
        unrt; unct.
        split.
        * apply svd_singleton; auto.
        * apply forest_der_singleton__tree_der in hfod.
          destruct hfod as (tr & heq & htd).
          apply forest_der_singleton__tree_der in hfod'.
          destruct hfod' as (tr' & heq' & htd').
          rewrite heq in hneq; rewrite heq' in hneq.
          exists tr; exists tr'; repeat split; auto; tc.
      + inv hafd'.
    - destruct he as (sk' & ts' & vi' & un' & ca' & hc' & hk' & hb' & a'' & hs & hm).
      eapply IH with (w := w) in hm; eauto.
      + eapply step_parser_meas_lt; eauto.
      + eapply step_preserves_stack_wf_invar; eauto. 
      + eapply step_preserves_stack_prefix_derivation_invar; eauto. 
      + eapply step_preserves_ambiguous_stack_prefix_derivation_invar; eauto.
  Qed.

  (** If [multistep] returns [ambig x v], then [v] is valid for [w] under [x] and two distinct parse trees witness the ambiguity. *)
  Lemma multistep_sound_ambig :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (w wsuf : list token)
           (vi     : NtSet.t)
           (sk     : parser_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (ha     : Acc lex_nat_triple (parser_meas rm sk wsuf vi))
           (v      : nt_semty x),
      no_left_recursion gr
      -> stack_wf gr sk
      -> stack_prefix_derivation gr w sk wsuf
      -> ambiguous_stack_prefix_derivation gr w sk wsuf un
      -> multistep gr hw rm hr cm x sk wsuf vi un ca hc hk hb ha = ambig _ v
      -> sem_value_derivation gr (NT x) w v
         /\ (exists t t' : tree,
                tree_derivation gr (NT x) w t
                /\ tree_derivation gr (NT x) w t'
                /\ t <> t').
  Proof.
    intros; eapply multistep_sound_ambig'; eauto.
  Qed.
  
End ParserSoundFn.
