(** Layer 3 of the proof, and UNSAT soundness: when [Solver.solve] answers
    "unsatisfiable", the formula it was given has no model.

    Fix a valuation [val] that satisfies the formula.  Each function gets a
    [wp] specification over the abstract state of [SolverRepr], and the
    invariants of [SolverInv] are carried through them, so that [search]
    never answers 0 and [load] never answers false. *)
From Stdlib Require Import List PeanoNat Lia Bool Permutation.
From Crane Require Import Monads.ITree.
Require Import SatVec VecSem Solver SolverSat SolverRepr SolverInv.
Import ListNotations.
Import Solver.

Lemma wp_seq {T U} (t : itree vecE T) (k : T -> itree vecE U) P Q h :
  wp t P h -> (forall r h1, P r h1 -> wp (k r) Q h1) -> wp (ITree.bind t k) Q h.
Proof. intros Ht Hk. apply wp_bind. eapply wp_conseq; [exact Ht | exact Hk]. Qed.

Section Spec.
Variables (s : state) (inp : vec nat) (xs0 : list nat) (val : nat -> bool).

Local Notation R := (repr s inp xs0).
Local Notation keeps := (keeps s inp).

Lemma keeps_trans st h1 h2 h3 : keeps st h1 h2 -> keeps st h2 h3 -> keeps st h1 h3.
Proof. intros H1 H2 v xs Hv Hp. auto. Qed.

Lemma locs_eq st st' : hcls st' = hcls st -> hwl st' = hwl st -> locs s inp st' = locs s inp st.
Proof. intros E1 E2. unfold locs. now rewrite E1, E2. Qed.

Lemma keeps_eq st st' h h' : hcls st' = hcls st -> hwl st' = hwl st -> keeps st' h h' -> keeps st h h'.
Proof. intros E1 E2 H. unfold SolverRepr.keeps. rewrite <- (locs_eq st st' E1 E2). exact H. Qed.

(** ** Stepping *)

(** One event of the program against [repr].  [eassumption] finds the
    [repr] of the heap the goal is about. *)
Ltac ev :=
  cbv beta;
  match goal with
  | |- wp (ITree.bind _ _) _ _ => apply wp_bind
  | |- wp (Ret _) _ _ => apply wp_ret
  | |- wp (vabort _) _ _ => apply wp_vabort
  | |- wp (vget (assigns s) _) _ _ => refine (get_f s inp xs0 _ _ _ FAsg _ _ _); [eassumption | ]
  | |- wp (vget (level s) _) _ _ => refine (get_f s inp xs0 _ _ _ FLvl _ _ _); [eassumption | ]
  | |- wp (vget (reason s) _) _ _ => refine (get_f s inp xs0 _ _ _ FRsn _ _ _); [eassumption | ]
  | |- wp (vget (phase s) _) _ _ => refine (get_f s inp xs0 _ _ _ FPh _ _ _); [eassumption | ]
  | |- wp (vget (stamp s) _) _ _ => refine (get_f s inp xs0 _ _ _ FSt _ _ _); [eassumption | ]
  | |- wp (vget (seen s) _) _ _ => refine (get_f s inp xs0 _ _ _ FSn _ _ _); [eassumption | ]
  | |- wp (vget (trail s) _) _ _ => refine (get_f s inp xs0 _ _ _ FTr _ _ _); [eassumption | ]
  | |- wp (vget (trail_lim s) _) _ _ => refine (get_f s inp xs0 _ _ _ FLim _ _ _); [eassumption | ]
  | |- wp (vget (misc s) _) _ _ => refine (get_f s inp xs0 _ _ _ FMisc _ _ _); [eassumption | ]
  | |- wp (vlen (trail s)) _ _ => refine (len_f s inp xs0 _ _ _ FTr _ _); [eassumption |]
  | |- wp (vlen (trail_lim s)) _ _ => refine (len_f s inp xs0 _ _ _ FLim _ _); [eassumption |]
  | |- wp (vset (assigns s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FAsg _ _ _ _); [eassumption | ]
  | |- wp (vset (level s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FLvl _ _ _ _); [eassumption | ]
  | |- wp (vset (reason s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FRsn _ _ _ _); [eassumption | ]
  | |- wp (vset (phase s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FPh _ _ _ _); [eassumption | ]
  | |- wp (vset (stamp s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FSt _ _ _ _); [eassumption | ]
  | |- wp (vset (seen s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FSn _ _ _ _); [eassumption | ]
  | |- wp (vset (misc s) _ _) _ _ => refine (set_f s inp xs0 _ _ _ FMisc _ _ _ _); [eassumption | ]
  | |- wp (vpush (trail s) _) _ _ => refine (push_f s inp xs0 _ _ _ FTr _ _ _); [eassumption | ]
  | |- wp (vpush (trail_lim s) _) _ _ => refine (push_f s inp xs0 _ _ _ FLim _ _ _); [eassumption | ]
  | |- wp (vshrink (trail s) _) _ _ => refine (shrink_f s inp xs0 _ _ _ FTr _ _ _); [eassumption | ]
  | |- wp (vshrink (trail_lim s) _) _ _ => refine (shrink_f s inp xs0 _ _ _ FLim _ _ _); [eassumption | ]
  | |- wp (vget (clauses s) _) _ _ => refine (get_hc s inp xs0 _ _ _ _ _ _); [eassumption | ]
  | |- wp (vget (watches s) _) _ _ => refine (get_hw s inp xs0 _ _ _ _ _ _); [eassumption | ]
  | |- wp (vlen (clauses s)) _ _ => refine (len_hc s inp xs0 _ _ _ _ _); [eassumption |]
  end.

Ltac fvs := cbn [fv fset dset wset cpush wpush fld_eqb hcls db hwl wl] in *.

Lemma nth_error_nth_eq (xs : list nat) i x : nth_error xs i = Some x -> x = nth i xs 0.
Proof. intros H. symmetry. now apply nth_error_nth. Qed.

Lemma nth_error_lt {A} (xs : list A) i x : nth_error xs i = Some x -> i < length xs.
Proof. intros H. apply nth_error_Some. congruence. Qed.

(** ** Readers *)

Lemma lit_value_sp h st l Q :
  R h st -> (lvar l < length (asg st) -> Q (lval (asg st) l) h) -> wp (lit_value s l) Q h.
Proof.
  intros Hr HQ. unfold lit_value. ev. ev. intros a Ha. cbv beta. ev.
  pose proof (nth_error_lt _ _ _ Ha) as Hlt. apply nth_error_nth_eq in Ha. subst a.
  apply HQ, Hlt.
Qed.

Lemma enqueue_sp h st l r Q :
  R h st ->
  (forall h', lvar l < length (asg st) -> lvar l < length (lvl st) -> lvar l < length (rsn st) ->
     R h' (enq st l r) -> keeps st h h' -> Q tt h') ->
  wp (enqueue s l r) Q h.
Proof.
  intros Hr HQ. unfold enqueue, decision_level. cbv zeta.
  ev. ev. intros h1 Hi1 Hr1 Hk1. ev. ev. ev. ev. intros h2 Hi2 Hr2 Hk2. ev. ev. intros h3 Hi3 Hr3 Hk3.
  ev. intros h4 Hr4 Hk4. fvs.
  apply HQ; try assumption.
  eapply keeps_trans; [exact Hk1|]. eapply keeps_trans; [exact Hk2|]. eapply keeps_trans; eassumption.
Qed.

Lemma find_watch_sp fuel : forall h st ci c cl k Q,
  R h st -> nth_error (hcls st) ci = Some c -> nth_error (db st) ci = Some cl ->
  (forall r, (r = 0 -> forall j, k <= j < length cl -> lval (asg st) (nth j cl 0) = 2) ->
             (r <> 0 -> k <= r - 1 < length cl /\ lval (asg st) (nth (r - 1) cl 0) <> 2) -> Q r h) ->
  wp (find_watch s fuel c k (length cl)) Q h.
Proof.
  induction fuel as [|f IH]; intros h st ci c cl k Q Hr Hc Hd HQ; cbn [find_watch].
  - apply wp_vabort.
  - destruct (Nat.leb_spec (length cl) k).
    + apply wp_ret, HQ; intros; lia.
    + ev. eapply (get_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd |]. intros x Hx.
      apply nth_error_nth_eq in Hx. subst x.
      ev. eapply lit_value_sp; [exact Hr|]. intros _. cbv beta.
      destruct (Nat.eqb_spec (lval (asg st) (nth k cl 0)) 2) as [E | E].
      * eapply IH; [exact Hr | exact Hc | exact Hd |]. intros r H0 H1. apply HQ.
        -- intros -> j Hj. destruct (Nat.eq_dec j k) as [-> | Hne]; [exact E|]. apply H0; auto; lia.
        -- intros Hr0. specialize (H1 Hr0). lia.
      * apply wp_ret, HQ; [lia|]. intros _. replace (k + 1 - 1) with k by lia. split; [lia | exact E].
Qed.

Lemma copy_rest_sp fuel : forall h st fl ws L i j n Q,
  R h st -> nth_error (hwl st) fl = Some ws -> nth_error (wl st) fl = Some L -> length L = n -> j <= i ->
  (forall h', R h' (wset st (lset (wl st) fl (firstn j L ++ skipn i L))) -> Q tt h') ->
  wp (copy_rest fuel ws i j n) Q h.
Proof.
  induction fuel as [|f IH]; intros h st fl ws L i j n Q Hr Hw HL Hn Hji HQ; cbn [copy_rest].
  - apply wp_vabort.
  - destruct (Nat.leb_spec n i).
    + eapply (shrink_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL |]. intros h' _ Hr' _.
      apply HQ. rewrite (skipn_all2 L) by lia. now rewrite app_nil_r.
    + ev. eapply (get_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL |]. intros x Hx.
      ev. eapply (set_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL |]. intros h1 Hj Hr1 _.
      assert (Hfl : fl < length (wl st)) by (eapply nth_error_lt; eauto).
      eapply IH; [exact Hr1 | exact Hw | fvs; now apply nth_error_lset_eq | now rewrite lset_length | lia |].
      intros h' Hr'. apply HQ. fvs. rewrite lset_lset, !Nat.add_1_r, keep_step in Hr' by (auto; lia).
      exact Hr'.
Qed.

Lemma prop_watch_sp fuel : forall h st fl ws L i j n Q,
  R h st -> nth_error (hwl st) fl = Some ws -> nth_error (wl st) fl = Some L -> length L = n -> j <= i ->
  Core val st -> Wch (db st) (lset (wl st) fl (firstn j L ++ skipn i L)) -> Seen0 st ->
  lval (asg st) fl = 2 -> cur_lit st fl ->
  (forall r h' st', R h' st' -> Inv val st' -> (r = 0 \/ conflict st' r) -> Q r h') ->
  wp (prop_watch s fuel fl ws i j n) Q h.
Proof.
  induction fuel as [|f IH]; intros h st fl ws L i j n Q Hr Hw HL Hn Hji C W S0 Hfl Hcur HQ;
    cbn [prop_watch].
  { apply wp_vabort. }
  assert (Hflw : fl < length (wl st)) by (eapply nth_error_lt; eauto).
  destruct (Nat.leb_spec n i).
  { (* the end of the list *)
    ev. eapply (shrink_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL |]. intros h' _ Hr' _.
    apply wp_ret. apply (HQ 0 h' _ Hr'); [|now left].
    rewrite (skipn_all2 L), app_nil_r in W by lia.
    split; [now apply core_wset | split; [exact W | exact S0]]. }
  ev. eapply (get_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL |]. intros ci Hci.
  ev. ev. intros c Hc.
  destruct (repr_cl s inp xs0 h st ci c Hr Hc) as (cl & Hd & _).
  assert (Hcid : ci < length (db st)) by (eapply nth_error_lt; eauto).
  assert (Hci_in : In ci (nth fl (lset (wl st) fl (firstn j L ++ skipn i L)) [])).
  { rewrite nth_lset, Nat.eqb_refl. destruct (Nat.ltb_spec fl (length (wl st))); [|lia].
    apply in_or_app. right. rewrite (skipn_nth_error L i ci Hci). now left. }
  destruct (wch_in _ _ fl ci W ltac:(rewrite lset_length; lia) Hci_in) as (cl' & Hd' & Hlen & H01).
  rewrite Hd in Hd'. injection Hd' as <-.
  ev. eapply (get_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd |]. intros c0 Hc0.
  apply nth_error_nth_eq in Hc0. subst c0.
  (* Afterwards [c[1] = fl], whichever way the first test went. *)
  eapply wp_seq with (P := fun _ h1 => exists cl1,
    R h1 (dset st (lset (db st) ci cl1)) /\ Core val (dset st (lset (db st) ci cl1)) /\
    Wch (lset (db st) ci cl1) (lset (wl st) fl (firstn j L ++ skipn i L)) /\
    length cl1 = length cl /\ nth 1 cl1 0 = fl).
  { destruct (Nat.eqb_spec (nth 0 cl 0) fl) as [E0 | Hne].
    - ev. eapply (get_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd |]. intros c1 Hc1.
      apply nth_error_nth_eq in Hc1. subst c1.
      ev. eapply (set_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd |]. intros h1 _ Hr1 _.
      eapply (set_cl s inp xs0 h1 _ Hr1 ci c); [exact Hc | fvs; now apply nth_error_lset_eq |].
      intros h2 _ Hr2 _. fvs. rewrite lset_lset in Hr2.
      exists (lset (lset cl 0 (nth 1 cl 0)) 1 fl). split; [exact Hr2|].
      split; [|split; [|split]].
      + eapply core_dset; [exact C | exact Hd | rewrite <- E0; apply perm_swap; lia |].
        eapply not_reason; [exact C | exact Hd |]. intros x Hx.
        rewrite (nth_error_nth' cl 0 x 0 Hx) in E0. subst x. lia.
      + eapply wch_same_expect; [exact W | exact Hd |]. intros l. rewrite <- E0. now apply expect_swap01.
      + now rewrite !lset_length.
      + rewrite nth_lset, lset_length. cbn [Nat.eqb]. destruct (Nat.ltb_spec 1 (length cl)); [reflexivity | lia].
    - apply wp_ret. exists cl. rewrite (lset_same _ _ _ Hd), dset_id.
      split; [exact Hr|]. split; [exact C|]. split; [exact W|]. split; [reflexivity|]. tauto. }
  intros _ h1 (cl1 & Hr1 & C1 & W1 & Hlen1 & H11).
  set (st1 := dset st (lset (db st) ci cl1)) in *.
  assert (Hd1 : nth_error (db st1) ci = Some cl1) by (now apply nth_error_lset_eq).
  ev. eapply (get_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc | exact Hd1 |]. intros first Hfirst.
  ev. eapply lit_value_sp; [exact Hr1 |]. intros _. cbv beta. fold st1.
  set (fv1 := lval (asg st1) first).
  assert (Hfv : fv1 <= 2) by apply (asg_lval_le2 val st1 C1).
  (* Keeping [ci] in the list of [fl]: the logical list does not change. *)
  assert (Keep : forall h2 st2, R h2 (wset st2 (lset (wl st2) fl (lset L j ci))) ->
                  wl st2 = wl st -> hwl st2 = hwl st -> j < length L ->
                  nth_error (wl (wset st2 (lset (wl st2) fl (lset L j ci)))) fl = Some (lset L j ci) /\
                  lset (wl (wset st2 (lset (wl st2) fl (lset L j ci)))) fl
                    (firstn (j + 1) (lset L j ci) ++ skipn (i + 1) (lset L j ci)) =
                  lset (wl st) fl (firstn j L ++ skipn i L)).
  { intros h2 st2 _ Ew _ Hj. fvs. rewrite Ew. split.
    - now apply nth_error_lset_eq.
    - rewrite lset_lset, !Nat.add_1_r, keep_step; auto. }
  destruct (Nat.eqb_spec fv1 1) as [Etrue | Hnt].
  { (* satisfied: keep watching *)
    ev. eapply (set_w s inp xs0 h1 st1 Hr1 fl ws L); [exact Hw | exact HL |]. intros h2 Hj Hr2 _.
    destruct (Keep h2 st1 Hr2 eq_refl eq_refl Hj) as [HL2 Hlog].
    eapply IH; [exact Hr2 | exact Hw | exact HL2 | now rewrite lset_length | lia | now apply core_wset | | | | |].
    - rewrite Hlog. exact W1.
    - exact S0.
    - exact Hfl.
    - exact Hcur.
    - exact HQ. }
  ev. eapply (len_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc | exact Hd1 |].
  ev. eapply find_watch_sp; [exact Hr1 | exact Hc | exact Hd1 |]. intros k1 Hk0 Hk1.
  destruct (Nat.eqb_spec k1 0) as [-> | Hk1nz].
  { (* no other literal to watch: unit or conflict *)
    specialize (Hk0 eq_refl).
    assert (Hrest : forall p, 1 <= p < length cl1 -> lval (asg st1) (nth p cl1 0) = 2).
    { intros p Hp. destruct (Nat.eq_dec p 1) as [-> | ?]; [rewrite H11; exact Hfl | apply Hk0; lia]. }
    ev. eapply (set_w s inp xs0 h1 st1 Hr1 fl ws L); [exact Hw | exact HL |]. intros h2 Hj Hr2 _.
    destruct (Keep h2 st1 Hr2 eq_refl eq_refl Hj) as [HL2 Hlog].
    set (st2 := wset st1 (lset (wl st1) fl (lset L j ci))) in *.
    destruct (Nat.eqb_spec fv1 2) as [Efalse | Hnf].
    - (* conflict *)
      ev. eapply copy_rest_sp; [exact Hr2 | exact Hw | exact HL2 | now rewrite lset_length | lia |].
      intros h3 Hr3. rewrite Hlog in Hr3. apply wp_ret.
      apply (HQ _ h3 _ Hr3).
      + split; [now apply core_wset, core_wset | split; [exact W1 | exact S0]].
      + right. exists ci, cl1. split; [lia|]. split; [exact Hd1|]. split.
        * rewrite <- (skipn_O cl1). apply all_false_cl. intros p Hp.
          destruct p as [|p]; [|apply Hrest; lia].
          rewrite (nth_error_nth' cl1 0 first 0 Hfirst). exact Efalse.
        * apply Exists_exists. exists fl. split; [rewrite <- H11; apply nth_In; lia | exact Hcur].
    - (* unit: propagate [first] *)
      assert (Hfv0 : fv1 = 0) by lia.
      ev. eapply enqueue_sp; [exact Hr2 |]. intros h3 Ha3 Hl3 Hr3' Hr3 _.
      assert (Hvne : lvar fl <> lvar first).
      { intros E. unfold fv1 in Hfv0. rewrite <- (lval_ext (asg st1) (asg st) first) in Hfv0 by reflexivity.
        assert (lval (asg st) fl <> 0) by lia.
        pose proof (i_asg _ _ C (lvar fl)). pose proof (i_asg _ _ C (lvar first)).
        apply (lval_zero _ _ ltac:(eauto)) in Hfv0. rewrite <- E in Hfv0.
        apply (lval_zero _ fl ltac:(eauto)) in Hfv0. lia. }
      eapply IH; [exact Hr3 | exact Hw | exact HL2 | now rewrite lset_length | lia | | | | | |].
      + apply core_enq; auto.
        * apply core_wset. exact C1.
        * intros; lia.
        * intros ci' E. assert (ci' = ci) as -> by lia. exists cl1. split; [exact Hd1|].
          split; [exact Hfirst|]. rewrite tl_skipn1. apply all_false_cl. exact Hrest.
        * intros H0. eapply unit_true; [exact C1 | exact Hd1 | exact H0 | exact Hfirst | exact Hrest].
      + unfold enq. fvs. rewrite Hlog. exact W1.
      + exact S0.
      + unfold enq. fvs. rewrite lval_lset_neq by auto. exact Hfl.
      + destruct Hcur as (k & Hk & Hlim). exists k. unfold enq. fvs. split; [now apply at_pos_snoc | exact Hlim].
      + exact HQ. }
  (* another literal to watch: move [ci] to the list of [ck] *)
  destruct (Hk1 Hk1nz) as [Hkr Hck2]. cbv zeta.
  set (k := k1 - 1) in *.
  ev. eapply (get_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc | exact Hd1 |]. intros ck Hck.
  apply nth_error_nth_eq in Hck. subst ck.
  ev. eapply (set_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc | exact Hd1 |]. intros h2 _ Hr2 _.
  ev. eapply (set_cl s inp xs0 h2 _ Hr2 ci c);
    [exact Hc | unfold st1; fvs; apply nth_error_lset_eq; rewrite lset_length; lia |].
  intros h3 _ Hr3 _. unfold st1 in Hr3. fvs. rewrite !lset_lset in Hr3.
  set (cl2 := lset (lset cl1 1 (nth k cl1 0)) k fl) in *.
  set (st3 := dset st (lset (db st) ci cl2)) in *.
  assert (Hckfl : nth k cl1 0 <> fl) by (intros E; rewrite E in Hck2; contradiction).
  ev. ev. intros w Hw'.
  destruct (repr_w s inp xs0 h3 st3 _ w Hr3 Hw') as (Wck & HWck & _).
  ev. eapply (push_w s inp xs0 h3 st3 Hr3 (nth k cl1 0) w Wck); [exact Hw' | exact HWck |]. intros h4 Hr4 _.
  set (st4 := wset st3 (lset (wl st3) (nth k cl1 0) (Wck ++ [ci]))) in *.
  assert (Hckw : nth k cl1 0 < length (wl st)) by (eapply nth_error_lt; eauto).
  eapply IH; [exact Hr4 | exact Hw | | exact Hn | lia | | | | | |].
  - unfold st4. fvs. rewrite nth_error_lset_neq by auto. exact HL.
  - apply core_wset. eapply core_dset in C1; [| exact Hd1 | |].
    + unfold st1 in C1. fvs. rewrite lset_lset in C1. exact C1.
    + unfold cl2. rewrite <- H11. apply perm_swap; lia.
    + eapply not_reason; [exact C1 | exact Hd1 |]. intros x Hx.
      rewrite Hfirst in Hx. injection Hx as <-. exact Hnt.
  - unfold st4, st3. fvs. rewrite Nat.add_1_r. eapply wch_rehome; eauto.
    + intros l. rewrite <- H11. unfold cl2. rewrite <- H11. apply expect_swap1k. lia.
  - exact S0.
  - exact Hfl.
  - exact Hcur.
  - exact HQ.
Qed.

Lemma propagate_sp fuel : forall h st Q,
  R h st -> Inv val st ->
  (forall r h' st', R h' st' -> Inv val st' ->
     (r = 0 -> length (tr st') <= qhead st') -> (r <> 0 -> conflict st' r) -> Q r h') ->
  wp (propagate s fuel) Q h.
Proof.
  induction fuel as [|f IH]; intros h st Q Hr (C & W & S0) HQ; cbn [propagate].
  { apply wp_vabort. }
  ev. ev. intros qh Hqh. apply nth_error_nth_eq in Hqh.
  ev. ev. destruct (Nat.leb_spec (length (tr st)) qh).
  { apply wp_ret. apply (HQ 0 h st Hr); [split; auto | intros; subst; lia | lia]. }
  ev. ev. intros p Hp.
  ev. ev. intros h1 Hq1 Hr1 _. cbv zeta.
  ev. ev. intros ws Hws.
  destruct (repr_w s inp xs0 h1 _ _ ws Hr1 Hws) as (L & HL & _).
  ev. eapply (len_w s inp xs0 h1 _ Hr1 (lneg p) ws L); [exact Hws | exact HL |].
  assert (Hpin : In p (tr st)) by (eapply nth_error_In; eauto).
  ev. eapply prop_watch_sp; [exact Hr1 | exact Hws | exact HL | reflexivity | lia | | | | | |].
  - apply core_fset_misc; [exact C|]. unfold QHEAD in *. rewrite nth_lset. cbn [Nat.eqb].
    destruct (Nat.ltb_spec 0 (length (fv st FMisc))); [|lia]. rewrite <- Hqh. lia.
  - fvs. rewrite firstn_O, skipn_O. cbn [app]. rewrite (lset_same _ _ _ HL). exact W.
  - exact S0.
  - fvs. now apply (lneg_trail_false val st).
  - exists qh. fvs. split.
    + exists p. split; [exact Hp | symmetry; apply lvar_lneg].
    + rewrite Hqh. apply (i_limq _ _ C).
  - intros confl h2 st2 Hr2 I2 Hc. destruct (Nat.eqb_spec confl 0) as [-> | Hne].
    + eapply IH; [exact Hr2 | exact I2 | exact HQ].
    + apply wp_ret. apply (HQ _ _ _ Hr2 I2); [lia|]. intros _. destruct Hc; [lia | assumption].
Qed.

(** What [unassign] leaves: the variables of [seg] unassigned, and only
    [assigns], [reason] and [phase] written. *)
Definition unas (st st' : astate) (seg : list nat) : Prop :=
  hcls st' = hcls st /\ db st' = db st /\ hwl st' = hwl st /\ wl st' = wl st /\
  (forall f, f <> FAsg -> f <> FRsn -> f <> FPh -> fv st' f = fv st f) /\
  (forall w, In w seg -> nth w (asg st') 0 = 0) /\
  (forall w, ~ In w seg -> nth w (asg st') 0 = nth w (asg st) 0) /\
  (forall w, ~ In w seg -> nth w (rsn st') 0 = nth w (rsn st) 0).

Lemma unassign_sp fuel : forall h st i m Q,
  R h st -> i <= length (tr st) -> m <= i ->
  (forall h' st', R h' st' -> keeps st h h' -> unas st st' (map lvar (skipn m (firstn i (tr st)))) -> Q tt h') ->
  wp (unassign s fuel i m) Q h.
Proof.
  induction fuel as [|f IH]; intros h st i m Q Hr Hi Hm HQ; cbn [unassign].
  { apply wp_vabort. }
  destruct (Nat.leb_spec i m).
  { apply wp_ret. apply (HQ h st Hr (keeps_refl _ _ _ _)).
    assert (i = m) as -> by lia. rewrite skipn_all2 by (rewrite length_firstn; lia).
    repeat split; auto; intros w []. }
  ev. ev. intros l Hl. cbv zeta.
  ev. ev. intros a Ha.
  ev. ev. intros h1 Hp1 Hr1 Hk1.
  ev. ev. intros h2 Ha2 Hr2 Hk2.
  ev. ev. intros h3 Hrs3 Hr3 Hk3. fvs.
  eapply IH; [exact Hr3 | fvs; lia | lia |]. intros h' st' Hr' Hk' (E1 & E2 & E3 & E4 & Ef & Az & Ak & Rk).
  apply (HQ h' st' Hr').
  { eapply keeps_trans; [exact Hk1|]. eapply keeps_trans; [exact Hk2|]. eapply keeps_trans; eassumption. }
  fvs.
  assert (Hseg : map lvar (skipn m (firstn i (tr st))) = map lvar (skipn m (firstn (i - 1) (tr st))) ++ [lvar l]).
  { replace i with (S (i - 1)) at 1 by lia. rewrite (firstn_S_snoc _ _ _ Hl), skipn_snoc, map_app; [reflexivity|].
    rewrite length_firstn. lia. }
  rewrite Hseg. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  split; [|split; [|split]].
  - intros g H1 H2 H3. rewrite Ef by auto. destruct g; try reflexivity; congruence.
  - intros w Hw. apply in_app_or in Hw as [Hw | [<- | []]].
    + now apply Az.
    + destruct (in_dec Nat.eq_dec (lvar l) (map lvar (skipn m (firstn (i - 1) (tr st))))) as [Hin | Hin].
      * now apply Az.
      * rewrite Ak by exact Hin. fvs. rewrite nth_lset, Nat.eqb_refl.
        now destruct (Nat.ltb_spec (lvar l) (length (asg st))).
  - intros w Hw. rewrite Ak by (intros Hx; apply Hw, in_or_app; auto). fvs.
    rewrite nth_lset. destruct (Nat.eqb_spec (lvar l) w) as [E | _]; [|reflexivity].
    exfalso. apply Hw, in_or_app. right. now left.
  - intros w Hw. rewrite Rk by (intros Hx; apply Hw, in_or_app; auto). fvs.
    rewrite nth_lset. destruct (Nat.eqb_spec (lvar l) w) as [E | _]; [|reflexivity].
    exfalso. apply Hw, in_or_app. right. now left.
Qed.

Lemma backtrack_sp fuel h st lv Q :
  R h st -> Inv val st ->
  (forall h' st', R h' st' -> keeps st h h' -> Inv val st' ->
     hcls st' = hcls st -> hwl st' = hwl st -> db st' = db st ->
     (lv < length (lim st) -> bt_rel st st' lv) -> Q tt h') ->
  wp (backtrack s fuel lv) Q h.
Proof.
  intros Hr (C & W & S0) HQ. unfold backtrack, decision_level.
  ev. ev. destruct (Nat.leb_spec (length (lim st)) lv).
  { apply wp_ret. apply (HQ h st Hr (keeps_refl _ _ _ _)); auto; [split; auto | intros; lia]. }
  ev. ev. intros m Hm. apply nth_error_nth_eq in Hm.
  ev. ev.
  assert (Hmq : m <= length (tr st)).
  { pose proof (i_limq _ _ C) as F. rewrite Forall_forall in F.
    pose proof (F m ltac:(rewrite Hm; apply nth_In; lia)). pose proof (i_qtr _ _ C). lia. }
  ev. eapply unassign_sp; [exact Hr | lia | exact Hmq |].
  intros h1 st1 Hr1 Hk1 (E1 & E2 & E3 & E4 & Ef & Az & Ak & Rk).
  rewrite firstn_all in Az, Ak, Rk.
  ev. ev. intros h2 Hm2 Hr2 Hk2.
  ev. ev. intros h3 Hl3 Hr3 Hk3.
  ev. intros h4 Hq4 Hr4 Hk4. fvs.
  set (st4 := fset (fset (fset st1 FTr (firstn m (fv st1 FTr))) FLim (firstn lv (fv st1 FLim)))
                FMisc (lset (fv st1 FMisc) QHEAD m)) in *.
  assert (Hbt : bt_rel st st4 lv).
  { unfold bt_rel, st4. cbv zeta. rewrite <- Hm. fvs.
    rewrite (Ef FTr), (Ef FLim), (Ef FMisc), (Ef FLvl) by discriminate.
    split; [exact E2|]. split; [exact Az|]. split; [exact Ak|]. split; [reflexivity|].
    split; [exact Rk|]. split; [reflexivity|]. split; [reflexivity|].
    unfold QHEAD. rewrite nth_lset. cbn [Nat.eqb]. rewrite (Ef FMisc) in Hq4 by discriminate.
    destruct (Nat.ltb_spec 0 (length (fv st FMisc))); [reflexivity | unfold QHEAD in Hq4; lia]. }
  apply (HQ h4 st4 Hr4).
  - eapply keeps_trans; [exact Hk1|]. apply (keeps_eq st st1); [exact E1 | exact E3 |].
    eapply keeps_trans; [exact Hk2|]. eapply keeps_trans; eassumption.
  - split; [eapply core_bt; eauto |]. split.
    + unfold st4. fvs. rewrite E2, E4. exact W.
    + intros v. unfold st4. fvs. rewrite (Ef FSn) by discriminate. apply S0.
  - unfold st4. fvs. exact E1.
  - unfold st4. fvs. exact E3.
  - unfold st4. fvs. exact E2.
  - intros _. exact Hbt.
Qed.
End Spec.
