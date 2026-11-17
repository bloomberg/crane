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
        rewrite (nth_of_error cl 0 x 0 Hx) in E0. subst x. lia.
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
          rewrite (nth_of_error cl1 0 first 0 Hfirst). exact Efalse.
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

(** ** First-UIP analysis *)

(** A state that differs from [st0] only in the marks and the stamps. *)
Definition only_sn (st0 st : astate) : Prop :=
  hcls st = hcls st0 /\ db st = db st0 /\ hwl st = hwl st0 /\ wl st = wl st0 /\
  (forall f, f <> FSn -> f <> FSt -> fv st f = fv st0 f).

Lemma only_sn_refl st : only_sn st st.
Proof. repeat split; auto. Qed.

Lemma only_sn_fset st0 st f xs : f = FSn \/ f = FSt -> only_sn st0 st -> only_sn st0 (fset st f xs).
Proof.
  intros Hf (E1 & E2 & E3 & E4 & Ef). repeat split; auto. intros g H1 H2. cbn.
  destruct (fld_eqb g f) eqn:E; [apply fld_eqb_eq in E; subst; destruct Hf; congruence | auto].
Qed.

Section Analyze.
Variables (st0 : astate) (learnt : vec nat) (now : nat).
Hypotheses (C0 : Core val st0) (Hne0 : lim st0 <> []) (Hfresh : ~ In (vloc learnt) (locs s inp st0)).

Lemma learnt_kept st h h' Lr : only_sn st0 st -> keeps st h h' -> pts h learnt Lr -> pts h' learnt Lr.
Proof.
  intros (E1 & _ & E3 & _) Hk Hp. apply Hk; [|exact Hp]. now rewrite (locs_eq st0 st E1 E3).
Qed.

Lemma analyze_lits_sp fuel : forall h stc ci c cl j pathC Lr index Q,
  R h stc -> only_sn st0 stc -> nth_error (hcls st0) ci = Some c -> nth_error (db st0) ci = Some cl ->
  pts h learnt Lr -> AInv st0 (sn stc) Lr index pathC ->
  (forall p, j <= p < length cl -> lval (asg st0) (nth p cl 0) = 2 /\
                                    exists k, at_pos (tr st0) k (lvar (nth p cl 0)) /\ k <= index) ->
  (forall r h' stc' Lr', R h' stc' -> only_sn st0 stc' -> pts h' learnt Lr' -> AInv st0 (sn stc') Lr' index r ->
     (forall u, marked (sn stc) u -> marked (sn stc') u) ->
     (forall p, j <= p < length cl -> 0 < nth (lvar (nth p cl 0)) (lvl st0) 0 ->
                marked (sn stc') (lvar (nth p cl 0))) ->
     Q r h') ->
  wp (analyze_lits s fuel c j (length cl) (length (lim st0)) pathC learnt now) Q h.
Proof.
  induction fuel as [|f IH]; intros h stc ci c cl j pathC Lr index Q Hr Hos Hc Hd Hp A Hpend HQ;
    cbn [analyze_lits].
  { apply wp_vabort. }
  destruct (Nat.leb_spec (length cl) j).
  { apply wp_ret. apply (HQ pathC h stc Lr Hr Hos Hp A); [auto | intros; lia]. }
  pose proof Hos as (E1 & E2 & E3 & E4 & Ef).
  ev. eapply (get_cl s inp xs0 h stc Hr ci c cl); [now rewrite E1 | now rewrite E2 |]. intros q Hq.
  apply nth_error_nth_eq in Hq. subst q. cbv zeta.
  set (q := nth j cl 0) in *.
  destruct (Hpend j ltac:(lia)) as [Hqf (k & Hk & Hki)].
  assert (Hlv : nth (lvar q) (lvl st0) 0 = count_le (lim st0) k) by (eapply lvl_at; eauto).
  ev. ev. intros sv Hsv. pose proof (nth_error_lt _ _ _ Hsv) as Hvlen. apply nth_error_nth_eq in Hsv. subst sv.
  ev. ev. intros lv Hlv'. apply nth_error_nth_eq in Hlv'. subst lv. rewrite (Ef FLvl) by discriminate.
  rewrite Hlv.
  (* every later step keeps the marks this one leaves, so the first literal's obligation is met *)
  assert (Hrest : forall h1 stc1 Lr1 pathC1, R h1 stc1 -> only_sn st0 stc1 -> pts h1 learnt Lr1 ->
            AInv st0 (sn stc1) Lr1 index pathC1 -> (forall u, marked (sn stc) u -> marked (sn stc1) u) ->
            (0 < count_le (lim st0) k -> marked (sn stc1) (lvar q)) ->
            wp (analyze_lits s f c (j + 1) (length cl) (length (lim st0)) pathC1 learnt now) Q h1).
  { intros h1 stc1 Lr1 pathC1 Hr1 Hos1 Hp1 A1 Hmono1 Hq1.
    eapply IH; [exact Hr1 | exact Hos1 | exact Hc | exact Hd | exact Hp1 | exact A1 | |].
    - intros p' Hp'. apply Hpend. lia.
    - intros r h' stc' Lr' Hr' Hos' Hp' A' Hmono' Hpend'. apply (HQ r h' stc' Lr' Hr' Hos' Hp' A').
      + intros u Hu. auto.
      + intros p' Hp'' Hlvp. destruct (Nat.eq_dec p' j) as [-> | Hne].
        * apply Hmono'. apply Hq1. fold q in Hlvp. lia.
        * apply Hpend'; [lia | exact Hlvp]. }
  destruct (Nat.eqb_spec (nth (lvar q) (sn stc) 0) 0) as [Hs0 | Hs0];
    destruct (Nat.ltb_spec 0 (count_le (lim st0) k)) as [Hl0 | Hl0]; cbn [andb].
  - (* a new mark *)
    ev. ev. intros h1 _ Hr1 Hk1.
    ev. ev. intros h2 _ Hr2 Hk2.
    assert (Hos2 : only_sn st0 (fset (fset stc FSn (lset (fv stc FSn) (lvar q) 1)) FSt
                     (lset (fv (fset stc FSn (lset (fv stc FSn) (lvar q) 1)) FSt) (lvar q) now)))
      by (apply only_sn_fset; [auto|]; apply only_sn_fset; auto).
    assert (Hp2 : pts h2 learnt Lr).
    { eapply learnt_kept; [| exact Hk2 |]; [apply only_sn_fset; auto|].
      exact (learnt_kept stc h h1 Lr Hos Hk1 Hp). }
    assert (Hnm : ~ marked (sn stc) (lvar q)) by (unfold marked; lia).
    assert (Hmono : forall u, marked (sn stc) u -> marked (lset (sn stc) (lvar q) 1) u)
      by (intros; now apply marked_mono1).
    assert (Hqm : marked (lset (sn stc) (lvar q) 1) (lvar q))
      by (apply marked_lset; [exact Hvlen | rewrite Nat.eqb_refl; lia]).
    destruct (Nat.leb_spec (length (lim st0)) (count_le (lim st0) k)) as [Hcur | Hlow].
    + (* current level: one more path *)
      pose proof (count_le_max (lim st0) k).
      assert (Hbk : base st0 <= k) by (apply (cur_iff val st0 C0 Hne0); lia).
      eapply Hrest; [exact Hr2 | exact Hos2 | exact Hp2 | | | ].
      * fvs. rewrite Nat.add_1_r. eapply ainv_mark_cur; eauto.
      * fvs. exact Hmono.
      * fvs. intros _. exact Hqm.
    + (* lower level: into the learnt clause *)
      ev. eapply (push_scr s inp xs0 h2 _ Hr2 learnt Lr q); [rewrite (locs_eq st0); destruct Hos2 as (? & _ & ? & _); auto | exact Hp2 |].
      intros h3 Hr3 Hp3 _.
      eapply Hrest; [exact Hr3 | exact Hos2 | exact Hp3 | | | ].
      * fvs. eapply ainv_mark_low; eauto.
      * fvs. exact Hmono.
      * fvs. intros _. exact Hqm.
  - (* level 0: nothing to do *)
    eapply Hrest; [exact Hr | exact Hos | exact Hp | exact A | auto | intros; lia].
  - (* already marked *)
    eapply Hrest; [exact Hr | exact Hos | exact Hp | exact A | auto | intros _; exact Hs0].
  - eapply Hrest; [exact Hr | exact Hos | exact Hp | exact A | auto | intros; lia].
Qed.


Lemma next_seen_sp fuel : forall h stc i Q,
  R h stc -> only_sn st0 stc -> i < length (tr st0) ->
  (exists k, base st0 <= k <= i /\ marked (sn stc) (lvar (nth k (tr st0) 0))) ->
  (forall idx, base st0 <= idx <= i -> marked (sn stc) (lvar (nth idx (tr st0) 0)) ->
     (forall k, idx < k <= i -> ~ marked (sn stc) (lvar (nth k (tr st0) 0))) -> Q idx h) ->
  wp (next_seen s fuel i) Q h.
Proof.
  induction fuel as [|f IH]; intros h stc i Q Hr Hos Hi Hex HQ; cbn [next_seen].
  { apply wp_vabort. }
  pose proof Hos as (_ & _ & _ & _ & Ef).
  ev. ev. intros l Hl. apply nth_error_nth_eq in Hl. subst l. rewrite (Ef FTr) by discriminate.
  ev. ev. intros sv Hsv. apply nth_error_nth_eq in Hsv. subst sv.
  destruct (Nat.eqb_spec (nth (lvar (nth i (tr st0) 0)) (sn stc) 0) 0) as [E | E].
  - destruct Hex as (k & Hk & Hm).
    assert (Hki : k <> i) by (intros ->; unfold marked in Hm; lia).
    eapply IH; [exact Hr | exact Hos | lia | exists k; split; [lia | exact Hm] |].
    intros idx Hidx Hmi Hnone. apply HQ; [lia | exact Hmi |].
    intros k' Hk'. destruct (Nat.eq_dec k' i) as [-> | ?]; [unfold marked; lia | apply Hnone; lia].
  - apply wp_ret. destruct Hex as (k & Hk & _). apply HQ; [lia | exact E | intros; lia].
Qed.

Lemma analyze_loop_sp fuel : forall h stc confl cl start index pathC Lr Q,
  R h stc -> only_sn st0 stc -> nth_error (db st0) confl = Some cl -> pts h learnt Lr ->
  AInv st0 (sn stc) Lr index pathC ->
  (forall p, start <= p < length cl -> lval (asg st0) (nth p cl 0) = 2 /\
                                       exists k, at_pos (tr st0) k (lvar (nth p cl 0)) /\ k <= index) ->
  (1 <= pathC \/ exists p k, start <= p < length cl /\ at_pos (tr st0) k (lvar (nth p cl 0)) /\ base st0 <= k) ->
  ((exists u, marked (sn stc) u /\ disagree val (asg st0) u) \/ Exists (lit_true val) (skipn start cl)) ->
  (forall p h' stc' Lr', R h' stc' -> only_sn st0 stc' -> pts h' learnt Lr' ->
     (exists idx, nth_error (tr st0) idx = Some p /\ base st0 <= idx) ->
     (forall u, marked (sn stc') u -> exists q, In q (tl Lr') /\ lvar q = u) ->
     Lr' <> [] ->
     Forall (fun q => lval (asg st0) q = 2 /\ 0 < nth (lvar q) (lvl st0) 0 < length (lim st0)) (tl Lr') ->
     (lit_true val (lneg p) \/ Exists (lit_true val) (tl Lr')) ->
     Q p h') ->
  wp (analyze_loop s fuel confl start index pathC (length (lim st0)) learnt now) Q h.
Proof.
  induction fuel as [|f IH]; intros h stc confl cl start index pathC Lr Q Hr Hos Hd Hp A Hpend Hpath Hsound HQ;
    cbn [analyze_loop].
  { apply wp_vabort. }
  pose proof Hos as (E1 & E2 & E3 & E4 & Ef).
  assert (Hasg : forall u, nth u (asg st0) 0 <= 2) by apply (i_asg _ _ C0).
  ev. ev. intros c Hc. rewrite E1 in Hc.
  ev. eapply (len_cl s inp xs0 h stc Hr confl c cl); [now rewrite E1 | now rewrite E2 |].
  ev. eapply analyze_lits_sp; [exact Hr | exact Hos | exact Hc | exact Hd | exact Hp | exact A | exact Hpend |].
  intros pathC1 h1 stc1 Lr1 Hr1 Hos1 Hp1 A1 Hmono Hmarked.
  pose proof Hos1 as (F1 & F2 & F3 & F4 & Ff).
  (* at least one marked literal at the current level *)
  assert (Hpc1 : 1 <= pathC1).
  { rewrite (a_cnt _ _ _ _ _ A1). destruct Hpath as [Hpc | (p & k & Hp' & Hk & Hbk)].
    - rewrite (a_cnt _ _ _ _ _ A) in Hpc. etransitivity; [exact Hpc | now apply cntm_mono].
    - destruct (Hpend p Hp') as [_ (k' & Hk' & Hk'i)].
      rewrite <- (pos_unique val st0 C0 _ _ _ Hk Hk') in Hk'i.
      apply (cntm_pos _ _ _ _ k); [lia|].
      apply at_pos_nth in Hk as [Hkt Ek]. rewrite Ek. apply Hmarked; [lia|].
      rewrite (lvl_at val st0 C0 k) by (apply at_pos_nth; auto).
      pose proof (proj2 (cur_iff val st0 C0 Hne0 k) Hbk). destruct (lim st0); [congruence | cbn [length] in *; lia]. }
  (* a marked literal [val] disagrees with *)
  assert (Hdis : exists u, marked (sn stc1) u /\ disagree val (asg st0) u).
  { destruct Hsound as [(u & Hu & Hdu) | Hex].
    - exists u. auto.
    - apply Exists_exists in Hex as (q & Hq & Ht). apply in_skipn_nth in Hq as (p & Hp' & <-).
      destruct (Hpend p Hp') as [Hf (k & Hk & _)].
      exists (lvar (nth p cl 0)). split; [|now apply false_true_disagree].
      apply Hmarked; [exact Hp'|]. destruct (Nat.eq_dec (nth (lvar (nth p cl 0)) (lvl st0) 0) 0) as [E0 | ?]; [|lia].
      exfalso. exact (false_l0 val st0 C0 _ Hf E0 Ht). }
  assert (Hidx_ok : index < length (tr st0)) by apply (a_idx _ _ _ _ _ A1).
  ev. eapply next_seen_sp; [exact Hr1 | exact Hos1 | exact Hidx_ok | |].
  { destruct (cntm_exists (tr st0) (sn stc1) (base st0) (S index)) as (k & Hk & Hm);
      [rewrite <- (a_cnt _ _ _ _ _ A1); lia|].
    exists k. split; [lia | exact Hm]. }
  intros idx Hidx Hmi Hnone.
  ev. ev. intros p Hp'. rewrite (Ff FTr) in Hp' by discriminate.
  pose proof (nth_error_lt _ _ _ Hp') as Hidxt.
  pose proof Hp' as Hpn. apply nth_error_nth_eq in Hpn. subst p. cbv zeta.
  set (p := nth idx (tr st0) 0) in *.
  ev. ev. intros r Hrr. apply nth_error_nth_eq in Hrr. subst r. rewrite (Ff FRsn) by discriminate.
  ev. ev. intros h2 Hv2 Hr2 Hk2.
  assert (Hos2 : only_sn st0 (fset stc1 FSn (lset (fv stc1 FSn) (lvar p) 0))) by (apply only_sn_fset; auto).
  assert (Hp2 : pts h2 learnt Lr1) by exact (learnt_kept stc1 h1 h2 Lr1 Hos1 Hk2 Hp1).
  assert (Hptrue : lval (asg st0) p = 1) by (apply (true_on_trail val st0 C0); eapply nth_error_In; eauto).
  destruct (Nat.leb_spec pathC1 1) as [Hle | Hgt].
  - (* the first UIP *)
    apply wp_ret. apply (HQ p h2 _ Lr1 Hr2 Hos2 Hp2).
    + exists idx. split; [exact Hp' | lia].
    + fvs. eapply ainv_final; eauto.
    + apply (a_lr_ne _ _ _ _ _ A1).
    + eapply Forall_impl; [|apply (a_lr _ _ _ _ _ A1)]. intros q (H1 & _ & H3). auto.
    + destruct Hdis as (u & Hu & Hdu). destruct (Nat.eq_dec u (lvar p)) as [-> | Hne].
      * left. eapply true_disagree_false; eauto.
      * right. destruct (ainv_final val st0 C0 Hne0 _ _ _ _ idx A1 ltac:(lia) Hmi Hnone Hle Hv2 u)
          as (q & Hq & Eq).
        { apply marked_lset; [exact Hv2|]. fold p. destruct (Nat.eqb_spec (lvar p) u); [congruence | exact Hu]. }
        apply Exists_exists. exists q. split; [exact Hq|].
        pose proof (proj1 (Forall_forall _ _) (a_lr _ _ _ _ _ A1) q Hq) as (Hqf & _).
        subst u. eapply false_disagree_true; eauto.
  - (* resolve with the reason of [p] *)
    destruct (ainv_pop val st0 C0 Hne0 _ _ _ _ idx A1 ltac:(lia) Hmi Hnone ltac:(lia) Hv2) as [Hb A2].
    pose proof (reason_exists val st0 C0 Hne0 idx Hb Hidxt) as Hrnz.
    destruct (nth (lvar p) (rsn st0) 0) as [|r'] eqn:Er; [contradiction|].
    destruct (i_rsn _ _ C0 idx p r' Hp' Er) as (c' & Hc' & Hc0 & Hrest).
    replace (S r' - 1) with r' by lia.
    eapply IH; [exact Hr2 | exact Hos2 | exact Hc' | exact Hp2 | fvs; exact A2 | | left; lia | | exact HQ].
    + intros p' Hp''. rewrite Forall_forall in Hrest.
      destruct (Hrest (nth p' c' 0) (in_tl_nth c' p' Hp'')) as [Hf (k' & Hk' & Hpos)].
      split; [exact Hf|]. exists k'. split; [exact Hpos | lia].
    + destruct Hdis as (u & Hu & Hdu). destruct (Nat.eq_dec u (lvar p)) as [-> | Hne].
      * right. pose proof (true_disagree_false val _ _ Hptrue Hdu) as Hneg.
        apply lit_true_lneg in Hneg.
        pose proof (Forall_nth_error _ _ _ _ (i_db _ _ C0) Hc') as Hex.
        destruct c' as [|a c']; [discriminate|]. cbn in Hc0. injection Hc0 as ->.
        inversion Hex; subst; [contradiction | cbn; assumption].
      * left. exists u. split; [|exact Hdu]. fvs. apply marked_lset; [exact Hv2|].
        destruct (Nat.eqb_spec (lvar p) u); [congruence | exact Hu].
Qed.


Lemma finish_learnt_sp fuel : forall h stc Lr i best bestlv Q,
  R h stc -> only_sn st0 stc -> pts h learnt Lr -> 1 <= i <= length Lr ->
  (forall k, 1 <= k < i -> nth (lvar (nth k Lr 0)) (lvl st0) 0 <= bestlv) ->
  ((best = 0 /\ bestlv = 0) \/ (1 <= best < i /\ nth (lvar (nth best Lr 0)) (lvl st0) 0 = bestlv)) ->
  (forall u, marked (sn stc) u -> exists k, i <= k < length Lr /\ lvar (nth k Lr 0) = u) ->
  (forall r h' stc' Lr', R h' stc' -> only_sn st0 stc' -> pts h' learnt Lr' ->
     (forall u, nth u (sn stc') 0 = 0) ->
     (exists a t t', Lr = a :: t /\ Lr' = a :: t' /\ Permutation t t') ->
     (forall q, In q (tl Lr) -> nth (lvar q) (lvl st0) 0 <= r) ->
     (r = 0 \/ exists q, In q (tl Lr) /\ nth (lvar q) (lvl st0) 0 = r) ->
     Q r h') ->
  wp (finish_learnt s fuel learnt i (length Lr) best bestlv) Q h.
Proof.
  induction fuel as [|f IH]; intros h stc Lr i best bestlv Q Hr Hos Hp Hi Hle Hbest Hmarks HQ;
    cbn [finish_learnt].
  { apply wp_vabort. }
  pose proof Hos as (E1 & E2 & E3 & E4 & Ef).
  assert (Hfr : ~ In (vloc learnt) (locs s inp stc)) by (now rewrite (locs_eq st0 stc E1 E3)).
  destruct Lr as [|a t]; [cbn in Hi; lia|].
  destruct (Nat.leb_spec (length (a :: t)) i).
  { (* move the deepest literal to position 1 *)
    eapply wp_seq with (P := fun _ h1 => exists t', R h1 stc /\ pts h1 learnt (a :: t') /\ Permutation t t').
    - destruct (Nat.ltb_spec 1 best).
      + destruct Hbest as [[-> _] | [Hb _]]; [lia|].
        ev. eapply wp_get_pts; [exact Hp|]. intros b Hb'.
        ev. eapply wp_get_pts; [exact Hp|]. intros x Hx.
        ev. eapply (set_scr s inp xs0 h stc Hr learnt); [exact Hfr | exact Hp |]. intros h1 _ Hr1 Hp1 _.
        eapply (set_scr s inp xs0 h1 stc Hr1 learnt); [exact Hfr | exact Hp1 |]. intros h2 _ Hr2 Hp2 _.
        exists (lset (lset t 0 b) (best - 1) x). split; [exact Hr2|]. split.
        * destruct best as [|best]; [lia|].
          replace (S best - 1) with best by lia.
          assert (E : lset (lset (a :: t) 1 b) (S best) x = a :: lset (lset t 0 b) best x) by reflexivity.
          exact (eq_rect _ (pts h2 learnt) Hp2 _ E).
        * apply nth_error_nth_eq in Hb'. apply nth_error_nth_eq in Hx. subst b x.
          destruct best as [|best]; [lia|]. replace (S best - 1) with best by lia. cbn [nth].
          assert (best < length t) by (cbn [length] in H, Hi; lia).
          apply perm_swap; lia.
      + apply wp_ret. exists t. split; [exact Hr|]. split; [exact Hp | reflexivity].
    - intros _ h1 (t' & Hr1 & Hp1 & Hperm). apply wp_ret.
      apply (HQ bestlv h1 stc (a :: t') Hr1 Hos Hp1).
      + intros u. destruct (Nat.eq_dec (nth u (sn stc) 0) 0) as [E | E]; [exact E|].
        destruct (Hmarks u E) as (k & Hk & _). lia.
      + exists a, t, t'. auto.
      + intros q Hq. apply In_nth with (d := 0) in Hq as (k & Hk & <-).
        apply (Hle (S k)). cbn [length tl] in Hk, H |- *. lia.
      + destruct Hbest as [[_ ->] | [Hb Hlv]]; [now left|]. right.
        exists (nth best (a :: t) 0). split; [apply in_tl_nth; lia | exact Hlv]. }
  ev. eapply wp_get_pts; [exact Hp|]. intros q Hq. apply nth_error_nth_eq in Hq. subst q. cbv zeta.
  ev. ev. intros h1 Hv1 Hr1 Hk1.
  assert (Hos1 : only_sn st0 (fset stc FSn (lset (sn stc) (lvar (nth i (a :: t) 0)) 0)))
    by (apply only_sn_fset; auto).
  pose proof (learnt_kept stc h h1 _ Hos Hk1 Hp) as Hp1.
  ev. ev. intros lv Hlv. apply nth_error_nth_eq in Hlv. subst lv. fvs. rewrite (Ef FLvl) by discriminate.
  assert (Hmarks1 : forall u, marked (lset (sn stc) (lvar (nth i (a :: t) 0)) 0) u ->
            exists k, i + 1 <= k < length (a :: t) /\ lvar (nth k (a :: t) 0) = u).
  { intros u Hu. apply marked_lset in Hu; [|exact Hv1].
    destruct (Nat.eqb_spec (lvar (nth i (a :: t) 0)) u); [lia|].
    destruct (Hmarks u Hu) as (k & Hk & Ek). exists k. split; [|exact Ek].
    destruct (Nat.eq_dec k i) as [-> | ?]; [congruence | lia]. }
  destruct (Nat.ltb_spec bestlv (nth (lvar (nth i (a :: t) 0)) (lvl st0) 0)).
  - eapply IH; [exact Hr1 | exact Hos1 | exact Hp1 | lia | | | fvs; exact Hmarks1 | exact HQ].
    + intros k Hk. destruct (Nat.eq_dec k i) as [-> | ?]; [lia|]. specialize (Hle k ltac:(lia)). lia.
    + right. split; [lia | reflexivity].
  - eapply IH; [exact Hr1 | exact Hos1 | exact Hp1 | lia | | | fvs; exact Hmarks1 | exact HQ].
    + intros k Hk. destruct (Nat.eq_dec k i) as [-> | ?]; [lia|]. apply Hle. lia.
    + destruct Hbest as [? | [? ?]]; [now left | right; split; [lia | assumption]].
Qed.


End Analyze.

(** ** Learning *)

Lemma attach_sp h st ci c cl Q :
  R h st -> nth_error (hcls st) ci = Some c -> nth_error (db st) ci = Some cl -> 2 <= length cl ->
  Wch (db st) (wl st) -> (forall l, l < length (wl st) -> cnt (wl st) l ci = 0) ->
  (forall h' st', R h' st' -> keeps st h h' -> hcls st' = hcls st -> hwl st' = hwl st -> db st' = db st ->
     (forall f, fv st' f = fv st f) -> Wch (db st') (wl st') -> Q tt h') ->
  wp (attach s ci c) Q h.
Proof.
  intros Hr Hc Hd Hlen W W0 HQ. unfold attach.
  ev. eapply (get_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd |]. intros c0 H0.
  ev. eapply (get_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd |]. intros c1 H1.
  apply nth_error_nth_eq in H0, H1. subst c0 c1.
  assert (He : forall l, expect (db st) ci l = expect_cl cl l) by (intros; now apply expect_nth).
  ev. ev. intros w0 Hw0. destruct (repr_w s inp xs0 h st _ _ Hr Hw0) as (W0l & HW0 & _).
  assert (Ha0 : nth 0 cl 0 < length (wl st)) by (eapply nth_error_lt; eauto).
  ev. eapply (push_w s inp xs0 h st Hr _ w0 W0l); [exact Hw0 | exact HW0 |]. intros h1 Hr1 Hk1.
  ev. ev. intros w1 Hw1. destruct (repr_w s inp xs0 h1 _ _ _ Hr1 Hw1) as (W1l & HW1 & _). fvs.
  assert (Ha1 : nth 1 cl 0 < length (wl st)) by (rewrite <- (lset_length (wl st) (nth 0 cl 0) (W0l ++ [ci])); eapply nth_error_lt; eauto).
  eapply (push_w s inp xs0 h1 _ Hr1 _ w1 W1l); [exact Hw1 | exact HW1 |]. intros h2 Hr2 Hk2.
  apply (HQ h2 _ Hr2); fvs; try reflexivity.
  - eapply keeps_trans; eassumption.
  - assert (W1 : Wch (db st) (lset (wl st) (nth 0 cl 0) (W0l ++ [ci]))).
    { apply wch_push; [exact W | exact HW0 |]. rewrite W0, He by exact Ha0. unfold expect_cl.
      destruct (Nat.leb_spec 2 (length cl)); [|lia]. rewrite Nat.eqb_refl. lia. }
    apply wch_push; [exact W1 | exact HW1 |]. rewrite He. unfold expect_cl.
    destruct (Nat.leb_spec 2 (length cl)); [|lia].
    rewrite cnt_lset by exact Ha0.
    assert (Hc0 : count_occ Nat.eq_dec W0l ci = 0)
      by (pose proof (W0 _ Ha0) as X; unfold cnt in X; now rewrite (nth_of_error _ _ _ [] HW0) in X).
    destruct (Nat.eqb_spec (nth 0 cl 0) (nth 1 cl 0)) as [E | E]; rewrite Nat.eqb_refl.
    + rewrite count_occ_app. cbn [count_occ]. destruct (Nat.eq_dec ci ci); [lia | congruence].
    + rewrite (W0 _ Ha1). lia.
Qed.


Lemma learn_sp fuel h st confl Q :
  R h st -> Inv val st -> conflict st (S confl) -> lim st <> [] ->
  (forall h' st', R h' st' -> Inv val st' -> Q tt h') ->
  wp (learn s fuel confl) Q h.
Proof.
  intros Hr (C & W & S0) Hconf Hne HQ. unfold learn, decision_level.
  destruct Hconf as (ci & cl & Eci & Hd & Hfalse & Hcur). injection Eci as <-.
  assert (Hasg : forall u, nth u (asg st) 0 <= 2) by apply (i_asg _ _ C).
  ev. ev. ev. ev. intros now Hnow.
  ev. eapply (make_scr s inp xs0 h st Hr). intros lr h1 Hfresh Hp1 Hr1 Hk1 _ _. cbn [repeat] in Hp1.
  ev. ev.
  (* the conflict clause has a literal at the current level, so the trail is not empty *)
  destruct (proj1 (Exists_exists _ _) Hcur) as (q0 & Hq0 & (k0 & Hk0 & Hk0lim)).
  assert (Htr : tr st <> []) by (intros E; apply at_pos_lt in Hk0; rewrite E in Hk0; cbn in Hk0; lia).
  ev. eapply (analyze_loop_sp st lr now C Hne Hfresh fuel h1 st confl cl 0 (length (tr st) - 1) 0 [0]);
    [exact Hr1 | apply only_sn_refl | exact Hd | exact Hp1 | | | | |].
  { apply ainv_init; [exact Htr | exact S0]. }
  { intros p Hp. rewrite Forall_forall in Hfalse. pose proof (Hfalse _ (nth_In cl 0 (proj2 Hp))) as Hf.
    split; [exact Hf|]. destruct (false_at_pos val st C _ Hf) as (k & Hk). exists k. split; [exact Hk|].
    pose proof (at_pos_lt _ _ _ Hk). lia. }
  { right. apply In_nth with (d := 0) in Hq0 as (p & Hp & Ep). exists p, k0. split; [lia|].
    rewrite Ep. split; [exact Hk0|]. rewrite Forall_forall in Hk0lim. apply Hk0lim, base_in, Hne. }
  { right. rewrite skipn_O. apply (Forall_nth_error _ _ _ _ (i_db _ _ C) Hd). }
  intros p h2 stc2 Lr1 Hr2 Hos2 Hp2 (idx & Hidx & Hbidx) Hmarks2 Hne1 Hlr1 Hsound. cbv zeta.
  destruct Lr1 as [|a t]; [congruence|]. cbn [tl] in *.
  pose proof Hos2 as (F1 & F2 & F3 & F4 & Ff).
  assert (Hfr2 : ~ In (vloc lr) (locs s inp stc2)) by (now rewrite (locs_eq st stc2 F1 F3)).
  ev. eapply (set_scr s inp xs0 h2 stc2 Hr2 lr); [exact Hfr2 | exact Hp2 |]. intros h3 _ Hr3 Hp3 _.
  rewrite lset_cons0 in Hp3.
  ev. eapply wp_len_pts; [exact Hp3|].
  ev. eapply (finish_learnt_sp st lr Hfresh fuel h3 stc2 (lneg p :: t) 1 0 0);
    [exact Hr3 | exact Hos2 | exact Hp3 | cbn; lia | intros; lia | now left | |].
  { intros u Hu. destruct (Hmarks2 u Hu) as (q & Hq & <-). apply In_nth with (d := 0) in Hq as (k & Hk & <-).
    exists (S k). cbn. split; [lia | reflexivity]. }
  intros bt h4 stc4 Lr3 Hr4 Hos4 Hp4 Hz4 (a' & t0 & t' & Ea & ELr3 & Hperm) Hbt_le Hbt. injection Ea as <- <-.
  subst Lr3. cbn [tl] in Hbt_le, Hbt.
  pose proof Hos4 as (G1 & G2 & G3 & G4 & Gf).
  assert (Hlvl : forall q, In q t -> 0 < nth (lvar q) (lvl st) 0 < length (lim st)).
  { intros q Hq. rewrite Forall_forall in Hlr1. apply Hlr1, Hq. }
  assert (Hbt_lt : bt < length (lim st)).
  { destruct Hbt as [-> | (q & Hq & <-)]; [destruct (lim st); [congruence | cbn; lia] | now apply Hlvl]. }
  assert (I4 : Inv val stc4).
  { split; [|split].
    - eapply core_ext; [| | | | | | | exact C]; rewrite ?G2, ?Gf by discriminate; reflexivity.
    - rewrite G2, G4. exact W.
    - exact Hz4. }
  ev. eapply backtrack_sp; [exact Hr4 | exact I4 |].
  intros h5 st5 Hr5 Hk5 I5 H1 H3 H2 Hbtr.
  rewrite (Gf FLim) in Hbtr by discriminate. specialize (Hbtr Hbt_lt).
  destruct Hbtr as (Edb & Az & Ak & Elv & Rk & Etr & Elim & Eq).
  rewrite (Gf FTr), (Gf FLim) in * by discriminate.
  set (m := nth bt (lim st) 0) in *.
  pose proof I5 as (C5 & W5 & S5).
  assert (Hp5 : pts h5 lr (lneg p :: t')).
  { apply Hk5; [|exact Hp4]. now rewrite (locs_eq st stc4 G1 G3). }
  assert (Hfr5 : ~ In (vloc lr) (locs s inp st5)) by (now rewrite (locs_eq st st5); [| rewrite H1 | rewrite H3]).
  (* the learnt literals stay false, the UIP becomes unassigned *)
  assert (Hlow : forall q, In q t -> lval (asg st5) q = 2).
  { intros q Hq. pose proof (proj1 (Forall_forall _ _) Hlr1 q Hq) as (Hqf & _).
    destruct (false_at_pos val st C q Hqf) as (k & Hk).
    assert (Hkm : k < m).
    { apply (count_le_lt_iff (lim st) bt k (i_sorted _ _ C) Hbt_lt). rewrite <- (lvl_at val st C k (lvar q) Hk).
      now apply Hbt_le. }
    rewrite lval_ext with (A := asg st); [exact Hqf|].
    rewrite Ak; [rewrite (Gf FAsg) by discriminate; reflexivity|].
    eapply at_pos_not_skipn; eauto. apply (i_nd _ _ C). }
  assert (Hlow' : Forall (fun q => lval (asg st5) q = 2) t').
  { apply Forall_forall. intros q Hq. apply Hlow. eapply Permutation_in; [symmetry; exact Hperm | exact Hq]. }
  assert (Huip : lval (asg st5) (lneg p) = 0).
  { apply lval_zero; [apply (i_asg _ _ C5)|]. rewrite lvar_lneg. apply Az.
    assert (Hidxm : m <= idx).
    { destruct (Nat.leb_spec m idx) as [|Hlt]; [assumption|]. exfalso.
      apply (count_le_lt_iff (lim st) bt idx (i_sorted _ _ C) Hbt_lt) in Hlt.
      pose proof (proj2 (cur_iff val st C Hne idx) Hbidx). lia. }
    apply in_map_iff. exists p. split; [reflexivity|].
    rewrite <- (firstn_skipn m (tr st)) in Hidx. rewrite nth_error_app2 in Hidx.
    - eapply nth_error_In. exact Hidx.
    - rewrite length_firstn. lia. }
  assert (Hlim5 : length (lim st5) = bt) by (rewrite Elim, length_firstn; lia).
  assert (Hsat : Exists (lit_true val) (lneg p :: t')).
  { destruct Hsound as [Ht | Hex]; [now left | right].
    apply Exists_exists in Hex as (q & Hq & Ht). apply Exists_exists. exists q. split; [|exact Ht].
    eapply Permutation_in; [exact Hperm | exact Hq]. }
  assert (Hv5 : lvar (lneg p) < length (asg st5) -> True) by auto.
  cbn [length]. destruct (Nat.eqb_spec (S (length t)) 1) as [Hl1 | Hl1].
  - (* a unit clause: learnt at level 0 *)
    assert (t = []) as -> by (destruct t; [reflexivity | cbn in Hl1; lia]).
    assert (bt = 0) as Hbt0 by (destruct Hbt as [-> | (q & [] & _)]; reflexivity).
    eapply enqueue_sp; [exact Hr5 |]. intros h6 Ha6 Hl6 Hrs6 Hr6 _.
    apply (HQ h6 _ Hr6). split; [|split].
    + apply core_enq; auto.
      * intros _. left. rewrite Elim, Hbt0. constructor.
      * intros; lia.
      * intros _. destruct Hsound as [Ht | Hex]; [exact Ht | inversion Hex].
    + exact W5.
    + exact S5.
  - (* store and watch the clause, then propagate the UIP from it *)
    assert (Ht' : t' <> []) by (intros ->; apply Permutation_sym, Permutation_nil in Hperm; subst t; cbn in Hl1; lia).
    assert (Hbt1 : 1 <= bt).
    { destruct t as [|q t]; [cbn in Hl1; lia|].
      pose proof (Hbt_le q (or_introl eq_refl)). pose proof (Hlvl q (or_introl eq_refl)). lia. }
    ev. ev.
    ev. eapply (push_cls s inp xs0 h5 st5 Hr5 lr (lneg p :: t')); [exact Hfr5 | exact Hp5 |]. intros h6 Hr6.
    assert (Hci : nth_error (hcls (cpush st5 lr (lneg p :: t'))) (length (db st5)) = Some lr).
    { cbn [hcls cpush]. rewrite <- (repr_len_db s inp xs0 h5 st5 Hr5), nth_error_app2, Nat.sub_diag by lia.
      reflexivity. }
    assert (Hcd : nth_error (db (cpush st5 lr (lneg p :: t'))) (length (db st5)) = Some (lneg p :: t')).
    { cbn [db cpush]. now rewrite nth_error_app2, Nat.sub_diag by lia. }
    ev. eapply attach_sp; [exact Hr6 | exact Hci | exact Hcd | destruct t'; [congruence | cbn; lia] | | |].
    { cbn [db wl cpush]. apply wch_snoc, W5. }
    { intros l Hl. apply (wch_fresh _ _ l W5). exact Hl. }
    intros h7 st7 Hr7 _ E71 E73 E72 E7f W7.
    eapply enqueue_sp; [exact Hr7 |]. intros h8 Ha8 Hl8 Hrs8 Hr8 _.
    apply (HQ h8 _ Hr8).
    assert (C7 : Core val st7).
    { eapply core_ext; [| | | | | | | apply (core_cpush val st5 lr _ C5 Hsat)];
        rewrite ?E72, ?E7f; reflexivity. }
    split; [|split].
    + apply core_enq; auto.
      * rewrite E7f. exact Huip.
      * intros; lia.
      * intros ci' E. assert (ci' = length (db st5)) as -> by lia. exists (lneg p :: t').
        rewrite E72. split; [exact Hcd|]. split; [reflexivity|]. cbn [tl]. rewrite E7f. exact Hlow'.
      * rewrite E7f. cbn [fv cpush]. rewrite Hlim5. lia.
    + unfold enq. cbn [fv fset fld_eqb db wl]. exact W7.
    + intros v. unfold enq. cbn [fv fset fld_eqb]. rewrite E7f. exact (S5 v).
Qed.


(** ** Search *)

Lemma pick_sp fuel : forall h st v n best bs Q,
  R h st -> (best = 0 \/ nth (best - 1) (asg st) 0 = 0) ->
  (forall r, (r = 0 \/ nth (r - 1) (asg st) 0 = 0) -> Q r h) ->
  wp (pick s fuel v n best bs) Q h.
Proof.
  induction fuel as [|f IH]; intros h st v n best bs Q Hr Hb HQ; cbn [pick].
  { apply wp_vabort. }
  destruct (Nat.leb_spec n v); [apply wp_ret, HQ, Hb|].
  ev. ev. intros a Ha. apply nth_error_nth_eq in Ha. subst a.
  destruct (Nat.eqb_spec (nth v (asg st) 0) 0) as [E | E].
  - ev. ev. intros st' _.
    destruct (Nat.eqb best 0 || Nat.ltb bs st').
    + eapply IH; [exact Hr | right; now replace (v + 1 - 1) with v by lia | exact HQ].
    + eapply IH; [exact Hr | exact Hb | exact HQ].
  - eapply IH; [exact Hr | exact Hb | exact HQ].
Qed.

Lemma search_sp fuel budget : forall nvars h st Q,
  R h st -> Inv val st -> (forall r h', r <> 0 -> r <= 2 -> Q r h') ->
  wp (search s fuel budget nvars) Q h.
Proof.
  induction budget as [|b IH]; intros nvars h st Q Hr I HQ; cbn [search].
  { apply wp_ret, HQ; lia. }
  ev. eapply propagate_sp; [exact Hr | exact I |]. intros confl h1 st1 Hr1 I1 H0 Hc.
  pose proof I1 as (C1 & W1 & S1).
  destruct (Nat.eqb_spec confl 0) as [-> | Hne].
  - (* no conflict: decide *)
    specialize (H0 eq_refl).
    ev. eapply pick_sp; [exact Hr1 | now left |]. intros v1 Hv1.
    destruct (Nat.eqb_spec v1 0) as [-> | Hv1nz]; [apply wp_ret, HQ; lia|].
    destruct Hv1 as [|Hv0]; [lia|]. cbv zeta.
    ev. ev. intros ph _. ev. ev. ev. ev. intros h2 Hr2 _.
    ev. eapply enqueue_sp; [exact Hr2 |]. intros h3 Ha3 Hl3 Hrs3 Hr3 _.
    assert (Hq : qhead st1 = length (tr st1)) by (pose proof (i_qtr _ _ C1); lia).
    eapply IH; [exact Hr3 | | exact HQ].
    split; [|split].
    + apply core_enq; fvs; auto.
      * now apply core_decide.
      * apply lval_zero; [apply (i_asg _ _ C1)|]. now rewrite lvar_lit_of.
      * intros _. right. apply in_or_app. right. now left.
      * intros; lia.
      * rewrite length_app. cbn. lia.
    + exact W1.
    + exact S1.
  - (* a conflict *)
    destruct (Hc Hne) as (ci & cl & Eci & Hd & Hfalse & Hcur). subst confl.
    unfold decision_level. ev. ev. destruct (Nat.eqb_spec (length (lim st1)) 0) as [Hl0 | Hl0].
    { exfalso. eapply (no_false_clause_l0 val st1 C1 cl Hl0); [eapply nth_error_In; eauto | exact Hfalse]. }
    ev. ev. intros k _. ev. ev. intros h2 _ Hr2 _.
    assert (I2 : Inv val (fset st1 FMisc (lset (fv st1 FMisc) CONFLICTS (k + 1))))
      by (apply inv_misc_other; [discriminate | exact I1]).
    ev. eapply learn_sp; [exact Hr2 | exact I2 | | cbn [fv fset fld_eqb]; intros E; rewrite E in Hl0; cbn in Hl0; lia |].
    { exists ci, cl. replace (S ci - 1) with ci by lia. auto. }
    replace (S ci - 1) with ci by lia.
    intros h3 st3 Hr3 I3.
    ev. ev. intros rc _. ev. ev. intros rl _.
    eapply wp_seq with (P := fun _ h4 => exists st4, R h4 st4 /\ Inv val st4).
    + destruct (Nat.leb_spec rl (rc + 1)).
      * ev. ev. intros h4 _ Hr4 _. ev. ev. intros h5 _ Hr5 _.
        assert (I4 : Inv val (fset st3 FMisc (lset (fv st3 FMisc) RCOUNT 0)))
          by (apply inv_misc_other; [discriminate | exact I3]).
        eapply backtrack_sp; [exact Hr5 | apply inv_misc_other; [discriminate | exact I4] |].
        intros h6 st6 Hr6 _ I6 _ _ _ _. exists st6. auto.
      * ev. intros h4 _ Hr4 _. eexists. split; [exact Hr4|].
        apply inv_misc_other; [discriminate | exact I3].
    + intros _ h4 (st4 & Hr4 & I4). eapply IH; [exact Hr4 | exact I4 | exact HQ].
Qed.


(** ** Loading *)

Lemma read_lits_sp fuel : forall h st c xs pos ys Q,
  R h st -> ~ In (vloc c) (locs s inp st) -> pts h c xs ->
  (forall j, j < length ys -> nth_error xs0 (pos + j) = nth_error ys j) ->
  (forall h', R h' st -> pts h' c (xs ++ ys) -> Q tt h') ->
  wp (read_lits fuel inp c pos (length ys)) Q h.
Proof.
  induction fuel as [|f IH]; intros h st c xs pos ys Q Hr Hc Hp Hys HQ; cbn [read_lits].
  { apply wp_vabort. }
  destruct ys as [|y ys]; cbn [length].
  { apply wp_ret, HQ; [exact Hr | now rewrite app_nil_r]. }
  ev. eapply (get_inp s inp xs0 h st Hr). intros x Hx.
  assert (x = y) as -> by (specialize (Hys 0 ltac:(cbn; lia)); rewrite Nat.add_0_r in Hys; cbn in Hys; congruence).
  ev. eapply (push_scr s inp xs0 h st Hr c xs y); [exact Hc | exact Hp |]. intros h1 Hr1 Hp1 _.
  eapply IH; [exact Hr1 | exact Hc | exact Hp1 | |].
  - intros j Hj. rewrite <- Nat.add_assoc. apply (Hys (S j)). cbn. lia.
  - intros h' Hr' Hp'. apply HQ; [exact Hr'|]. now rewrite <- app_assoc in Hp'.
Qed.

Lemma load_sp fuel n : forall F pos h st Q,
  R h st -> Inv val st -> lim st = [] -> encodes xs0 n pos F -> Forall (Exists (lit_true val)) F ->
  (forall h' st', R h' st' -> Inv val st' -> Q true h') ->
  wp (load s fuel inp pos n) Q h.
Proof.
  induction fuel as [|f IH]; intros F pos h st Q Hr I Hlim HF Hsat HQ; cbn [load].
  { apply wp_vabort. }
  pose proof I as (C & W & S0).
  destruct (Nat.leb_spec n pos).
  { apply wp_ret. now apply (HQ h st). }
  inversion HF as [? Hle | ? c F' Hlt Hlen Hc HF']; subst; [lia|].
  inversion Hsat as [|? ? Hcsat HF'sat]; subst.
  ev. eapply (get_inp s inp xs0 h st Hr). intros len Hl. rewrite Hlen in Hl. injection Hl as <-.
  ev. eapply (make_scr s inp xs0 h st Hr). intros v h1 Hfresh Hp1 Hr1 _ _ _. cbn [repeat] in Hp1.
  ev. eapply read_lits_sp; [exact Hr1 | exact Hfresh | exact Hp1 | exact Hc |]. intros h2 Hr2 Hp2. cbn [app] in Hp2.
  ev. ev. ev. eapply (push_cls s inp xs0 h2 st Hr2 v c); [exact Hfresh | exact Hp2 |]. intros h3 Hr3.
  set (st3 := cpush st v c) in *.
  assert (I3 : Inv val st3).
  { split; [|split]; [apply core_cpush; auto | apply wch_snoc, W | exact S0]. }
  assert (Hci : nth_error (hcls st3) (length (db st)) = Some v).
  { unfold st3. cbn [hcls cpush]. rewrite <- (repr_len_db s inp xs0 h st Hr), nth_error_app2, Nat.sub_diag by lia.
    reflexivity. }
  assert (Hcd : nth_error (db st3) (length (db st)) = Some c).
  { unfold st3. cbn [db cpush]. now rewrite nth_error_app2, Nat.sub_diag by lia. }
  destruct (Nat.eqb_spec (length c) 0) as [H0 | H0].
  { exfalso. destruct c; [inversion Hcsat | cbn in H0; lia]. }
  destruct (Nat.eqb_spec (length c) 1) as [H1 | H1].
  - (* a unit clause: assign its literal at level 0, or find the input contradictory *)
    destruct c as [|l [|l' c]]; [cbn in H1; lia | | cbn in H1; lia].
    ev. eapply (get_cl s inp xs0 h3 st3 Hr3 _ v); [exact Hci | exact Hcd |]. intros x Hx. cbn in Hx.
    injection Hx as <-.
    ev. eapply lit_value_sp; [exact Hr3 |]. intros _. cbv beta.
    assert (Hltv : lit_true val l) by (apply Exists_exists in Hcsat as (x & [<- | []] & Hx); exact Hx).
    destruct (Nat.eqb_spec (lval (asg st3) l) 2) as [E2 | E2].
    { exfalso. eapply (no_false_clause_l0 val st3 (proj1 I3) [l]); [unfold st3; cbn [fv cpush]; now rewrite Hlim | |].
      - unfold st3. cbn [db cpush]. apply in_or_app. right. now left.
      - constructor; [exact E2 | constructor]. }
    eapply wp_seq with (P := fun _ h4 => exists st4, R h4 st4 /\ Inv val st4 /\ lim st4 = []).
    + destruct (Nat.eqb_spec (lval (asg st3) l) 0) as [E0 | E0].
      * eapply enqueue_sp; [exact Hr3 |]. intros h4 Ha4 Hl4 Hrs4 Hr4 _.
        exists (enq st3 l 0). split; [exact Hr4|]. split; [split; [|split]|].
        -- apply core_enq; [apply (proj1 I3) | exact E0 | exact Ha4 | exact Hl4 | exact Hrs4 | | intros; lia | intros _; exact Hltv].
           intros _. left. unfold st3. cbn [fv cpush]. rewrite Hlim. constructor.
        -- exact (proj1 (proj2 I3)).
        -- exact S0.
        -- unfold enq, st3. cbn [fv fset fld_eqb cpush]. exact Hlim.
      * apply wp_ret. exists st3. auto.
    + intros _ h4 (st4 & Hr4 & I4 & Hlim4).
      eapply IH; [exact Hr4 | exact I4 | exact Hlim4 | exact HF' | exact HF'sat | exact HQ].
  - (* watch two of its literals *)
    ev. eapply attach_sp; [exact Hr3 | exact Hci | exact Hcd | lia | apply I3 | |].
    { intros l Hl. apply (wch_fresh _ _ l W). exact Hl. }
    intros h4 st4 Hr4 _ E1 E3 E2 Ef W4.
    eapply IH; [exact Hr4 | | | exact HF' | exact HF'sat | exact HQ].
    + split; [|split].
      * eapply core_ext; [| | | | | | | apply (proj1 I3)]; rewrite ?E2, ?Ef; reflexivity.
      * exact W4.
      * intros u. rewrite Ef. apply S0.
    + rewrite Ef. exact Hlim.
Qed.

End Spec.

(** * Initialization *)

Local Notation cellof := (fun T : Type => list T).

(** The locations [L] are allocated and pairwise distinct. *)
Definition Alloc (h : heap) (L : list loc) : Prop := NoDup L /\ forall l, In l L -> h l <> None.

Lemma alloc_fresh h L l c : Alloc h L -> h l = None -> Alloc (upd h l c) (L ++ [l]).
Proof.
  intros [Hn Ha] Hl. split.
  - apply nodup_snoc'; [exact Hn|]. intros Hi. exact (Ha l Hi Hl).
  - intros x Hx. apply in_app_or in Hx as [Hx | [<- | []]].
    + destruct (Nat.eq_dec x l) as [-> | Hne]; [rewrite upd_eq; discriminate|].
      rewrite upd_neq by exact Hne. now apply Ha.
    + rewrite upd_eq. discriminate.
Qed.

Lemma alloc_upd h L l c : Alloc h L -> h l <> None -> Alloc (upd h l c) L.
Proof.
  intros [Hn Ha] Hl. split; [exact Hn|]. intros x Hx.
  destruct (Nat.eq_dec x l) as [-> | Hne]; [rewrite upd_eq; discriminate | rewrite upd_neq by exact Hne; auto].
Qed.

Lemma keep_fresh h l c x c' : h l = None -> h x = Some c' -> upd h l c x = Some c'.
Proof. intros Hl Hx. rewrite upd_neq; [exact Hx | congruence]. Qed.

Lemma keep_fresh_all h l c W xs : h l = None -> Forall (fun w => pts h w xs) W -> Forall (fun w => pts (upd h l c) w xs) W.
Proof. intros Hl. apply Forall_impl. intros w Hw. unfold pts in *. now apply keep_fresh. Qed.

Lemma fresh_vecs_sp fuel : forall (acc : vec (vec nat)) n h L W Q,
  Alloc h L -> h (vloc acc) = Some (existT cellof (vec nat) W) ->
  (forall h' W', Alloc h' (L ++ map vloc W') -> h' (vloc acc) = Some (existT cellof (vec nat) (W ++ W')) ->
     Forall (fun w => pts h' w []) W' -> (forall x c, x <> vloc acc -> h x = Some c -> h' x = Some c) ->
     Q tt h') ->
  wp (fresh_vecs fuel acc n) Q h.
Proof.
  induction fuel as [|f IH]; intros acc n h L W Q HA Hacc HQ; cbn [fresh_vecs].
  { apply wp_vabort. }
  destruct n as [|n].
  { apply wp_ret. apply (HQ h []); [now rewrite app_nil_r | now rewrite app_nil_r | constructor | auto]. }
  apply wp_bind, wp_vmake. intros w Hw.
  assert (Hne : vloc acc <> vloc w) by congruence.
  apply wp_bind, wp_vpush. intros ws Hws.
  rewrite (cell_inj _ _ _ _ Hws (keep_fresh _ _ _ _ _ Hw Hacc)).
  eapply IH with (L := L ++ [vloc w]).
  - apply alloc_upd; [apply alloc_fresh; assumption |]. rewrite upd_neq by exact Hne. congruence.
  - apply upd_eq.
  - intros h' W'' HA' Hacc' HW'' Hfr. apply (HQ h' (w :: W'')).
    + now rewrite <- app_assoc in HA'.
    + now rewrite <- app_assoc in Hacc'.
    + constructor; [|exact HW'']. apply Hfr; [congruence|]. rewrite upd_neq by congruence. apply upd_eq.
    + intros x c Hx Hc. apply Hfr; [exact Hx|]. rewrite upd_neq by exact Hx. now apply keep_fresh.
Qed.


Definition init_st (W : list (vec nat)) (nv : nat) : astate :=
  AS [] [] W (map (fun _ => []) W)
     (fun f => match f with
               | FPh => repeat 2 nv | FTr | FLim => [] | FMisc => repeat 0 4 | _ => repeat 0 nv
               end).

Lemma nth_repeat0 v n : nth v (repeat 0 n) 0 = 0.
Proof. apply nth_repeat. Qed.

Lemma nth_map_nil {A} (W : list A) l : nth l (map (fun _ => @nil nat) W) [] = [].
Proof. revert l; induction W; intros [|l]; cbn; auto. Qed.

Lemma init_inv val W nv : Inv val (fset (init_st W nv) FMisc (lset (repeat 0 4) RLIMIT 100)).
Proof.
  split; [|split].
  - constructor; cbn [fv fset fld_eqb init_st db].
    + constructor.
    + intros v. rewrite nth_repeat0. lia.
    + constructor.
    + intros v. rewrite nth_repeat0. cbn. tauto.
    + constructor.
    + intros k l Hk. destruct k; discriminate.
    + intros i j H. cbn in H. lia.
    + constructor.
    + vm_compute. lia.
    + intros k l r Hk. destruct k; discriminate.
    + intros k l Hk. destruct k; discriminate.
    + intros l [].
  - intros ci l _. unfold cnt. cbn [wl fset init_st]. rewrite nth_map_nil. cbn. lia.
  - intros v. cbn [fv fset fld_eqb init_st]. apply nth_repeat0.
Qed.

Lemma F2_init h W : Forall (fun w => pts h w []) W -> Forall2 (pts h) W (map (fun _ => []) W).
Proof. induction 1; constructor; auto. Qed.

Lemma nodup_drop2 (a b : loc) l : NoDup (a :: b :: l) -> NoDup (a :: l).
Proof.
  intros H. inversion H as [|? ? Ha Hn]; subst. inversion Hn; subst.
  constructor; [intros Hi; apply Ha; now right | assumption].
Qed.

Lemma mod8_ne c k : c = 1 \/ c = 2 \/ c = 3 -> (c + 8 * k) mod 8 <> 0.
Proof. intros H. rewrite Nat.mul_comm, Nat.Div0.mod_add. destruct H as [-> | [-> | ->]]; cbn; lia. Qed.

(** After allocating [v] in [h], carry every fact about [h] over to the new heap. *)
Ltac bump :=
  match goal with
  | Hn : ?h (vloc ?v) = None |- wp _ _ (upd ?h (vloc ?v) ?c) =>
    repeat match goal with
      | H : h ?x = Some ?c' |- _ =>
        let H' := fresh "K" in pose proof (keep_fresh h (vloc v) c x c' Hn H) as H'; clear H
      | H : Forall (fun w => pts h w ?xs) ?W |- _ =>
        let H' := fresh "KW" in pose proof (keep_fresh_all h (vloc v) c W xs Hn H) as H'; clear H
      end;
    match goal with
    | HA : Alloc h ?L |- _ =>
      let H' := fresh "A" in pose proof (alloc_fresh h L (vloc v) c HA Hn) as H'; clear HA
    end;
    let Hv := fresh "P" in assert (Hv : upd h (vloc v) c (vloc v) = Some c) by apply upd_eq;
    clear Hn
  end.

(** If [run] finishes and answers "unsatisfiable" ([code] 0), the formula
    encoded in [input] when it started has no model. *)
Theorem run_unsat_sound fuel budget nvars inp ninput xs0 F h0 r h1 :
  h0 (vloc inp) = Some (existT cellof nat xs0) ->
  encodes xs0 ninput 0 F ->
  runs h0 (Solver.run fuel budget nvars inp ninput) r h1 ->
  r mod 8 = 0 ->
  ~ exists val, satisfies val F.
Proof.
  intros Hinp HF Hrun Hr0 (val & Hval). revert r h1 Hrun Hr0.
  change (wp (Solver.run fuel budget nvars inp ninput) (fun r _ => r mod 8 <> 0) h0).
  assert (HA : Alloc h0 [vloc inp]) by (split; [constructor; [intros [] | constructor] | intros l [<- | []]; congruence]).
  unfold Solver.run.
  apply wp_bind, wp_vmake. intros e He. bump.
  apply wp_bind, wp_vmake. intros cs Hcs. bump.
  apply wp_bind, wp_vmake. intros ws Hws. bump.
  apply wp_bind. eapply fresh_vecs_sp; [eassumption | eassumption |]. cbn [app].
  intros h2 W HA2 Hws2 HW Hfr.
  pose proof HA2 as [ND2 _]. inversion ND2 as [|? ? N1 ND3]; subst. inversion ND3 as [|? ? N2 ND4]; subst.
  inversion ND4 as [|? ? N3 _]; subst.
  assert (Dinp : vloc inp <> vloc ws) by (intros E; apply N1; rewrite E; cbn; tauto).
  assert (Dcs : vloc cs <> vloc ws) by (intros E; apply N3; rewrite E; cbn; tauto).
  pose proof (Hfr _ _ Dinp K2) as Kinp. pose proof (Hfr _ _ Dcs K) as Kcs.
  clear K K1 K2 P A Hfr N1 N2 N3 ND2 ND3 ND4.
  apply wp_bind, wp_vmake. intros asg Hasg. bump.
  apply wp_bind, wp_vmake. intros lvl Hlvl. bump.
  apply wp_bind, wp_vmake. intros rsn Hrsn. bump.
  apply wp_bind, wp_vmake. intros ph Hph. bump.
  apply wp_bind, wp_vmake. intros stp Hstp. bump.
  apply wp_bind, wp_vmake. intros sn Hsn. bump.
  apply wp_bind, wp_vmake. intros tr Htr. bump.
  apply wp_bind, wp_vmake. intros tlim Htlim. bump.
  apply wp_bind, wp_vmake. intros m Hm. bump.
  set (s := mk_state cs ws asg lvl rsn ph stp sn tr tlim m).
  match goal with |- wp _ _ ?h => set (h9 := h) in * end.
  assert (R9 : repr s inp xs0 h9 (init_st W nvars)).
  { constructor; cbn [init_st hcls hwl db wl fv].
    - assumption.
    - assumption.
    - constructor.
    - now apply F2_init.
    - intros f. destruct f; unfold pts; cbn [floc s]; assumption.
    - unfold pts; assumption.
    - match goal with H : Alloc h9 _ |- _ => destruct H as [ND _] end.
      rewrite <- !app_assoc in ND. cbn [app] in ND. apply nodup_drop2 in ND.
      eapply Permutation_NoDup; [| exact ND]. unfold locs. cbn [map all_flds floc hcls hwl init_st s app].
      do 3 apply perm_skip. apply Permutation_app_comm. }
  apply wp_bind. eapply (set_f s inp xs0 h9 _ R9 FMisc RLIMIT 100). intros h10 _ R10 _. cbv zeta. fold s.
  apply wp_bind. eapply (load_sp s inp xs0 val fuel ninput F 0 h10); [exact R10 | apply init_inv | reflexivity | exact HF | exact Hval |].
  intros h11 st11 R11 I11. cbv beta iota.
  eapply wp_seq with (P := fun code _ => code = 1 \/ code = 2 \/ code = 3).
  - apply wp_bind. eapply search_sp; [exact R11 | exact I11 |]. intros r1 h12 Hr1 Hr2.
    destruct (Nat.eqb_spec r1 1) as [-> | Hne].
    + apply wp_bind. intros b h13 _. apply wp_ret. destruct b; auto.
    + apply wp_ret. lia.
  - intros code h12 Hcode. apply wp_bind, wp_vget. intros _ k _ _. apply wp_ret. now apply mod8_ne.
Qed.

(** If [solve] finishes and answers "unsatisfiable" ([code] 0), the formula
    encoded in [input] when it started has no model. *)
Theorem solve_unsat_sound fuel budget nvars inp ninput xs0 F h0 r h1 :
  h0 (vloc inp) = Some (existT cellof nat xs0) ->
  encodes xs0 ninput 0 F ->
  runs h0 (Solver.solve fuel budget nvars inp ninput) r h1 ->
  r mod 8 = 0 ->
  ~ exists val, satisfies val F.
Proof.
  intros Hinp HF Hrun. revert r h1 Hrun.
  change (wp (Solver.solve fuel budget nvars inp ninput)
            (fun r _ => r mod 8 = 0 -> ~ exists val, satisfies val F) h0).
  apply (solve_wp _ _ _ _ _ xs0); [exact Hinp | intros H; cbv in H; discriminate |].
  intros F' _ _ r h1 Hr. eapply run_unsat_sound; eassumption.
Qed.

