(** Memory safety of [Solver.run]: on a well-formed input no run gets
    stuck.  Every event the solver performs has a [step]: indices are in
    bounds, shrinks never grow, and every handle points at a cell.

    The proof is separate from the soundness proofs: those fix a model of
    the formula (UNSAT soundness) or only look at the frame (SAT soundness),
    while safety must hold of every input, satisfiable or not.  So it has
    its own invariant [SI], much weaker than [Core]: the per-variable
    vectors have [nv] cells, [watches] has [2 * nv] lists, every literal in
    the database and on the trail is below [2 * nv], every watch entry
    names a clause of length at least 2, every reason is at most the
    database's length, and [trail_lim] is strictly increasing and below the
    trail's length.  It holds of the state [run] builds, and every event
    keeps it.  [repr] from [SolverRepr] supplies the separation. *)
From Stdlib Require Import List PeanoNat Lia Bool Permutation.
From Crane Require Import Monads.ITree.
Require Import SatVec VecSem VecSafe Solver SolverSat SolverRepr SolverInv SolverUnsat.
Import ListNotations.
Import Solver.

Local Notation cellof := (fun T : Type => list T).

Lemma nth_error_lt' {A} (xs : list A) i x : nth_error xs i = Some x -> i < length xs.
Proof. intros H. apply nth_error_Some. congruence. Qed.

Lemma Forall_nth_error {A} (P : A -> Prop) xs i x : Forall P xs -> nth_error xs i = Some x -> P x.
Proof. intros H Hi. rewrite Forall_forall in H. apply H. eapply nth_error_In; eauto. Qed.

Lemma Forall_lset {A} (P : A -> Prop) xs i x : Forall P xs -> P x -> Forall P (lset xs i x).
Proof.
  intros H Hx. revert i. induction H as [|y ys Hy H IH]; intros [|i]; cbn; constructor; auto.
Qed.

Lemma Forall_firstn' {A} (P : A -> Prop) n xs : Forall P xs -> Forall P (firstn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. now apply Forall_app in H as [H _]. Qed.

Lemma Forall_skipn' {A} (P : A -> Prop) n xs : Forall P xs -> Forall P (skipn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. now apply Forall_app in H as [_ H]. Qed.

Lemma lvar_lt l nv : l < 2 * nv -> lvar l < nv.
Proof. intros H. unfold lvar. apply Nat.Div0.div_lt_upper_bound. lia. Qed.

Lemma lneg_lt l nv : l < 2 * nv -> lneg l < 2 * nv.
Proof.
  intros H. destruct (lit_cases l) as [[E M] | [E M]]; unfold lneg.
  - rewrite M. cbn. lia.
  - rewrite M. cbn. lia.
Qed.

Lemma lit_of_lt v a nv : v < nv -> lit_of v a < 2 * nv.
Proof. intros H. unfold lit_of. destruct (Nat.eqb a 1); lia. Qed.

(** * Events, with their obligations *)

Section Ev.
Variables (s : state) (inp : vec nat) (xs0 : list nat) (h : heap) (st : astate).
Hypothesis R : repr s inp xs0 h st.

Lemma sget_pts v xs i (Q : nat -> heap -> Prop) :
  pts h v xs -> i < length xs -> (forall x, nth_error xs i = Some x -> Q x h) -> safe (vget (E := vecE) v i) Q h.
Proof. intros Hp Hi HQ. eapply safe_vget; eauto. Qed.

Lemma slen_pts v xs (Q : nat -> heap -> Prop) :
  pts h v xs -> Q (length xs) h -> safe (vlen (E := vecE) v) Q h.
Proof. intros Hp HQ. eapply safe_vlen; eauto. Qed.

Lemma sget_f f i Q :
  i < length (fv st f) -> (forall x, nth_error (fv st f) i = Some x -> Q x h) -> safe (vget (floc s f) i) Q h.
Proof. apply sget_pts, (r_fv _ _ _ _ _ R). Qed.

Lemma slen_f f Q : Q (length (fv st f)) h -> safe (vlen (floc s f)) Q h.
Proof. apply slen_pts, (r_fv _ _ _ _ _ R). Qed.

Lemma sset_f f i x Q :
  i < length (fv st f) ->
  (forall h', repr s inp xs0 h' (fset st f (lset (fv st f) i x)) -> keeps s inp st h h' -> Q tt h') ->
  safe (vset (floc s f) i x) Q h.
Proof.
  intros Hi HQ. eapply safe_vset; [apply (r_fv _ _ _ _ _ R) | exact Hi |]. apply HQ.
  - now apply repr_fset.
  - apply keeps_upd, locs_in_f.
Qed.

Lemma spush_f f x Q :
  (forall h', repr s inp xs0 h' (fset st f (fv st f ++ [x])) -> keeps s inp st h h' -> Q tt h') ->
  safe (vpush (floc s f) x) Q h.
Proof.
  intros HQ. eapply safe_vpush; [apply (r_fv _ _ _ _ _ R) |]. apply HQ.
  - now apply repr_fset.
  - apply keeps_upd, locs_in_f.
Qed.

Lemma sshrink_f f n Q :
  n <= length (fv st f) ->
  (forall h', repr s inp xs0 h' (fset st f (firstn n (fv st f))) -> keeps s inp st h h' -> Q tt h') ->
  safe (vshrink (floc s f) n) Q h.
Proof.
  intros Hn HQ. eapply safe_vshrink; [apply (r_fv _ _ _ _ _ R) | exact Hn |]. apply HQ.
  - now apply repr_fset.
  - apply keeps_upd, locs_in_f.
Qed.

Lemma sget_hc i (Q : vec nat -> heap -> Prop) :
  i < length (db st) -> (forall c, nth_error (hcls st) i = Some c -> Q c h) -> safe (vget (clauses s) i) Q h.
Proof.
  intros Hi HQ. eapply safe_vget; [apply (r_cls _ _ _ _ _ R) | | exact HQ].
  now rewrite (repr_len_db _ _ _ _ _ R).
Qed.

Lemma slen_hc Q : Q (length (db st)) h -> safe (vlen (clauses s)) Q h.
Proof.
  intros HQ. eapply safe_vlen; [apply (r_cls _ _ _ _ _ R) |]. now rewrite (repr_len_db _ _ _ _ _ R).
Qed.

Lemma sget_hw i (Q : vec nat -> heap -> Prop) :
  i < length (wl st) -> (forall c, nth_error (hwl st) i = Some c -> Q c h) -> safe (vget (watches s) i) Q h.
Proof.
  intros Hi HQ. eapply safe_vget; [apply (r_wls _ _ _ _ _ R) | | exact HQ].
  now rewrite (repr_len_wl _ _ _ _ _ R).
Qed.

Lemma sget_cl k c cl i Q :
  nth_error (hcls st) k = Some c -> nth_error (db st) k = Some cl -> i < length cl ->
  (forall x, nth_error cl i = Some x -> Q x h) -> safe (vget c i) Q h.
Proof.
  intros Hk Hd Hi. destruct (repr_cl _ _ _ _ _ _ _ R Hk) as (cl' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply sget_pts.
Qed.

Lemma slen_cl k c cl Q :
  nth_error (hcls st) k = Some c -> nth_error (db st) k = Some cl -> Q (length cl) h -> safe (vlen c) Q h.
Proof.
  intros Hk Hd. destruct (repr_cl _ _ _ _ _ _ _ R Hk) as (cl' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply slen_pts.
Qed.

Lemma sset_cl k c cl i x Q :
  nth_error (hcls st) k = Some c -> nth_error (db st) k = Some cl -> i < length cl ->
  (forall h', repr s inp xs0 h' (dset st (lset (db st) k (lset cl i x))) -> keeps s inp st h h' -> Q tt h') ->
  safe (vset c i x) Q h.
Proof.
  intros Hk Hd Hi HQ. destruct (repr_cl _ _ _ _ _ _ _ R Hk) as (cl' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply safe_vset; [exact Hp | exact Hi |]. apply HQ.
  - now apply repr_dset.
  - eapply keeps_upd, locs_in_c; eauto.
Qed.

Lemma sget_w k c ws i Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws -> i < length ws ->
  (forall x, nth_error ws i = Some x -> Q x h) -> safe (vget c i) Q h.
Proof.
  intros Hk Hd Hi. destruct (repr_w _ _ _ _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply sget_pts.
Qed.

Lemma slen_w k c ws Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws -> Q (length ws) h -> safe (vlen c) Q h.
Proof.
  intros Hk Hd. destruct (repr_w _ _ _ _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply slen_pts.
Qed.

Lemma sset_w k c ws i x Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws -> i < length ws ->
  (forall h', repr s inp xs0 h' (wset st (lset (wl st) k (lset ws i x))) -> keeps s inp st h h' -> Q tt h') ->
  safe (vset c i x) Q h.
Proof.
  intros Hk Hd Hi HQ. destruct (repr_w _ _ _ _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply safe_vset; [exact Hp | exact Hi |]. apply HQ.
  - now apply repr_wset.
  - eapply keeps_upd, locs_in_w; eauto.
Qed.

Lemma spush_w k c ws x Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws ->
  (forall h', repr s inp xs0 h' (wset st (lset (wl st) k (ws ++ [x]))) -> keeps s inp st h h' -> Q tt h') ->
  safe (vpush c x) Q h.
Proof.
  intros Hk Hd HQ. destruct (repr_w _ _ _ _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply safe_vpush; [exact Hp |]. apply HQ.
  - now apply repr_wset.
  - eapply keeps_upd, locs_in_w; eauto.
Qed.

Lemma sshrink_w k c ws n Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws -> n <= length ws ->
  (forall h', repr s inp xs0 h' (wset st (lset (wl st) k (firstn n ws))) -> keeps s inp st h h' -> Q tt h') ->
  safe (vshrink c n) Q h.
Proof.
  intros Hk Hd Hn HQ. destruct (repr_w _ _ _ _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply safe_vshrink; [exact Hp | exact Hn |]. apply HQ.
  - now apply repr_wset.
  - eapply keeps_upd, locs_in_w; eauto.
Qed.

(** A fresh vector is a scratch cell. *)
Lemma smake_scr n (x : nat) Q :
  (forall v h', ~ In (vloc v) (locs s inp st) -> pts h' v (repeat x n) -> repr s inp xs0 h' st ->
     keeps s inp st h h' -> Q v h') ->
  safe (vmake (E := vecE) n x) Q h.
Proof.
  intros HQ. apply safe_vmake. intros v Hv.
  assert (Hn : ~ In (vloc v) (locs s inp st)) by (intros Hi; exact (repr_alloc _ _ _ _ _ _ R Hi Hv)).
  apply HQ; auto.
  - apply pts_upd_eq.
  - now apply repr_out.
  - intros v' xs _ Hp. apply pts_upd_neq; [|exact Hp]. unfold pts in Hp. congruence.
Qed.

Lemma sset_scr v xs i x Q :
  ~ In (vloc v) (locs s inp st) -> pts h v xs -> i < length xs ->
  (forall h', repr s inp xs0 h' st -> pts h' v (lset xs i x) -> Q tt h') ->
  safe (vset v i x) Q h.
Proof.
  intros Hn Hp Hi HQ. eapply safe_vset; [exact Hp | exact Hi |]. apply HQ.
  - now apply repr_out.
  - apply pts_upd_eq.
Qed.

Lemma spush_scr v xs x Q :
  ~ In (vloc v) (locs s inp st) -> pts h v xs ->
  (forall h', repr s inp xs0 h' st -> pts h' v (xs ++ [x]) -> Q tt h') ->
  safe (vpush v x) Q h.
Proof.
  intros Hn Hp HQ. eapply safe_vpush; [exact Hp |]. apply HQ.
  - now apply repr_out.
  - apply pts_upd_eq.
Qed.

Lemma spush_cls c cl Q :
  ~ In (vloc c) (locs s inp st) -> pts h c cl ->
  (forall h', repr s inp xs0 h' (cpush st c cl) -> Q tt h') -> safe (vpush (clauses s) c) Q h.
Proof.
  intros Hn Hp HQ. eapply safe_vpush; [apply (r_cls _ _ _ _ _ R) |].
  apply HQ. now apply repr_cpush.
Qed.

Lemma sget_inp i Q : i < length xs0 -> (forall x, nth_error xs0 i = Some x -> Q x h) -> safe (vget inp i) Q h.
Proof. apply sget_pts, (r_inp _ _ _ _ _ R). Qed.

End Ev.

(** * The safety invariant *)

Section Safe.
Variables (s : state) (inp : vec nat) (xs0 : list nat) (nv : nat).

Local Notation R := (repr s inp xs0).
Local Notation keeps := (keeps s inp).

(** A watch entry names a clause of length at least 2. *)
Definition wok (D : list (list nat)) (ci : nat) : Prop :=
  exists cl, nth_error D ci = Some cl /\ 2 <= length cl.

Definition incr (l : list nat) : Prop :=
  forall i j a b, i < j -> nth_error l i = Some a -> nth_error l j = Some b -> a < b.

Definition lit_ok (l : nat) : Prop := l < 2 * nv.

(** Everything but [trail_lim]'s bound by the trail, which a decision
    breaks for one event. *)
Record SIc (st : astate) : Prop := {
  si_asg : length (asg st) = nv;
  si_lvl : length (lvl st) = nv;
  si_rsn : length (rsn st) = nv;
  si_ph : length (fv st FPh) = nv;
  si_st : length (fv st FSt) = nv;
  si_sn : length (sn st) = nv;
  si_misc : length (fv st FMisc) = 4;
  si_wl : length (wl st) = 2 * nv;
  si_db : Forall (Forall lit_ok) (db st);
  si_tr : Forall lit_ok (tr st);
  si_w : Forall (Forall (wok (db st))) (wl st);
  si_r : Forall (fun r => r <= length (db st)) (rsn st);
  si_inc : incr (lim st)
}.

Definition lim_lt (st : astate) : Prop := Forall (fun x => x < length (tr st)) (lim st).

Definition SI (st : astate) : Prop := SIc st /\ lim_lt st.

Ltac fvs := cbn [fv fset dset wset cpush wpush fld_eqb hcls db hwl wl] in *.

Lemma sic_free st f xs :
  SIc st -> f = FAsg \/ f = FLvl \/ f = FPh \/ f = FSt \/ f = FSn \/ f = FMisc ->
  length xs = length (fv st f) -> SIc (fset st f xs).
Proof.
  intros [] Hf Hl. destruct Hf as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    constructor; fvs; auto; lia.
Qed.

Lemma sic_lset st f i x :
  SIc st -> f = FAsg \/ f = FLvl \/ f = FPh \/ f = FSt \/ f = FSn \/ f = FMisc ->
  SIc (fset st f (lset (fv st f) i x)).
Proof. intros H Hf. apply sic_free; auto. apply lset_length. Qed.

Lemma sic_rsn st i r : SIc st -> r <= length (db st) -> SIc (fset st FRsn (lset (rsn st) i r)).
Proof.
  intros [] Hr. constructor; fvs; auto.
  - now rewrite lset_length.
  - now apply Forall_lset.
Qed.

Lemma sic_tr st xs : SIc st -> Forall lit_ok xs -> SIc (fset st FTr xs).
Proof. intros [] Hx. constructor; fvs; auto. Qed.

Lemma sic_lim st xs : SIc st -> incr xs -> SIc (fset st FLim xs).
Proof. intros [] Hx. constructor; fvs; auto. Qed.

Lemma wok_lset D k cl cl' ci :
  nth_error D k = Some cl -> length cl' = length cl -> wok D ci -> wok (lset D k cl') ci.
Proof.
  intros Hk Hl (c & Hc & H2). destruct (Nat.eqb_spec k ci) as [<- | Hne].
  - rewrite Hk in Hc. injection Hc as <-. exists cl'. split; [| lia].
    apply nth_error_lset_eq, (nth_error_lt' _ _ _ Hk).
  - exists c. split; [| exact H2]. rewrite nth_error_lset_neq; auto.
Qed.

Lemma sic_dset st k cl cl' :
  SIc st -> nth_error (db st) k = Some cl -> length cl' = length cl -> Forall lit_ok cl' ->
  SIc (dset st (lset (db st) k cl')).
Proof.
  intros [] Hk Hl Hc. constructor; fvs; auto.
  - now apply Forall_lset.
  - eapply Forall_impl; [| exact si_w0]. intros L. apply Forall_impl. intros ci. now apply wok_lset with (cl := cl).
  - now rewrite lset_length.
Qed.

Lemma sic_wset st W : SIc st -> length W = 2 * nv -> Forall (Forall (wok (db st))) W -> SIc (wset st W).
Proof. intros [] Hl Hw. constructor; fvs; auto. Qed.

Lemma wok_app D cl ci : wok D ci -> wok (D ++ [cl]) ci.
Proof. intros (c & Hc & H2). exists c. split; [| exact H2]. rewrite nth_error_app1; [exact Hc | eapply nth_error_lt'; eauto]. Qed.

Lemma sic_cpush st c cl : SIc st -> Forall lit_ok cl -> SIc (cpush st c cl).
Proof.
  intros [] Hc. constructor; fvs; auto.
  - apply Forall_app; auto.
  - eapply Forall_impl; [| exact si_w0]. intros L. apply Forall_impl. intros ci. apply wok_app.
  - eapply Forall_impl; [| exact si_r0]. intros r Hr. rewrite length_app. cbn [length] in *. lia.
Qed.

(** A watch list may get any entry naming a long enough clause. *)
Lemma sic_wl_lset st k L : SIc st -> Forall (wok (db st)) L -> SIc (wset st (lset (wl st) k L)).
Proof.
  intros H HL. apply sic_wset; [exact H | rewrite lset_length; apply (si_wl _ H) |].
  apply Forall_lset; [apply (si_w _ H) | exact HL].
Qed.

Lemma lim_lt_grow st st' : lim st' = lim st -> length (tr st) <= length (tr st') -> lim_lt st -> lim_lt st'.
Proof. intros E Hl H. unfold lim_lt in *. rewrite E. revert H. apply Forall_impl. intros x Hx. lia. Qed.



End Safe.

(** * The solver's functions are safe *)

Section Funs.
Variables (s : state) (inp : vec nat) (xs0 : list nat) (nv : nat).

Local Notation R := (repr s inp xs0).
Local Notation keeps := (keeps s inp).
Local Notation SIc := (SIc nv).
Local Notation SI := (SI nv).
Local Notation lit_ok := (lit_ok nv).

Ltac fvs := cbn [fv fset dset wset cpush wpush fld_eqb hcls db hwl wl enq] in *.

Lemma keeps_tr st h1 h2 h3 : keeps st h1 h2 -> keeps st h2 h3 -> keeps st h1 h3.
Proof. intros H1 H2 v xs Hv Hp. auto. Qed.

Lemma db_lit st k cl j l : SIc st -> nth_error (db st) k = Some cl -> nth_error cl j = Some l -> lit_ok l.
Proof.
  intros Hs Hk Hj. eapply Forall_nth_error; [| exact Hj].
  eapply Forall_nth_error; [apply (si_db _ _ Hs) | exact Hk].
Qed.

Lemma tr_lit st j l : SIc st -> nth_error (tr st) j = Some l -> lit_ok l.
Proof. intros Hs Hj. eapply Forall_nth_error; [apply (si_tr _ _ Hs) | exact Hj]. Qed.

Lemma var_ok st f l : SIc st -> lit_ok l ->
  f = FAsg \/ f = FLvl \/ f = FRsn \/ f = FPh \/ f = FSt \/ f = FSn -> lvar l < length (fv st f).
Proof.
  intros [] Hl Hf. apply lvar_lt in Hl.
  destruct Hf as [-> | [-> | [-> | [-> | [-> | ->]]]]]; lia.
Qed.

Lemma lit_value_safe h st l Q :
  R h st -> SIc st -> lit_ok l -> (forall x, Q x h) -> safe (lit_value s l) Q h.
Proof.
  intros Hr Hs Hl HQ. unfold lit_value. apply safe_bind.
  eapply (sget_f s inp xs0 h st Hr FAsg); [apply var_ok; auto |]. intros a _. apply safe_ret, HQ.
Qed.

Lemma enq_sic st l r : SIc st -> lit_ok l -> r <= length (db st) -> SIc (enq st l r).
Proof.
  intros [] Hl Hr. unfold enq. constructor; fvs; rewrite ?lset_length; auto.
  - apply Forall_app. split; [assumption | constructor; auto].
  - now apply Forall_lset.
Qed.

Lemma enq_si st l r : SI st -> lit_ok l -> r <= length (db st) -> SI (enq st l r).
Proof.
  intros [Hs Hl'] Hl Hr. split; [now apply enq_sic|].
  eapply lim_lt_grow; [| | exact Hl']; fvs; [reflexivity | rewrite length_app; lia].
Qed.

Lemma enqueue_safe h st l r Q :
  R h st -> SIc st -> lit_ok l ->
  (forall h', R h' (enq st l r) -> keeps st h h' -> Q tt h') ->
  safe (enqueue s l r) Q h.
Proof.
  intros Hr Hs Hl HQ. unfold enqueue, decision_level. cbv zeta.
  apply safe_bind. eapply (sset_f s inp xs0 h st Hr FAsg); [apply var_ok; auto |]. intros h1 Hr1 Hk1.
  apply safe_bind. eapply (slen_f s inp xs0 h1 _ Hr1 FLim). cbv beta.
  apply safe_bind. eapply (sset_f s inp xs0 h1 _ Hr1 FLvl); [fvs; apply var_ok; auto |]. intros h2 Hr2 Hk2.
  apply safe_bind. eapply (sset_f s inp xs0 h2 _ Hr2 FRsn); [fvs; apply var_ok; auto |]. intros h3 Hr3 Hk3.
  eapply (spush_f s inp xs0 h3 _ Hr3 FTr). intros h4 Hr4 Hk4.
  eapply HQ; [exact Hr4 |].
  eapply keeps_tr; [exact Hk1|]. eapply keeps_tr; [exact Hk2|]. eapply keeps_tr; eassumption.
Qed.

Lemma find_watch_safe fuel : forall h st ci c cl k Q,
  R h st -> SIc st -> nth_error (hcls st) ci = Some c -> nth_error (db st) ci = Some cl ->
  (forall r, (r <> 0 -> r - 1 < length cl) -> Q r h) ->
  safe (find_watch s fuel c k (length cl)) Q h.
Proof.
  induction fuel as [|f IH]; intros h st ci c cl k Q Hr Hs Hc Hd HQ; cbn [find_watch].
  - apply safe_vabort.
  - destruct (Nat.leb_spec (length cl) k).
    + apply safe_ret, HQ. lia.
    + apply safe_bind. eapply (sget_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hd | exact H |].
      intros x Hx. apply safe_bind. eapply lit_value_safe; [exact Hr | exact Hs | eapply db_lit; eauto |].
      intros v. destruct (Nat.eqb v 2).
      * eapply IH; eauto.
      * apply safe_ret, HQ. lia.
Qed.

Lemma copy_rest_safe fuel : forall h st fl ws L i j n Q,
  R h st -> SIc st -> nth_error (hwl st) fl = Some ws -> nth_error (wl st) fl = Some L ->
  n <= length L -> j <= i -> i <= n ->
  (forall h' L', R h' (wset st (lset (wl st) fl L')) -> Forall (wok (db st)) L' -> Q tt h') ->
  safe (copy_rest fuel ws i j n) Q h.
Proof.
  induction fuel as [|f IH]; intros h st fl ws L i j n Q Hr Hs Hw HL Hn Hji Hin HQ; cbn [copy_rest].
  - apply safe_vabort.
  - assert (FL : Forall (wok (db st)) L) by (eapply Forall_nth_error; [apply (si_w _ _ Hs) | exact HL]).
    destruct (Nat.leb_spec n i).
    + eapply (sshrink_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL | lia |]. intros h' Hr' _.
      apply (HQ h' (firstn j L)); [exact Hr' |]. now apply Forall_firstn'.
    + apply safe_bind. eapply (sget_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL | lia |]. intros x Hx.
      apply safe_bind. eapply (sset_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL | lia |]. intros h1 Hr1 _.
      assert (Hfl : fl < length (wl st)) by (eapply nth_error_lt'; eauto).
      eapply IH; [exact Hr1 | | fvs; exact Hw | fvs; now apply nth_error_lset_eq | rewrite lset_length; lia | lia | lia |].
      * apply sic_wl_lset; [exact Hs |]. apply Forall_lset; [exact FL |]. eapply Forall_nth_error; eauto.
      * intros h' L' Hr' HL'. fvs. apply (HQ h' L'); [| exact HL'].
        rewrite lset_lset in Hr'. exact Hr'.
Qed.
Lemma wl_ok st fl L : SIc st -> nth_error (wl st) fl = Some L -> Forall (wok (db st)) L.
Proof. intros Hs HL. eapply Forall_nth_error; [apply (si_w _ _ Hs) | exact HL]. Qed.

Lemma si_wl_lset st k L : SI st -> Forall (wok (db st)) L -> SI (wset st (lset (wl st) k L)).
Proof. intros [Hs Hl] HL. split; [now apply sic_wl_lset | exact Hl]. Qed.

Lemma si_dset st k cl cl' :
  SI st -> nth_error (db st) k = Some cl -> length cl' = length cl -> Forall lit_ok cl' ->
  SI (dset st (lset (db st) k cl')).
Proof. intros [Hs Hl] Hk Hc HL. split; [eapply sic_dset; eauto | exact Hl]. Qed.

Lemma prop_watch_safe fuel : forall h st fl ws L i j n Q,
  R h st -> SI st -> nth_error (hwl st) fl = Some ws -> nth_error (wl st) fl = Some L ->
  n <= length L -> j <= i -> i <= n -> lit_ok fl ->
  (forall r h' st', R h' st' -> SI st' -> (r <> 0 -> r - 1 < length (db st')) -> Q r h') ->
  safe (prop_watch s fuel fl ws i j n) Q h.
Proof.
  induction fuel as [|f IH]; intros h st fl ws L i j n Q Hr Hsi Hw HL Hn Hji Hin Hfl HQ; cbn [prop_watch].
  { apply safe_vabort. }
  pose proof (proj1 Hsi) as Hs.
  assert (Hfw : fl < length (wl st)) by (eapply nth_error_lt'; eauto).
  destruct (Nat.leb_spec n i).
  { apply safe_bind. eapply (sshrink_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL | lia |].
    intros h' Hr' _. apply safe_ret. eapply HQ; [exact Hr' | | lia].
    apply si_wl_lset; [exact Hsi |]. apply Forall_firstn'. eapply wl_ok; eauto. }
  apply safe_bind. eapply (sget_w s inp xs0 h st Hr fl ws L); [exact Hw | exact HL | lia |]. intros ci Hci.
  destruct (Forall_nth_error _ _ _ _ (wl_ok _ _ _ Hs HL) Hci) as (cl & Hcl & H2).
  apply safe_bind. eapply (sget_hc s inp xs0 h st Hr); [eapply nth_error_lt'; eauto |]. intros c Hc.
  apply safe_bind. eapply (sget_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hcl | lia |]. intros c0 Hc0.
  apply safe_seq with (P := fun _ h1 => exists st1 cl1, R h1 st1 /\ SI st1 /\ hwl st1 = hwl st /\
      wl st1 = wl st /\ nth_error (hcls st1) ci = Some c /\ nth_error (db st1) ci = Some cl1 /\
      length cl1 = length cl).
  { destruct (Nat.eqb c0 fl).
    - apply safe_bind. eapply (sget_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hcl | lia |]. intros c1 Hc1.
      apply safe_bind. eapply (sset_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hcl | lia |]. intros h2 Hr2 _.
      assert (Hcl2 : nth_error (db (dset st (lset (db st) ci (lset cl 0 c1)))) ci = Some (lset cl 0 c1))
        by (fvs; apply nth_error_lset_eq; eapply nth_error_lt'; eauto).
      eapply (sset_cl s inp xs0 h2 _ Hr2 ci c); [fvs; exact Hc | exact Hcl2 | rewrite lset_length; lia |].
      intros h3 Hr3 _. eexists _, _. split; [exact Hr3 |]. fvs.
      assert (Hl1 : lit_ok c1) by (eapply db_lit; eauto).
      assert (Hsi2 : SI (dset st (lset (db st) ci (lset cl 0 c1))))
        by (eapply si_dset; eauto; [apply lset_length | apply Forall_lset; auto;
            eapply Forall_nth_error; [apply (si_db _ _ Hs) | exact Hcl]]).
      split; [| split; [reflexivity | split; [reflexivity | split; [exact Hc | split]]]].
      + eapply si_dset; [exact Hsi2 | exact Hcl2 | apply lset_length |].
        apply Forall_lset; [| exact Hfl]. eapply Forall_nth_error; [apply (si_db _ _ (proj1 Hsi2)) | exact Hcl2].
      + rewrite lset_lset. apply nth_error_lset_eq. eapply nth_error_lt'; eauto.
      + now rewrite !lset_length.
    - apply safe_ret. exists st, cl. auto 7. }
  intros [] h1 (st1 & cl1 & Hr1 & Hsi1 & Ehw & Ewl & Hc1 & Hcl1 & Hlen1). cbv beta.
  pose proof (proj1 Hsi1) as Hs1.
  assert (Hw1 : nth_error (hwl st1) fl = Some ws) by (rewrite Ehw; exact Hw).
  assert (HL1 : nth_error (wl st1) fl = Some L) by (rewrite Ewl; exact HL).
  assert (Hfw1 : fl < length (wl st1)) by (rewrite Ewl; exact Hfw).
  assert (Hok : wok (db st1) ci) by (exists cl1; split; [exact Hcl1 | lia]).
  assert (FL1 := wl_ok _ _ _ Hs1 HL1).
  apply safe_bind. eapply (sget_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc1 | exact Hcl1 | lia |].
  intros first Hfirst. assert (Hlf : lit_ok first) by (eapply db_lit; eauto).
  apply safe_bind. eapply lit_value_safe; [exact Hr1 | exact Hs1 | exact Hlf |]. intros fv1.
  (* Keeping [ci] at position [j] of the list being visited. *)
  assert (Keep : forall Q', (forall h2, R h2 (wset st1 (lset (wl st1) fl (lset L j ci))) -> Q' tt h2) ->
                   safe (vset ws j ci) Q' h1).
  { intros Q' HQ'. eapply (sset_w s inp xs0 h1 st1 Hr1 fl ws L); [exact Hw1 | exact HL1 | lia |].
    intros h2 Hr2 _. now apply HQ'. }
  assert (SIk : SI (wset st1 (lset (wl st1) fl (lset L j ci))))
    by (apply si_wl_lset; [exact Hsi1 | now apply Forall_lset]).
  assert (HLk : nth_error (wl (wset st1 (lset (wl st1) fl (lset L j ci)))) fl = Some (lset L j ci))
    by (fvs; now apply nth_error_lset_eq).
  destruct (Nat.eqb fv1 1).
  { apply safe_bind. apply Keep. intros h2 Hr2.
    eapply IH; [exact Hr2 | exact SIk | fvs; exact Hw1 | exact HLk | rewrite lset_length; lia | lia | lia | exact Hfl | exact HQ]. }
  apply safe_bind. eapply (slen_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc1 | exact Hcl1 |].
  apply safe_bind. eapply find_watch_safe; [exact Hr1 | exact Hs1 | exact Hc1 | exact Hcl1 |]. intros k1 Hk1.
  destruct (Nat.eqb_spec k1 0) as [_ | Hk0].
  { apply safe_bind. apply Keep. intros h2 Hr2. destruct (Nat.eqb fv1 2).
    - apply safe_bind. eapply copy_rest_safe; [exact Hr2 | exact (proj1 SIk) | fvs; exact Hw1 | exact HLk
        | rewrite lset_length; lia | lia | lia |].
      intros h3 L' Hr3 HL'. apply safe_ret. eapply HQ; [exact Hr3 | apply si_wl_lset; [exact SIk | exact HL'] |].
      intros _. fvs. pose proof (nth_error_lt' _ _ _ Hcl1). lia.
    - apply safe_bind. eapply enqueue_safe; [exact Hr2 | exact (proj1 SIk) | exact Hlf |]. intros h3 Hr3 _.
      eapply IH; [exact Hr3 | apply enq_si; [exact SIk | exact Hlf | fvs; pose proof (nth_error_lt' _ _ _ Hcl1); lia]
        | fvs; exact Hw1 | fvs; exact HLk | rewrite lset_length; lia | lia | lia | exact Hfl | exact HQ]. }
  specialize (Hk1 Hk0). cbv zeta.
  apply safe_bind. eapply (sget_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc1 | exact Hcl1 | lia |].
  intros ck Hck. assert (Hlk : lit_ok ck) by (eapply db_lit; eauto).
  apply safe_bind. eapply (sset_cl s inp xs0 h1 st1 Hr1 ci c cl1); [exact Hc1 | exact Hcl1 | lia |]. intros h2 Hr2 _.
  set (st2 := dset st1 (lset (db st1) ci (lset cl1 1 ck))) in Hr2.
  assert (Hcl2 : nth_error (db st2) ci = Some (lset cl1 1 ck))
    by (unfold st2; fvs; apply nth_error_lset_eq; eapply nth_error_lt'; eauto).
  assert (Hsi2 : SI st2).
  { eapply si_dset; [exact Hsi1 | exact Hcl1 | apply lset_length |]. apply Forall_lset; [| exact Hlk].
    eapply Forall_nth_error; [apply (si_db _ _ Hs1) | exact Hcl1]. }
  apply safe_bind. eapply (sset_cl s inp xs0 h2 st2 Hr2 ci c); [unfold st2; fvs; exact Hc1 | exact Hcl2 | rewrite lset_length; lia |].
  intros h3 Hr3 _.
  set (st3 := dset st2 (lset (db st2) ci (lset (lset cl1 1 ck) (k1 - 1) fl))) in Hr3.
  assert (Hsi3 : SI st3).
  { eapply si_dset; [exact Hsi2 | exact Hcl2 | apply lset_length |]. apply Forall_lset; [| exact Hfl].
    eapply Forall_nth_error; [apply (si_db _ _ (proj1 Hsi2)) | exact Hcl2]. }
  assert (Hok3 : wok (db st3) ci).
  { exists (lset (lset cl1 1 ck) (k1 - 1) fl). split; [| rewrite !lset_length; lia].
    unfold st3; fvs. apply nth_error_lset_eq. eapply nth_error_lt'; eauto. }
  assert (Ewl3 : wl st3 = wl st1) by reflexivity.
  assert (Hwl3 : length (wl st3) = 2 * nv) by apply (si_wl _ _ (proj1 Hsi3)).
  apply safe_bind. eapply (sget_hw s inp xs0 h3 st3 Hr3); [unfold lit_ok in Hlk; lia |]. intros w Hwk.
  destruct (nth_error (wl st3) ck) as [Lk|] eqn:HLk3; [| apply nth_error_None in HLk3; unfold lit_ok in Hlk; lia].
  apply safe_bind. eapply (spush_w s inp xs0 h3 st3 Hr3 ck w Lk); [exact Hwk | exact HLk3 |]. intros h4 Hr4 _.
  assert (Hsi4 : SI (wset st3 (lset (wl st3) ck (Lk ++ [ci])))).
  { apply si_wl_lset; [exact Hsi3 |]. apply Forall_app. split; [| constructor; [exact Hok3 | constructor]].
    eapply wl_ok; [exact (proj1 Hsi3) | exact HLk3]. }
  destruct (Nat.eq_dec ck fl) as [-> | Hne].
  - rewrite Ewl3, HL1 in HLk3. injection HLk3 as <-.
    eapply IH; [exact Hr4 | exact Hsi4 | fvs; exact Hw1 | fvs; apply nth_error_lset_eq; first [lia | rewrite Ewl3; lia | unfold st3, st2; fvs; lia]
      | rewrite length_app; lia | lia | lia | exact Hfl | exact HQ].
  - eapply IH; [exact Hr4 | exact Hsi4 | fvs; exact Hw1 | fvs; rewrite nth_error_lset_neq by exact Hne; exact HL1
      | lia | lia | lia | exact Hfl | exact HQ].
Qed.

Lemma propagate_safe fuel : forall h st Q,
  R h st -> SI st ->
  (forall r h' st', R h' st' -> SI st' -> (r <> 0 -> r - 1 < length (db st')) -> Q r h') ->
  safe (propagate s fuel) Q h.
Proof.
  induction fuel as [|f IH]; intros h st Q Hr Hsi HQ; cbn [propagate].
  { apply safe_vabort. }
  pose proof (proj1 Hsi) as Hs.
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FMisc); [rewrite (si_misc _ _ Hs); unfold QHEAD; lia |].
  intros qh _.
  apply safe_bind. eapply (slen_f s inp xs0 h st Hr FTr). cbv beta.
  destruct (Nat.leb_spec (length (tr st)) qh).
  { apply safe_ret. eapply HQ; eauto. lia. }
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FTr); [lia |]. intros p Hp.
  assert (Hlp : lit_ok p) by (eapply tr_lit; eauto).
  apply safe_bind. eapply (sset_f s inp xs0 h st Hr FMisc); [rewrite (si_misc _ _ Hs); unfold QHEAD; lia |].
  intros h1 Hr1 _. cbv zeta.
  set (st1 := fset st FMisc _) in Hr1.
  assert (Hsi1 : SI st1) by (split; [apply sic_lset; auto 7 | exact (proj2 Hsi)]).
  assert (Hln : lit_ok (lneg p)) by (now apply lneg_lt).
  assert (Hwl1 : length (wl st1) = 2 * nv) by apply (si_wl _ _ (proj1 Hsi1)).
  apply safe_bind. eapply (sget_hw s inp xs0 h1 st1 Hr1); [unfold lit_ok in Hln; lia |]. intros ws Hws.
  destruct (nth_error (wl st1) (lneg p)) as [L|] eqn:HL; [| apply nth_error_None in HL; unfold lit_ok in Hln; lia].
  apply safe_bind. eapply (slen_w s inp xs0 h1 st1 Hr1 (lneg p) ws L); [exact Hws | exact HL |].
  apply safe_bind. eapply prop_watch_safe; [exact Hr1 | exact Hsi1 | exact Hws | exact HL | lia | lia | lia | exact Hln |].
  intros confl h2 st2 Hr2 Hsi2 Hc. destruct (Nat.eqb_spec confl 0) as [-> | Hne].
  - eapply IH; eauto.
  - apply safe_ret. eapply HQ; eauto.
Qed.

(** ** Backtracking *)

(** Only per-variable cells and counters changed. *)
Definition same (st st' : astate) : Prop :=
  hcls st' = hcls st /\ hwl st' = hwl st /\ db st' = db st /\ wl st' = wl st /\
  tr st' = tr st /\ lim st' = lim st.

Lemma same_refl st : same st st.
Proof. repeat split. Qed.

Lemma same_trans a b c : same a b -> same b c -> same a c.
Proof. intros (E1 & E2 & E3 & E4 & E5 & E6) (F1 & F2 & F3 & F4 & F5 & F6). repeat split; congruence. Qed.

Lemma same_fset st f xs : f <> FTr -> f <> FLim -> same st (fset st f xs).
Proof.
  intros H1 H2. unfold same. fvs. repeat split.
  - destruct f; try reflexivity; congruence.
  - destruct f; try reflexivity; congruence.
Qed.

Lemma si_same st st' : SI st -> SIc st' -> same st st' -> SI st'.
Proof.
  intros [_ Hl] Hs (_ & _ & _ & _ & E5 & E6). split; [exact Hs|]. unfold lim_lt in *. now rewrite E5, E6.
Qed.

Lemma locs_same st st' : hcls st' = hcls st -> hwl st' = hwl st -> locs s inp st' = locs s inp st.
Proof. intros E1 E2. unfold locs. now rewrite E1, E2. Qed.

Lemma keeps_same st st' h1 h2 : same st st' -> keeps st' h1 h2 -> keeps st h1 h2.
Proof.
  intros (E1 & E2 & _) H. unfold SolverRepr.keeps in *. rewrite <- (locs_same st st' E1 E2). exact H.
Qed.

Lemma unassign_safe fuel : forall h st i m Q,
  R h st -> SIc st -> i <= length (tr st) ->
  (forall h' st', R h' st' -> SIc st' -> same st st' -> keeps st h h' -> Q tt h') ->
  safe (unassign s fuel i m) Q h.
Proof.
  induction fuel as [|f IH]; intros h st i m Q Hr Hs Hi HQ; cbn [unassign].
  { apply safe_vabort. }
  destruct (Nat.leb_spec i m).
  { apply safe_ret. apply (HQ h st); auto using same_refl, keeps_refl. }
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FTr); [lia |]. intros l Hl.
  assert (Hll : lit_ok l) by (eapply tr_lit; eauto). cbv zeta.
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FAsg); [apply var_ok; auto |]. intros a _.
  apply safe_bind. eapply (sset_f s inp xs0 h st Hr FPh); [apply var_ok; auto 7 |]. intros h1 Hr1 Hk1.
  set (st1 := fset st FPh _) in Hr1.
  assert (Hs1 : SIc st1) by (apply sic_lset; auto 7).
  apply safe_bind. eapply (sset_f s inp xs0 h1 st1 Hr1 FAsg); [apply var_ok; auto |]. intros h2 Hr2 Hk2.
  set (st2 := fset st1 FAsg _) in Hr2.
  assert (Hs2 : SIc st2) by (apply sic_lset; auto 7).
  apply safe_bind. eapply (sset_f s inp xs0 h2 st2 Hr2 FRsn); [apply var_ok; auto 7 |]. intros h3 Hr3 Hk3.
  set (st3 := fset st2 FRsn _) in Hr3.
  assert (Hs3 : SIc st3) by (apply sic_rsn; [exact Hs2 | lia]).
  assert (S3 : same st st3) by (repeat split).
  eapply IH; [exact Hr3 | exact Hs3 | unfold st3, st2, st1; fvs; lia |].
  intros h' st' Hr' Hs' S' Hk'. eapply HQ; [exact Hr' | exact Hs' | eapply same_trans; [exact S3 | exact S'] |].
  apply (keeps_same st st3) in Hk'; [| exact S3]. unfold SolverRepr.keeps in *.
  intros v xs Hv Hp. apply Hk'; [exact Hv |]. apply Hk3; [exact Hv |]. apply Hk2; [exact Hv |]. auto.
Qed.

Lemma incr_firstn n l : incr l -> incr (firstn n l).
Proof.
  intros H i j a b Hij Ha Hb. rewrite nth_error_firstn in Ha, Hb.
  destruct (Nat.ltb i n), (Nat.ltb j n); try discriminate. eauto.
Qed.

Lemma incr_snoc l x : incr l -> Forall (fun y => y < x) l -> incr (l ++ [x]).
Proof.
  intros H Hx i j a b Hij Ha Hb.
  assert (Hj : j < length (l ++ [x])) by (eapply nth_error_lt'; eauto). rewrite length_app in Hj. cbn in Hj.
  rewrite nth_error_app1 in Ha by lia.
  destruct (Nat.eq_dec j (length l)) as [-> | Hne].
  - rewrite nth_error_app2, Nat.sub_diag in Hb by lia. cbn in Hb. injection Hb as <-.
    exact (Forall_nth_error _ _ _ _ Hx Ha).
  - rewrite nth_error_app1 in Hb by lia. eauto.
Qed.

Lemma backtrack_safe fuel h st lv Q :
  R h st -> SI st ->
  (forall h' st', R h' st' -> SI st' -> hcls st' = hcls st -> hwl st' = hwl st -> db st' = db st ->
     keeps st h h' -> Q tt h') ->
  safe (backtrack s fuel lv) Q h.
Proof.
  intros Hr [Hs Hl] HQ. unfold backtrack, decision_level.
  apply safe_bind. eapply (slen_f s inp xs0 h st Hr FLim). cbv beta.
  destruct (Nat.leb_spec (length (lim st)) lv).
  { apply safe_ret. apply (HQ h st); auto using keeps_refl. split; auto. }
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FLim); [lia |]. intros x Hx.
  assert (Hxt : x < length (tr st)) by exact (Forall_nth_error _ _ _ _ Hl Hx).
  apply safe_bind. eapply (slen_f s inp xs0 h st Hr FTr). cbv beta.
  apply safe_bind. eapply unassign_safe; [exact Hr | exact Hs | lia |]. intros h1 st1 Hr1 Hs1 S1 Hk1.
  destruct S1 as (E1 & E2 & E3 & E4 & E5 & E6).
  apply safe_bind. eapply (sshrink_f s inp xs0 h1 st1 Hr1 FTr); [rewrite E5; lia |]. intros h2 Hr2 Hk2.
  apply safe_bind. eapply (sshrink_f s inp xs0 h2 _ Hr2 FLim); [fvs; rewrite E6; lia |]. intros h3 Hr3 Hk3.
  eapply (sset_f s inp xs0 h3 _ Hr3 FMisc); [fvs; rewrite (si_misc _ _ Hs1); unfold QHEAD; lia |].
  intros h4 Hr4 Hk4. eapply HQ; [exact Hr4 | | fvs; auto | fvs; auto | fvs; auto |].
  - split.
    + apply sic_lset; [| auto 7]. apply sic_lim; [apply sic_tr; [exact Hs1 |] |].
      * apply Forall_firstn', (si_tr _ _ Hs1).
      * fvs. apply incr_firstn, (si_inc _ _ Hs1).
    + unfold lim_lt. fvs. rewrite E5, E6, length_firstn, Nat.min_l by lia.
      apply Forall_forall. intros y Hy. apply In_nth_error in Hy as (k & Hk).
      rewrite nth_error_firstn in Hk. destruct (Nat.ltb_spec k lv); [| discriminate].
      eapply (si_inc _ _ Hs); [exact H0 | exact Hk | exact Hx].
  - unfold SolverRepr.keeps in *. pose proof (locs_same st st1 E1 E2) as EL.
    intros v xs Hv Hp. assert (Hv1 : ~ In (vloc v) (locs s inp st1)) by (rewrite EL; exact Hv).
    apply Hk4; [exact Hv1 |]. apply Hk3; [exact Hv1 |]. apply Hk2; [exact Hv1 |]. auto.
Qed.

(** ** Conflict analysis *)

Lemma learnt_kept st st' h h' learnt Lr :
  same st st' -> keeps st' h h' -> ~ In (vloc learnt) (locs s inp st) -> pts h learnt Lr -> pts h' learnt Lr.
Proof. intros S Hk Hn Hp. eapply keeps_same in Hk; [| exact S]. exact (Hk _ _ Hn Hp). Qed.

Lemma tl_app {A} (xs : list A) x : 1 <= length xs -> tl (xs ++ [x]) = tl xs ++ [x].
Proof. destruct xs; cbn; [lia | reflexivity]. Qed.

Lemma analyze_lits_safe fuel : forall h st ci c cl j dl pathC learnt Lr now Q,
  R h st -> SI st -> nth_error (hcls st) ci = Some c -> nth_error (db st) ci = Some cl ->
  ~ In (vloc learnt) (locs s inp st) -> pts h learnt Lr -> 1 <= length Lr -> Forall lit_ok (tl Lr) ->
  (forall r h' st' Lr', R h' st' -> SI st' -> same st st' -> pts h' learnt Lr' -> 1 <= length Lr' ->
     Forall lit_ok (tl Lr') -> Q r h') ->
  safe (analyze_lits s fuel c j (length cl) dl pathC learnt now) Q h.
Proof.
  induction fuel as [|f IH]; intros h st ci c cl j dl pathC learnt Lr now Q Hr Hsi Hc Hcl Hn Hp H1 Hlr HQ;
    cbn [analyze_lits].
  { apply safe_vabort. }
  pose proof (proj1 Hsi) as Hs.
  destruct (Nat.leb_spec (length cl) j).
  { apply safe_ret. eapply HQ; eauto using same_refl. }
  apply safe_bind. eapply (sget_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hcl | lia |]. intros q Hq.
  assert (Hlq : lit_ok q) by (eapply db_lit; eauto). cbv zeta.
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FSn); [apply var_ok; auto 7 |]. intros sv _.
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FLvl); [apply var_ok; auto 7 |]. intros lv _.
  destruct (Nat.eqb sv 0 && Nat.ltb 0 lv).
  2: { eapply IH; eauto. }
  apply safe_bind. eapply (sset_f s inp xs0 h st Hr FSn); [apply var_ok; auto 7 |]. intros h1 Hr1 Hk1.
  set (st1 := fset st FSn _) in Hr1.
  assert (Hs1 : SIc st1) by (apply sic_lset; auto 7).
  assert (S1 : same st st1) by (apply same_fset; discriminate).
  apply safe_bind. eapply (sset_f s inp xs0 h1 st1 Hr1 FSt); [apply var_ok; auto 7 |]. intros h2 Hr2 Hk2.
  set (st2 := fset st1 FSt _) in Hr2.
  assert (Hs2 : SIc st2) by (apply sic_lset; auto 7).
  assert (S2 : same st st2) by (repeat split).
  assert (Hsi2 : SI st2) by (eapply si_same; eauto).
  assert (Hp2 : pts h2 learnt Lr).
  { eapply learnt_kept; [exact S1 | exact Hk2 | exact Hn |]. exact (Hk1 _ _ Hn Hp). }
  destruct (Nat.leb dl lv).
  - eapply IH; [exact Hr2 | exact Hsi2 | exact Hc | exact Hcl | exact Hn | exact Hp2 | exact H1 | exact Hlr |].
    intros r h' st' Lr' Hr' Hsi' S' Hp' H1' Hlr'. eapply HQ; eauto; eapply same_trans; eauto.
  - apply safe_bind. eapply (spush_scr s inp xs0 h2 st2 Hr2 learnt Lr q); [exact Hn | exact Hp2 |].
    intros h3 Hr3 Hp3.
    eapply IH; [exact Hr3 | exact Hsi2 | exact Hc | exact Hcl | exact Hn | exact Hp3 | rewrite length_app; lia | |].
    + rewrite tl_app by exact H1. apply Forall_app. auto.
    + intros r h' st' Lr' Hr' Hsi' S' Hp' H1' Hlr'. eapply HQ; eauto; eapply same_trans; eauto.
Qed.

Lemma next_seen_safe fuel : forall h st i Q,
  R h st -> SIc st -> i < length (tr st) -> (forall r, r < length (tr st) -> Q r h) ->
  safe (next_seen s fuel i) Q h.
Proof.
  induction fuel as [|f IH]; intros h st i Q Hr Hs Hi HQ; cbn [next_seen].
  { apply safe_vabort. }
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FTr); [exact Hi |]. intros l Hl.
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FSn); [apply var_ok; auto 7; eapply tr_lit; eauto |].
  intros sv _. destruct (Nat.eqb sv 0).
  - eapply IH; eauto. lia.
  - apply safe_ret, HQ, Hi.
Qed.

Lemma analyze_loop_safe fuel : forall h st confl start index pathC dl learnt Lr now Q,
  R h st -> SI st -> confl < length (db st) -> index < length (tr st) ->
  ~ In (vloc learnt) (locs s inp st) -> pts h learnt Lr -> 1 <= length Lr -> Forall lit_ok (tl Lr) ->
  (forall p h' st' Lr', R h' st' -> SI st' -> same st st' -> pts h' learnt Lr' -> 1 <= length Lr' ->
     Forall lit_ok (tl Lr') -> lit_ok p -> Q p h') ->
  safe (analyze_loop s fuel confl start index pathC dl learnt now) Q h.
Proof.
  induction fuel as [|f IH]; intros h st confl start index pathC dl learnt Lr now Q Hr Hsi Hcf Hix Hn Hp H1 Hlr HQ;
    cbn [analyze_loop].
  { apply safe_vabort. }
  apply safe_bind. eapply (sget_hc s inp xs0 h st Hr); [exact Hcf |]. intros c Hc.
  destruct (nth_error (db st) confl) as [cl|] eqn:Hcl; [| apply nth_error_None in Hcl; lia].
  apply safe_bind. eapply (slen_cl s inp xs0 h st Hr confl c cl); [exact Hc | exact Hcl |].
  apply safe_bind. eapply analyze_lits_safe; [exact Hr | exact Hsi | exact Hc | exact Hcl | exact Hn | exact Hp | exact H1 | exact Hlr |].
  intros pathC' h1 st1 Lr1 Hr1 Hsi1 S1 Hp1 H11 Hlr1.
  pose proof S1 as (E1 & E2 & E3 & E4 & E5 & E6).
  apply safe_bind. eapply next_seen_safe; [exact Hr1 | exact (proj1 Hsi1) | rewrite E5; exact Hix |]. intros idx Hidx.
  apply safe_bind. eapply (sget_f s inp xs0 h1 st1 Hr1 FTr); [exact Hidx |]. intros p Hpp.
  assert (Hlp : lit_ok p) by (eapply tr_lit; [exact (proj1 Hsi1) | exact Hpp]). cbv zeta.
  apply safe_bind. eapply (sget_f s inp xs0 h1 st1 Hr1 FRsn); [apply var_ok; auto 7; exact (proj1 Hsi1) |].
  intros r Hrr. assert (Hrd : r <= length (db st1)) by exact (Forall_nth_error _ _ _ _ (si_r _ _ (proj1 Hsi1)) Hrr).
  apply safe_bind. eapply (sset_f s inp xs0 h1 st1 Hr1 FSn); [apply var_ok; auto 7; exact (proj1 Hsi1) |].
  intros h2 Hr2 Hk2. set (st2 := fset st1 FSn _) in Hr2.
  assert (S2 : same st1 st2) by (apply same_fset; discriminate).
  assert (Hsi2 : SI st2) by (eapply si_same; [exact Hsi1 | apply sic_lset; [exact (proj1 Hsi1) | auto 7] | exact S2]).
  assert (Hn1 : ~ In (vloc learnt) (locs s inp st1)) by (rewrite (locs_same st st1 E1 E2); exact Hn).
  assert (Hp2 : pts h2 learnt Lr1) by exact (Hk2 _ _ Hn1 Hp1).
  destruct (Nat.leb pathC' 1).
  - apply safe_ret. eapply HQ; [exact Hr2 | exact Hsi2 | eapply same_trans; [exact S1 | exact S2] | exact Hp2 | exact H11 | exact Hlr1 | exact Hlp].
  - eapply IH; [exact Hr2 | exact Hsi2 | unfold st2; fvs; rewrite E3 in *; lia | unfold st2; fvs; lia
      | unfold st2; fvs; exact Hn1 | exact Hp2 | exact H11 | exact Hlr1 |].
    intros p' h' st' Lr' Hr' Hsi' S' Hp' H1' Hlr' Hlp'.
    eapply HQ; [exact Hr' | exact Hsi' | | exact Hp' | exact H1' | exact Hlr' | exact Hlp'].
    eapply same_trans; [exact S1 | eapply same_trans; [exact S2 | exact S']].
Qed.

Lemma finish_learnt_safe fuel : forall h st learnt Lr i best bestlv Q,
  R h st -> SI st -> ~ In (vloc learnt) (locs s inp st) -> pts h learnt Lr -> Forall lit_ok Lr ->
  i <= length Lr -> best = 0 \/ best < i ->
  (forall r h' st' Lr', R h' st' -> SI st' -> same st st' -> pts h' learnt Lr' -> Forall lit_ok Lr' ->
     length Lr' = length Lr -> Q r h') ->
  safe (finish_learnt s fuel learnt i (length Lr) best bestlv) Q h.
Proof.
  induction fuel as [|f IH]; intros h st learnt Lr i best bestlv Q Hr Hsi Hn Hp Hlr Hi Hb HQ;
    cbn [finish_learnt].
  { apply safe_vabort. }
  destruct (Nat.leb_spec (length Lr) i).
  { apply safe_seq with (P := fun _ h' => exists Lr', R h' st /\ pts h' learnt Lr' /\ Forall lit_ok Lr' /\
                                            length Lr' = length Lr).
    - destruct (Nat.ltb_spec 1 best).
      + apply safe_bind. eapply (sget_pts h learnt Lr); [exact Hp | lia |]. intros b Hb'.
        apply safe_bind. eapply (sget_pts h learnt Lr); [exact Hp | lia |]. intros x Hx.
        apply safe_bind. eapply (sset_scr s inp xs0 h st Hr learnt Lr 1 b); [exact Hn | exact Hp | lia |].
        intros h1 Hr1 Hp1.
        eapply (sset_scr s inp xs0 h1 st Hr1 learnt _ best x); [exact Hn | exact Hp1 | rewrite lset_length; lia |].
        intros h2 Hr2 Hp2. eexists. split; [exact Hr2 | split; [exact Hp2 | split]].
        * apply Forall_lset; [apply Forall_lset; [exact Hlr |] |]; eapply Forall_nth_error; eauto.
        * now rewrite !lset_length.
      + apply safe_ret. eauto.
    - intros [] h' (Lr' & Hr' & Hp' & Hlr' & HL'). apply safe_ret. eapply HQ; eauto using same_refl. }
  apply safe_bind. eapply (sget_pts h learnt Lr); [exact Hp | lia |]. intros q Hq.
  assert (Hlq : lit_ok q) by (eapply Forall_nth_error; eauto). cbv zeta.
  apply safe_bind. eapply (sset_f s inp xs0 h st Hr FSn); [apply var_ok; auto 7; exact (proj1 Hsi) |].
  intros h1 Hr1 Hk1. set (st1 := fset st FSn _) in Hr1.
  assert (S1 : same st st1) by (apply same_fset; discriminate).
  assert (Hsi1 : SI st1) by (eapply si_same; [exact Hsi | apply sic_lset; [exact (proj1 Hsi) | auto 7] | exact S1]).
  assert (Hp1 : pts h1 learnt Lr) by exact (Hk1 _ _ Hn Hp).
  apply safe_bind. eapply (sget_f s inp xs0 h1 st1 Hr1 FLvl); [apply var_ok; auto 7; exact (proj1 Hsi1) |].
  intros lv _.
  assert (HQ' : forall r h' st' Lr', R h' st' -> SI st' -> same st1 st' -> pts h' learnt Lr' ->
                  Forall lit_ok Lr' -> length Lr' = length Lr -> Q r h')
    by (intros; eapply HQ; eauto; eapply same_trans; eauto).
  destruct (Nat.ltb bestlv lv).
  - eapply IH; [exact Hr1 | exact Hsi1 | exact Hn | exact Hp1 | exact Hlr | lia | right; lia | exact HQ'].
  - eapply IH; [exact Hr1 | exact Hsi1 | exact Hn | exact Hp1 | exact Hlr | lia | lia | exact HQ'].
Qed.

Lemma attach_safe h st ci c cl Q :
  R h st -> SI st -> nth_error (hcls st) ci = Some c -> nth_error (db st) ci = Some cl -> 2 <= length cl ->
  (forall h' st', R h' st' -> SI st' -> hcls st' = hcls st -> db st' = db st -> Q tt h') ->
  safe (attach s ci c) Q h.
Proof.
  intros Hr Hsi Hc Hcl H2 HQ. pose proof (proj1 Hsi) as Hs. unfold attach.
  assert (Hok : wok (db st) ci) by (exists cl; auto).
  apply safe_bind. eapply (sget_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hcl | lia |]. intros c0 H0.
  apply safe_bind. eapply (sget_cl s inp xs0 h st Hr ci c cl); [exact Hc | exact Hcl | lia |]. intros c1 H1.
  assert (L0 : lit_ok c0) by (eapply db_lit; eauto). assert (L1 : lit_ok c1) by (eapply db_lit; eauto).
  unfold lit_ok in L0, L1. pose proof (si_wl _ _ Hs) as Hwl.
  apply safe_bind. eapply (sget_hw s inp xs0 h st Hr); [lia |]. intros w0 Hw0.
  destruct (nth_error (wl st) c0) as [W0|] eqn:HW0; [| apply nth_error_None in HW0; lia].
  apply safe_bind. eapply (spush_w s inp xs0 h st Hr c0 w0 W0); [exact Hw0 | exact HW0 |]. intros h1 Hr1 _.
  set (st1 := wset st _) in Hr1.
  assert (Hsi1 : SI st1).
  { apply si_wl_lset; [exact Hsi |]. apply Forall_app. split; [eapply wl_ok; eauto | auto]. }
  apply safe_bind. eapply (sget_hw s inp xs0 h1 st1 Hr1); [unfold st1; fvs; rewrite lset_length; lia |]. intros w1 Hw1.
  destruct (nth_error (wl st1) c1) as [W1|] eqn:HW1; [| apply nth_error_None in HW1; unfold st1 in HW1; fvs; rewrite lset_length in HW1; lia].
  eapply (spush_w s inp xs0 h1 st1 Hr1 c1 w1 W1); [exact Hw1 | exact HW1 |]. intros h2 Hr2 _.
  eapply HQ; [exact Hr2 | | reflexivity | reflexivity].
  apply si_wl_lset; [exact Hsi1 |]. apply Forall_app. split; [eapply wl_ok; [exact (proj1 Hsi1) | exact HW1] | auto].
Qed.

Lemma learn_safe fuel h st confl Q :
  R h st -> SI st -> confl < length (db st) -> 1 <= length (lim st) ->
  (forall h' st', R h' st' -> SI st' -> Q tt h') ->
  safe (learn s fuel confl) Q h.
Proof.
  intros Hr Hsi Hcf Hdl HQ. pose proof (proj1 Hsi) as Hs. unfold learn, decision_level.
  apply safe_bind. eapply (slen_f s inp xs0 h st Hr FLim). cbv beta.
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FMisc); [rewrite (si_misc _ _ Hs); unfold CONFLICTS; lia |].
  intros now _.
  apply safe_bind. eapply (smake_scr s inp xs0 h st Hr 1 0). intros learnt h1 Hn Hp Hr1 _.
  apply safe_bind. eapply (slen_f s inp xs0 h1 st Hr1 FTr). cbv beta.
  assert (Htr : 1 <= length (tr st)).
  { destruct (lim st) as [|x l] eqn:El; [cbn in Hdl; lia |]. pose proof (proj2 Hsi) as Hl.
    unfold lim_lt in Hl. rewrite El in Hl. inversion Hl. lia. }
  apply safe_bind. eapply analyze_loop_safe; [exact Hr1 | exact Hsi | exact Hcf | lia | exact Hn | exact Hp
    | cbn; lia | cbn; constructor |].
  intros p h2 st2 Lr2 Hr2 Hsi2 S2 Hp2 H12 Hlr2 Hlp. cbv zeta.
  pose proof S2 as (E1 & E2 & E3 & E4 & E5 & E6).
  assert (Hn2 : ~ In (vloc learnt) (locs s inp st2)) by (rewrite (locs_same st st2 E1 E2); exact Hn).
  assert (Hlu : lit_ok (lneg p)) by (now apply lneg_lt).
  apply safe_bind. eapply (sset_scr s inp xs0 h2 st2 Hr2 learnt Lr2 0); [exact Hn2 | exact Hp2 | lia |].
  intros h3 Hr3 Hp3.
  assert (Hlr3 : Forall lit_ok (lset Lr2 0 (lneg p))).
  { destruct Lr2 as [|a t]; [cbn in H12; lia |]. rewrite lset_cons0. constructor; [exact Hlu | exact Hlr2]. }
  apply safe_bind. eapply (slen_pts h3 learnt _ _ Hp3).
  apply safe_bind. eapply finish_learnt_safe; [exact Hr3 | exact Hsi2 | exact Hn2 | exact Hp3 | exact Hlr3
    | rewrite lset_length; lia | left; reflexivity |].
  intros bt h4 st4 Lr4 Hr4 Hsi4 S4 Hp4 Hlr4 HL4.
  pose proof S4 as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (Hn4 : ~ In (vloc learnt) (locs s inp st4)) by (rewrite (locs_same st2 st4 F1 F2); exact Hn2).
  apply safe_bind. eapply backtrack_safe; [exact Hr4 | exact Hsi4 |]. intros h5 st5 Hr5 Hsi5 G1 G2 G3 Hk5.
  assert (Hp5 : pts h5 learnt Lr4) by exact (Hk5 _ _ Hn4 Hp4).
  assert (Hn5 : ~ In (vloc learnt) (locs s inp st5)) by (rewrite (locs_same st4 st5 G1 G2); exact Hn4).
  rewrite lset_length in HL4.
  destruct (Nat.eqb_spec (length (lset Lr2 0 (lneg p))) 1) as [_ | Hne].
  { eapply enqueue_safe; [exact Hr5 | exact (proj1 Hsi5) | exact Hlu |]. intros h6 Hr6 _.
    eapply HQ; [exact Hr6 |]. apply enq_si; [exact Hsi5 | exact Hlu | lia]. }
  rewrite lset_length in Hne.
  apply safe_bind. eapply (slen_hc s inp xs0 h5 st5 Hr5).
  apply safe_bind. eapply (spush_cls s inp xs0 h5 st5 Hr5 learnt Lr4); [exact Hn5 | exact Hp5 |]. intros h6 Hr6.
  assert (Hsi6 : SI (cpush st5 learnt Lr4)) by (split; [apply sic_cpush; [exact (proj1 Hsi5) | exact Hlr4] | exact (proj2 Hsi5)]).
  apply safe_bind. eapply (attach_safe h6 (cpush st5 learnt Lr4) (length (db st5)) learnt Lr4); [exact Hr6 | exact Hsi6 | | | lia |].
  - fvs. rewrite nth_error_app2, (repr_len_db _ _ _ _ _ Hr5), Nat.sub_diag by (rewrite (repr_len_db _ _ _ _ _ Hr5); lia).
    reflexivity.
  - fvs. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  - intros h7 st7 Hr7 Hsi7 H1 H2.
    eapply enqueue_safe; [exact Hr7 | exact (proj1 Hsi7) | exact Hlu |]. intros h8 Hr8 _.
    eapply HQ; [exact Hr8 |]. apply enq_si; [exact Hsi7 | exact Hlu |]. rewrite H2. fvs. rewrite length_app. cbn. lia.
Qed.

(** ** Search *)

Lemma pick_safe fuel : forall h st v n best bs Q,
  R h st -> SIc st -> n <= nv -> best <= n -> (forall r, r <= n -> Q r h) ->
  safe (pick s fuel v n best bs) Q h.
Proof.
  induction fuel as [|f IH]; intros h st v n best bs Q Hr Hs Hn Hb HQ; cbn [pick].
  { apply safe_vabort. }
  destruct (Nat.leb_spec n v).
  { apply safe_ret, HQ, Hb. }
  apply safe_bind. eapply (sget_f s inp xs0 h st Hr FAsg); [rewrite (si_asg _ _ Hs); lia |]. intros a _.
  destruct (Nat.eqb a 0).
  - apply safe_bind. eapply (sget_f s inp xs0 h st Hr FSt); [rewrite (si_st _ _ Hs); lia |]. intros st' _.
    destruct (Nat.eqb best 0 || Nat.ltb bs st'); eapply IH; eauto; lia.
  - eapply IH; eauto.
Qed.

Lemma search_safe fuel budget : forall h st Q,
  R h st -> SI st -> (forall r h' st', R h' st' -> SI st' -> r <= 2 -> Q r h') -> safe (search s fuel budget nv) Q h.
Proof.
  induction budget as [|b IH]; intros h st Q Hr Hsi HQ; cbn [search].
  { apply safe_ret. eapply HQ; eauto. }
  apply safe_bind. eapply propagate_safe; [exact Hr | exact Hsi |]. intros confl h1 st1 Hr1 Hsi1 Hc.
  pose proof (proj1 Hsi1) as Hs1.
  destruct (Nat.eqb_spec confl 0) as [_ | Hne].
  - apply safe_bind. eapply pick_safe; [exact Hr1 | exact Hs1 | lia | lia |]. intros v1 Hv1.
    destruct (Nat.eqb_spec v1 0); [apply safe_ret; eapply HQ; eauto |]. cbv zeta.
    apply safe_bind. eapply (sget_f s inp xs0 h1 st1 Hr1 FPh); [rewrite (si_ph _ _ Hs1); lia |]. intros ph _.
    apply safe_bind. eapply (slen_f s inp xs0 h1 st1 Hr1 FTr). cbv beta.
    apply safe_bind. eapply (spush_f s inp xs0 h1 st1 Hr1 FLim). intros h2 Hr2 _.
    set (st2 := fset st1 FLim _) in Hr2.
    assert (Hs2 : SIc st2) by (apply sic_lim; [exact Hs1 | apply incr_snoc; [apply (si_inc _ _ Hs1) | exact (proj2 Hsi1)]]).
    assert (Hl : lit_ok (lit_of (v1 - 1) ph)) by (apply lit_of_lt; lia).
    apply safe_bind. eapply enqueue_safe; [exact Hr2 | exact Hs2 | exact Hl |]. intros h3 Hr3 _.
    eapply IH; [exact Hr3 | | exact HQ]. split; [apply enq_sic; [exact Hs2 | exact Hl | lia] |].
    unfold lim_lt, st2. fvs. rewrite length_app. cbn [length].
    apply Forall_app. split; [| constructor; [lia | constructor]].
    eapply Forall_impl; [| exact (proj2 Hsi1)]. intros x Hx. cbv beta in Hx. lia.
  - apply safe_bind. eapply (slen_f s inp xs0 h1 st1 Hr1 FLim). cbv beta.
    destruct (Nat.eqb_spec (length (lim st1)) 0); [apply safe_ret; eapply HQ; eauto |].
    apply safe_bind. eapply (sget_f s inp xs0 h1 st1 Hr1 FMisc); [rewrite (si_misc _ _ Hs1); unfold CONFLICTS; lia |].
    intros k _.
    apply safe_bind. eapply (sset_f s inp xs0 h1 st1 Hr1 FMisc); [rewrite (si_misc _ _ Hs1); unfold CONFLICTS; lia |].
    intros h2 Hr2 _. set (st2 := fset st1 FMisc _) in Hr2.
    assert (Hsi2 : SI st2) by (split; [apply sic_lset; [exact Hs1 | auto 7] | exact (proj2 Hsi1)]).
    apply safe_bind. eapply learn_safe; [exact Hr2 | exact Hsi2 | unfold st2; fvs; lia | unfold st2; fvs; lia |].
    intros h3 st3 Hr3 Hsi3. pose proof (si_misc _ _ (proj1 Hsi3)) as Hm3.
    apply safe_bind. eapply (sget_f s inp xs0 h3 st3 Hr3 FMisc); [unfold RCOUNT; lia |]. intros rc _.
    apply safe_bind. eapply (sget_f s inp xs0 h3 st3 Hr3 FMisc); [unfold RLIMIT; lia |]. intros rl _.
    apply safe_seq with (P := fun _ h' => exists st', R h' st' /\ SI st').
    + destruct (Nat.leb rl (rc + 1)).
      * apply safe_bind. eapply (sset_f s inp xs0 h3 st3 Hr3 FMisc); [unfold RCOUNT; lia |]. intros h4 Hr4 _.
        set (st4 := fset st3 FMisc _) in Hr4.
        assert (Hsi4 : SI st4) by (split; [apply sic_lset; [exact (proj1 Hsi3) | auto 7] | exact (proj2 Hsi3)]).
        apply safe_bind. eapply (sset_f s inp xs0 h4 st4 Hr4 FMisc); [rewrite (si_misc _ _ (proj1 Hsi4)); unfold RLIMIT; lia |].
        intros h5 Hr5 _. set (st5 := fset st4 FMisc _) in Hr5.
        assert (Hsi5 : SI st5) by (split; [apply sic_lset; [exact (proj1 Hsi4) | auto 7] | exact (proj2 Hsi4)]).
        eapply backtrack_safe; [exact Hr5 | exact Hsi5 |]. intros h6 st6 Hr6 Hsi6 _ _ _ _. eauto.
      * eapply (sset_f s inp xs0 h3 st3 Hr3 FMisc); [unfold RCOUNT; lia |]. intros h4 Hr4 _.
        eexists. split; [exact Hr4 |]. split; [apply sic_lset; [exact (proj1 Hsi3) | auto 7] | exact (proj2 Hsi3)].
    + intros [] h4 (st4 & Hr4 & Hsi4). eapply IH; eauto.
Qed.

(** ** Loading and checking the input *)

(** The [len] positions of [xs0] from [pos] hold literals. *)
Definition lits_at (pos len : nat) : Prop :=
  forall j, j < len -> exists l, nth_error xs0 (pos + j) = Some l /\ lit_ok l.

Lemma lits_at_tail pos len : lits_at pos (S len) -> lits_at (pos + 1) len.
Proof.
  intros H j Hj. destruct (H (S j)) as (l & Hl & Hok); [lia |].
  exists l. split; [| exact Hok]. rewrite <- Hl. f_equal. lia.
Qed.

Lemma encodes_lits n pos c F :
  encodes xs0 n pos (c :: F) -> lits_below (2 * nv) (c :: F) -> lits_at (pos + 1) (length c).
Proof.
  intros HF HB j Hj. inversion HF as [| ? ? ? Hlt Hlen Hc HF']; subst.
  rewrite Hc by exact Hj. destruct (nth_error c j) as [l|] eqn:E; [| apply nth_error_None in E; lia].
  exists l. split; [reflexivity |]. inversion HB as [| ? ? Hc0 _]; subst.
  exact (Forall_nth_error _ _ _ _ Hc0 E).
Qed.

Lemma clause_sat_safe fuel : forall h st pos len Q,
  R h st -> SIc st -> lits_at pos len -> (forall b, Q b h) -> safe (clause_sat s fuel inp pos len) Q h.
Proof.
  induction fuel as [|f IH]; intros h st pos len Q Hr Hs Hl HQ; cbn [clause_sat].
  { apply safe_vabort. }
  destruct len as [|len]; [apply safe_ret, HQ |].
  destruct (Hl 0) as (l & Hl0 & Hok); [lia |]. rewrite Nat.add_0_r in Hl0.
  apply safe_bind. eapply (sget_inp s inp xs0 h st Hr); [eapply nth_error_lt'; eauto |]. intros x Hx.
  rewrite Hl0 in Hx. injection Hx as <-.
  apply safe_bind. eapply lit_value_safe; [exact Hr | exact Hs | exact Hok |]. intros v.
  destruct (Nat.eqb v 1); [apply safe_ret, HQ |]. eapply IH; eauto. now apply lits_at_tail.
Qed.

Lemma check_model_safe fuel : forall h st n pos F Q,
  R h st -> SIc st -> encodes xs0 n pos F -> lits_below (2 * nv) F -> (forall b, Q b h) ->
  safe (check_model s fuel inp pos n) Q h.
Proof.
  induction fuel as [|f IH]; intros h st n pos F Q Hr Hs HF HB HQ; cbn [check_model].
  { apply safe_vabort. }
  destruct (Nat.leb_spec n pos); [apply safe_ret, HQ |].
  inversion HF as [? Hle | ? c F' Hlt Hlen Hc HF']; subst; [lia |].
  apply safe_bind. eapply (sget_inp s inp xs0 h st Hr); [eapply nth_error_lt'; eauto |]. intros len Hx.
  rewrite Hlen in Hx. injection Hx as <-.
  apply safe_bind. eapply clause_sat_safe; [exact Hr | exact Hs | eapply encodes_lits; eauto |]. intros b.
  destruct b; [| apply safe_ret, HQ]. eapply IH; [exact Hr | exact Hs | exact HF' | | exact HQ].
  inversion HB; assumption.
Qed.

Lemma read_lits_safe fuel : forall h st c Lc pos len Q,
  R h st -> ~ In (vloc c) (locs s inp st) -> pts h c Lc -> lits_at pos len ->
  (forall h' ys, R h' st -> pts h' c (Lc ++ ys) -> length ys = len -> Forall lit_ok ys -> Q tt h') ->
  safe (read_lits fuel inp c pos len) Q h.
Proof.
  induction fuel as [|f IH]; intros h st c Lc pos len Q Hr Hn Hp Hl HQ; cbn [read_lits].
  { apply safe_vabort. }
  destruct len as [|len].
  { apply safe_ret. apply (HQ h []); [exact Hr | now rewrite app_nil_r | reflexivity | constructor]. }
  destruct (Hl 0) as (l & Hl0 & Hok); [lia |]. rewrite Nat.add_0_r in Hl0.
  apply safe_bind. eapply (sget_inp s inp xs0 h st Hr); [eapply nth_error_lt'; eauto |]. intros x Hx.
  rewrite Hl0 in Hx. injection Hx as <-.
  apply safe_bind. eapply (spush_scr s inp xs0 h st Hr c Lc l); [exact Hn | exact Hp |]. intros h1 Hr1 Hp1.
  eapply IH; [exact Hr1 | exact Hn | exact Hp1 | now apply lits_at_tail |].
  intros h' ys Hr' Hp' Hys Hok'. apply (HQ h' (l :: ys)); [exact Hr' | now rewrite <- app_assoc in Hp' | cbn; lia |].
  constructor; auto.
Qed.

Lemma load_safe fuel : forall n F pos h st Q,
  R h st -> SI st -> encodes xs0 n pos F -> lits_below (2 * nv) F ->
  (forall b h' st', R h' st' -> SI st' -> Q b h') ->
  safe (load s fuel inp pos n) Q h.
Proof.
  induction fuel as [|f IH]; intros n F pos h st Q Hr Hsi HF HB HQ; cbn [load].
  { apply safe_vabort. }
  destruct (Nat.leb_spec n pos); [apply safe_ret; eauto |].
  inversion HF as [? Hle | ? c F' Hlt Hlen Hc HF']; subst; [lia |].
  assert (HB' : lits_below (2 * nv) F') by (inversion HB; assumption).
  apply safe_bind. eapply (sget_inp s inp xs0 h st Hr); [eapply nth_error_lt'; eauto |]. intros len Hx.
  rewrite Hlen in Hx. injection Hx as <-.
  apply safe_bind. eapply (smake_scr s inp xs0 h st Hr 0 0). intros cv h1 Hn Hp Hr1 _.
  apply safe_bind. eapply read_lits_safe; [exact Hr1 | exact Hn | exact Hp | eapply encodes_lits; eauto |].
  intros h2 ys Hr2 Hp2 Hys Hok. cbn [repeat app] in Hp2.
  apply safe_bind. eapply (slen_hc s inp xs0 h2 st Hr2).
  apply safe_bind. eapply (spush_cls s inp xs0 h2 st Hr2 cv ys); [exact Hn | exact Hp2 |]. intros h3 Hr3.
  set (st3 := cpush st cv ys) in Hr3.
  assert (Hsi3 : SI st3) by (split; [apply sic_cpush; [exact (proj1 Hsi) | exact Hok] | exact (proj2 Hsi)]).
  assert (Hc3 : nth_error (hcls st3) (length (db st)) = Some cv).
  { unfold st3; fvs. rewrite nth_error_app2, <- (repr_len_db _ _ _ _ _ Hr2), Nat.sub_diag by (rewrite (repr_len_db _ _ _ _ _ Hr2); lia).
    reflexivity. }
  assert (Hd3 : nth_error (db st3) (length (db st)) = Some ys)
    by (unfold st3; fvs; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  destruct (Nat.eqb_spec (length c) 0); [apply safe_ret; eauto |].
  destruct (Nat.eqb_spec (length c) 1).
  - apply safe_bind. eapply (sget_cl s inp xs0 h3 st3 Hr3 _ cv ys); [exact Hc3 | exact Hd3 | lia |]. intros l Hl.
    assert (Hlo : lit_ok l) by exact (Forall_nth_error _ _ _ _ Hok Hl).
    apply safe_bind. eapply lit_value_safe; [exact Hr3 | exact (proj1 Hsi3) | exact Hlo |]. intros v.
    destruct (Nat.eqb v 2); [apply safe_ret; eauto |].
    apply safe_seq with (P := fun _ h' => exists st', R h' st' /\ SI st').
    + destruct (Nat.eqb v 0); [| apply safe_ret; eauto].
      eapply enqueue_safe; [exact Hr3 | exact (proj1 Hsi3) | exact Hlo |]. intros h4 Hr4 _.
      eexists. split; [exact Hr4 | apply enq_si; [exact Hsi3 | exact Hlo | lia]].
    + intros [] h4 (st4 & Hr4 & Hsi4). eapply IH; eauto.
  - apply safe_bind. eapply (attach_safe h3 st3 (length (db st)) cv ys); [exact Hr3 | exact Hsi3 | exact Hc3 | exact Hd3 | lia |].
    intros h4 st4 Hr4 Hsi4 _ _. eapply IH; eauto.
Qed.

End Funs.

(** * [run] is safe *)

Lemma fresh_vecs_safe fuel : forall (acc : vec (vec nat)) n h L W Q,
  Alloc h L -> h (vloc acc) = Some (existT cellof (vec nat) W) ->
  (forall h' W', Alloc h' (L ++ map vloc W') -> h' (vloc acc) = Some (existT cellof (vec nat) (W ++ W')) ->
     Forall (fun w => pts h' w []) W' -> length W' = n ->
     (forall x c, x <> vloc acc -> h x = Some c -> h' x = Some c) -> Q tt h') ->
  safe (fresh_vecs fuel acc n) Q h.
Proof.
  induction fuel as [|f IH]; intros acc n h L W Q HA Hacc HQ; cbn [fresh_vecs].
  { apply safe_vabort. }
  destruct n as [|n].
  { apply safe_ret. apply (HQ h []); [now rewrite app_nil_r | now rewrite app_nil_r | constructor | reflexivity | auto]. }
  apply safe_bind, safe_vmake. intros w Hw.
  assert (Hne : vloc acc <> vloc w) by congruence.
  apply safe_bind. eapply safe_vpush; [exact (keep_fresh _ _ _ _ _ Hw Hacc) |].
  eapply IH with (L := L ++ [vloc w]).
  - apply alloc_upd; [apply alloc_fresh; assumption |]. rewrite upd_neq by exact Hne. congruence.
  - apply upd_eq.
  - intros h' W'' HA' Hacc' HW'' Hlen Hfr. apply (HQ h' (w :: W'')).
    + now rewrite <- app_assoc in HA'.
    + now rewrite <- app_assoc in Hacc'.
    + constructor; [|exact HW'']. apply Hfr; [congruence|]. rewrite upd_neq by congruence. apply upd_eq.
    + cbn. lia.
    + intros x c Hx Hc. apply Hfr; [exact Hx|]. rewrite upd_neq by exact Hx. now apply keep_fresh.
Qed.

(** After allocating [v] in [h], carry every fact about [h] over to the new heap. *)
Ltac sbump :=
  match goal with
  | Hn : ?h (vloc ?v) = None |- safe _ _ (upd ?h (vloc ?v) ?c) =>
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

Lemma init_si W nv :
  length W = 2 * nv -> SI nv (fset (init_st W nv) FMisc (lset (repeat 0 4) RLIMIT 100)).
Proof.
  intros HW. split.
  - constructor; cbn [fv fset fld_eqb init_st db wl tr]; rewrite ?repeat_length, ?length_map, ?lset_length, ?repeat_length; auto.
    all: try solve [constructor].
    all: try solve [apply Forall_forall; intros L HL; apply in_map_iff in HL as (? & <- & _); constructor].
    all: try solve [apply Forall_forall; intros r Hr; apply repeat_spec in Hr; cbn; lia].
    all: try solve [intros i j a b _ Ha; destruct i; discriminate].
  - constructor.
Qed.

Lemma mod8_small c k : c <= 3 -> (c + 8 * k) mod 8 <= 3.
Proof. intros H. rewrite Nat.mul_comm, Nat.Div0.mod_add, Nat.mod_small; lia. Qed.

(** [run] on a well-formed input never gets stuck, and answers a code
    below 4. *)
Theorem run_safe fuel budget nvars inp ninput xs0 F h0 :
  h0 (vloc inp) = Some (existT cellof nat xs0) ->
  encodes xs0 ninput 0 F -> lits_below (2 * nvars) F ->
  safe (Solver.run fuel budget nvars inp ninput) (fun r _ => r mod 8 <= 3) h0.
Proof.
  intros Hinp HF HB.
  assert (HA : Alloc h0 [vloc inp]) by (split; [constructor; [intros [] | constructor] | intros l [<- | []]; congruence]).
  unfold Solver.run.
  apply safe_bind, safe_vmake. intros e He. sbump.
  apply safe_bind, safe_vmake. intros cs Hcs. sbump.
  apply safe_bind, safe_vmake. intros ws Hws. sbump.
  apply safe_bind. eapply fresh_vecs_safe; [eassumption | eassumption |]. cbn [app].
  intros h2 W HA2 Hws2 HW HWl Hfr.
  pose proof HA2 as [ND2 _]. inversion ND2 as [|? ? N1 ND3]; subst. inversion ND3 as [|? ? N2 ND4]; subst.
  inversion ND4 as [|? ? N3 _]; subst.
  assert (Dinp : vloc inp <> vloc ws) by (intros E; apply N1; rewrite E; cbn; tauto).
  assert (Dcs : vloc cs <> vloc ws) by (intros E; apply N3; rewrite E; cbn; tauto).
  pose proof (Hfr _ _ Dinp K2) as Kinp. pose proof (Hfr _ _ Dcs K) as Kcs.
  clear K K1 K2 P A Hfr N1 N2 N3 ND2 ND3 ND4.
  apply safe_bind, safe_vmake. intros asg Hasg. sbump.
  apply safe_bind, safe_vmake. intros lvl Hlvl. sbump.
  apply safe_bind, safe_vmake. intros rsn Hrsn. sbump.
  apply safe_bind, safe_vmake. intros ph Hph. sbump.
  apply safe_bind, safe_vmake. intros stp Hstp. sbump.
  apply safe_bind, safe_vmake. intros sn Hsn. sbump.
  apply safe_bind, safe_vmake. intros tr Htr. sbump.
  apply safe_bind, safe_vmake. intros tlim Htlim. sbump.
  apply safe_bind, safe_vmake. intros m Hm. sbump.
  set (s := mk_state cs ws asg lvl rsn ph stp sn tr tlim m).
  match goal with |- safe _ _ ?h => set (h9 := h) in * end.
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
  apply safe_bind. eapply (sset_f s inp xs0 h9 _ R9 FMisc RLIMIT 100); [cbn; unfold RLIMIT; lia |].
  intros h10 R10 _. cbv zeta. fold s.
  pose proof (init_si W nvars HWl) as SI10.
  apply safe_bind. eapply (load_safe s inp xs0 nvars fuel ninput F 0 h10); [exact R10 | exact SI10 | exact HF | exact HB |].
  intros ok h11 st11 R11 SI11. cbv beta iota.
  apply safe_seq with (P := fun code h' => code <= 3 /\ exists st', repr s inp xs0 h' st' /\ SI nvars st').
  - destruct ok; [| apply safe_ret; split; [lia | eauto]].
    apply safe_bind. eapply (search_safe s inp xs0 nvars fuel budget h11 st11); [exact R11 | exact SI11 |].
    intros r1 h12 st12 R12 SI12 Hr1.
    destruct (Nat.eqb_spec r1 1) as [-> | Hne].
    + apply safe_bind. eapply (check_model_safe s inp xs0 nvars fuel h12 st12 ninput 0 F); [exact R12 | exact (proj1 SI12) | exact HF | exact HB |].
      intros b. apply safe_ret. split; [destruct b; lia | eauto].
    + apply safe_ret. split; [lia | eauto].
  - intros code h12 (Hc & st12 & R12 & SI12).
    apply safe_bind. eapply (sget_f s inp xs0 h12 st12 R12 FMisc); [rewrite (si_misc _ _ (proj1 SI12)); unfold CONFLICTS; lia |].
    intros k _. apply safe_ret. now apply mod8_small.
Qed.
