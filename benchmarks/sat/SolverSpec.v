(** Per-function specifications of the solver, in [Sem.safe] form.

    Each function gets one specification that carries both halves of the
    proof: memory safety ([safe] rules out every failing access; [SI nv]
    gives the bounds) and the model invariant [Inv val] of [Inv.v], for an
    optional valuation [val] ([Core None] is purely structural).  The
    precondition is [repr s nv (mn, ma) st] for an abstract state [st];
    the postcondition hands the continuation the new abstract state with
    the invariants and the function's relation.  Specifications are in
    continuation form: [(forall r mn' ma' st', post -> Q r (mn', ma')) ->
    safe (f ...) Q (mn, ma)], so that [safe_bind] composes them. *)
From ITree Require Import ITree ITreeFacts.
From Crane Require Import Monads.Global Monads.GlobalFacts.
From Stdlib Require Import List PeanoNat Lia Bool Permutation.
Require Import Solver Cnf Abstract Inv Sem Repr.
Import ListNotations.
Import Solver.
Local Set Warnings "-unused-intro-pattern".

(** * Abstract states that agree on every component *)

(** [Core] survives [sim]. *)
Lemma core_sim val st st' : Core val st -> sim st st' -> Core val st'.
Proof. intros C (Ed & Ew & Ef). apply (core_ext val st st'); rewrite ?Ed, ?Ef; auto. Qed.

(** [SIc] survives [sim]. *)
Lemma sic_sim nv st st' : SIc nv st -> sim st st' -> SIc nv st'.
Proof. intros [] (Ed & Ew & Ef). constructor; rewrite ?Ed, ?Ew, ?Ef; auto. Qed.

(** [SI] survives [sim]. *)
Lemma si_sim nv st st' : SI nv st -> sim st st' -> SI nv st'.
Proof.
  intros [Hc Hl] H. split; [eapply sic_sim; eauto|]. destruct H as (_ & _ & Ef).
  unfold lim_lt in *. now rewrite !Ef.
Qed.

(** [Inv] survives [sim]. *)
Lemma inv_sim val st st' : Inv val st -> sim st st' -> Inv val st'.
Proof.
  intros (C & W & S0) H. split; [eapply core_sim; eauto|]. destruct H as (Ed & Ew & Ef).
  split; [now rewrite Ed, Ew | intros v; rewrite Ef; apply S0].
Qed.

(** [sim] is reflexive on equal components. *)
Lemma sim_refl st : sim st st.
Proof. repeat split. Qed.

(** [lia] after unfolding every local definition. *)
Ltac ulia :=
  repeat (match goal with x := _ |- _ => subst x end); cbn [wl db fv dset wset cpush fset fld_eqb] in *;
  rewrite ?lset_length, ?length_app in *; lia.

(** Prove [sim] of two explicit states by computing their components. *)
Ltac solve_sim := split; [reflexivity | split; [reflexivity | intros []; reflexivity]].

(** * Enqueueing *)

(** [enqueue l r] on the abstract state, including the trail counter. *)
Definition enqA (st : astate) (l r : nat) : astate :=
  fset (enq st l r) FMisc (lset (fv st FMisc) TLEN (length (tr st) + 1)).

(** [enqA] keeps [Core] under the conditions of [core_enq]. *)
Lemma core_enqA nv val st l r :
  Core val st -> SIc nv st -> lit_ok nv l -> lval (asg st) l = 0 ->
  (r = 0 -> Forall (fun x => length (tr st) <= x) (lim st) \/ In (length (tr st)) (lim st)) ->
  (forall ci, r = S ci -> exists c, nth_error (db st) ci = Some c /\ nth_error c 0 = Some l /\
                            Forall (fun q => lval (asg st) q = 2) (tl c)) ->
  (length (lim st) = 0 -> holds val l) ->
  Core val (enqA st l r).
Proof.
  intros C Hs Hl H0 Hr0 HrS Hh. unfold enqA.
  assert (Hv : forall f, f = FAsg \/ f = FLvl \/ f = FRsn -> lvar l < length (fv st f))
    by (intros f Hf; apply (var_ok nv st f l Hs Hl); tauto).
  pose proof (core_enq val st l r C H0 (Hv FAsg ltac:(tauto)) (Hv FLvl ltac:(tauto)) (Hv FRsn ltac:(tauto))
                Hr0 HrS Hh) as C1.
  apply core_fset_misc; [exact C1|]. unfold enq. cbn [fv fset fld_eqb].
  rewrite nth_lset_ne by (unfold QHEAD, TLEN; lia). pose proof (i_qtr _ _ C1) as Hq.
  unfold enq in Hq. cbn [fv fset fld_eqb] in Hq. lia.
Qed.

(** [enqA] keeps [SI]. *)
Lemma si_enqA nv st l r : SI nv st -> lit_ok nv l -> r <= length (db st) -> SI nv (enqA st l r).
Proof.
  intros H Hl Hr. pose proof (enq_si nv st l r H Hl Hr) as [Hc Hlt]. split; [|exact Hlt].
  unfold enqA. exact (sic_lset nv (enq st l r) FMisc TLEN (length (tr st) + 1) Hc ltac:(tauto)).
Qed.

(** [enqA] keeps the watch lists, marks and clauses. *)
Lemma enqA_wch val st l r : Inv val st -> Core val (enqA st l r) -> Inv val (enqA st l r).
Proof. intros (_ & W & S0) C. split; [exact C | split; [exact W | exact S0]]. Qed.

Section Spec.
(** The solver's handles [s], its number of variables [nv], and the
    optional valuation [val] that [Inv] is about. *)
Variables (s : state) (nv : nat) (val : option (nat -> bool)).

(** The representation relation for these handles. *)
Local Notation R := (repr s nv).

(** The value of a successful [nth_error], as [nth]. *)
Lemma nth_error_nth_eq (xs : list nat) i x : nth_error xs i = Some x -> x = nth i xs 0.
Proof. intros H. symmetry. now apply nth_error_nth. Qed.

(** A literal of a clause, read from the arena. *)
Lemma rd_cl {U} a ci cl j x i (k : nat -> itree E U) Q mn ma st :
  R mn ma st -> refp ma (arena s) a -> nth_error (db st) ci = Some cl -> nth_error cl j = Some x ->
  i = off (db st) ci + 1 + j -> safe (k x) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) a i) k) Q (mn, ma).
Proof.
  intros Hr Ha Hc Hx -> Hk. eapply rd_ar; [exact Hr | exact Ha | | exact Hk].
  rewrite enc_at_lit with (cl := cl); [exact Hx | exact Hc | apply nth_error_Some; congruence].
Qed.

(** A clause's length, read from the arena. *)
Lemma rd_clen {U} a ci cl i (k : nat -> itree E U) Q mn ma st :
  R mn ma st -> refp ma (arena s) a -> nth_error (db st) ci = Some cl -> i = off (db st) ci ->
  safe (k (length cl)) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) a i) k) Q (mn, ma).
Proof.
  intros Hr Ha Hc -> Hk. eapply rd_ar; [exact Hr | exact Ha | | exact Hk]. now apply enc_at_len.
Qed.

(** [lit_value l] answers [lval]. *)
Lemma lit_value_sp l Q mn ma st :
  R mn ma st -> SIc nv st -> lit_ok nv l -> Q (lval (asg st) l) (mn, ma) -> safe (lit_value s l) Q (mn, ma).
Proof.
  intros Hr Hs Hl HQ. unfold lit_value.
  eapply (rd_fld s nv FAsg (lvar l) (nth (lvar l) (asg st) 0) _ Q mn ma st Hr ltac:(discriminate)).
  - apply nth_error_nth'. apply (var_ok nv st FAsg l Hs Hl). tauto.
  - apply safe_ret. exact HQ.
Qed.

(** [enqueue l x], [x] naming the reason [r], performs [enqA]. *)
Lemma enqueue_sp l r x Q mn ma st :
  R mn ma st -> SIc nv st -> Core val st -> lit_ok nv l -> lval (asg st) l = 0 -> x = tr_rsn (db st) r ->
  (forall mn', R mn' ma (enqA st l r) -> Q tt (mn', ma)) -> safe (enqueue s l x) Q (mn, ma).
Proof.
  intros Hr Hs C Hl H0 -> HQ. unfold enqueue, decision_level, get, put. cbv zeta.
  assert (Hv : forall f, f = FAsg \/ f = FLvl \/ f = FRsn -> lvar l < length (fv st f))
    by (intros f Hf; apply (var_ok nv st f l Hs Hl); tauto).
  destruct (repr_counts _ _ _ _ _ Hr) as (Etl & Etll & _).
  eapply (wr_plain s nv FAsg); [exact Hr | unfold plain; tauto | discriminate | apply Hv; tauto |].
  intros mn1 R1. eapply (rd_misc s nv TLLEN); [exact R1 | unfold TLLEN, NMISC; lia |].
  cbn [fv fset fld_eqb]. rewrite Etll.
  eapply (wr_plain s nv FLvl); [exact R1 | unfold plain; tauto | discriminate | cbn; apply Hv; tauto |].
  intros mn2 R2. eapply (wr_rsn s nv (lvar l) r); [exact R2 | cbn; apply Hv; tauto | reflexivity |].
  intros mn3 R3. eapply (rd_misc s nv TLEN); [exact R3 | unfold TLEN, NMISC; lia |].
  cbn [fv fset fld_eqb]. rewrite Etl.
  eapply (wr_push_end s nv FTr l Q mn3 ma _ R3); [unfold seqf; tauto | cbn [capf fv fset fld_eqb] |].
  - exact (tr_room nv val st l C Hs (proj1 (lit_ok_var nv l) Hl) H0).
  - intros mn' R'. apply HQ. eapply repr_sim; [exact R'|]. solve_sim.
Qed.

(** * Watch lists *)

(** [watch l x] appends clause [ci] (at offset [x]) to [l]'s watch list,
    moving the list to larger storage when it is full.  The arena and the
    other literals' storage handles stay. *)
Lemma watch_sp l ci x Q mn ma st :
  R mn ma st -> l < 2 * nv -> x = off (db st) ci ->
  (forall mn' ma', R mn' ma' (wset st (lset (wl st) l (nth l (wl st) [] ++ [ci]))) ->
     (forall a, refp ma (arena s) a -> refp ma' (arena s) a) ->
     (forall l' w, l' <> l -> wd s ma l' w -> wd s ma' l' w) -> Q tt (mn', ma')) ->
  safe (watch s l x) Q (mn, ma).
Proof.
  intros (a & ws & cs & C & A) Hl -> HQ. unfold watch.
  pose proof (a_len _ _ _ A) as E0. pose proof (a_wln _ _ _ A) as E3. pose proof (a_wcn _ _ _ A) as E4.
  set (L := nth l (wl st) []) in *. set (S := cws cs l) in *.
  pose proof (a_ws _ _ _ A l Hl) as Hpre. fold L S in Hpre.
  pose proof (pre_length _ _ Hpre) as HLS. rewrite length_map in HLS.
  eapply safe_read_n_bind;
    [exact (conc_arr _ _ _ _ _ _ _ 10 _ C eq_refl) | apply nth_error_nth'; lia |].
  rewrite (a_wl _ _ _ A l Hl). fold L.
  eapply safe_read_n_bind;
    [exact (conc_arr _ _ _ _ _ _ _ 11 _ C eq_refl) | apply nth_error_nth'; lia |].
  rewrite (a_wc _ _ _ A l Hl). fold S.
  pose proof (c_wd _ _ _ _ _ _ _ C) as Hwd. pose proof (c_wdn _ _ _ _ _ _ _ C) as Hwdn.
  destruct (nth_error ws l) as [w|] eqn:Ew; [|apply nth_error_None in Ew; lia].
  eapply safe_read_a_bind; [exact Hwd | exact Ew |].
  pose proof (conc_arr _ _ _ _ _ _ _ (13 + l) _ C Ew) as Hw. fold S in Hw.
  (* the final length update, from any state whose storage holds the new entry *)
  assert (Fin : forall mn1 ma1 ws1 cs1,
            conc s nv mn1 ma1 a ws1 cs1 -> abs nv st cs1 -> l < length ws1 ->
            nth_error (cws cs1 l) (length L) = Some (off (db st) ci) ->
            (forall a', refp ma (arena s) a' -> refp ma1 (arena s) a') ->
            (forall l' w', l' <> l -> wd s ma l' w' -> wd s ma1 l' w') ->
            safe (Global.write_array (E := E) (V := Vn) (idx := 0) (wlen s) l (length L + 1)) Q (mn1, ma1)).
  { intros mn1 ma1 ws1 cs1 C1 A1 Hl1 Hn Hr1 Hd1.
    assert (Hl' : l < length (cwl cs1)) by (rewrite (a_wln _ _ _ A1); exact Hl).
    eapply safe_write_n; [exact (conc_arr _ _ _ _ _ _ _ 10 _ C1 eq_refl) | exact Hl' |].
    apply HQ; [| exact Hr1 | exact Hd1]. eapply repr_of.
    - apply (conc_awrite s nv mn1 ma1 a ws1 cs1 10 _ l _ C1); [reflexivity | exact Hl'].
    - exact (abs_wpush _ _ _ l ci A1 Hl Hn). }
  apply safe_bind. destruct (Nat.ltb_spec (length L) (length S)) as [Hlt | Hge]; cbv beta iota.
  - (* room: store the entry past the end *)
    eapply safe_write_n; [exact Hw | exact Hlt |].
    apply (Fin _ _ ws (lset cs (13 + l) (lset S (length L) (off (db st) ci)))); [| | lia | | auto | auto].
    + apply (conc_awrite s nv mn ma a ws cs (13 + l) w _ _ C); [exact Ew | exact Hlt].
    + apply abs_wpad; [exact A | exact Hl | unfold L; lia].
    + rewrite nth_lset_eq by lia. apply nth_error_lset_eq. exact Hlt.
  - (* full: move to storage twice as large *)
    cbv zeta. set (cap' := 2 * length S + 4).
    eapply safe_new_n_bind. set (w' := afresh mn cap'). set (mn1 := anew mn cap' 0).
    pose proof (conc_fresh _ _ _ _ _ _ _ cap' C) as Ho. fold w' in Ho.
    pose proof (conc_anew _ _ _ _ _ _ _ cap' 0 C) as C1. fold mn1 in C1.
    pose proof (arr_anew (V := Solver.Vn) mn cap' 0) as Hw'. fold w' mn1 in Hw'.
    pose proof (arr_anew_old (V := Solver.Vn) mn cap' 0 _ _ Hw) as Hw1. fold mn1 in Hw1.
    assert (Hdisj : forall y, In y (cells w') -> ~ In y (cells w)).
    { intros y Hy Hy'. apply (Ho y Hy). eapply in_cells_own; [apply (nth_error_In _ (13 + l)); exact Ew | exact Hy']. }
    apply safe_bind. apply (copy_safe w w' (length L) 0 S (repeat 0 cap') _ mn1 ma Hw1 Hw' Hdisj);
      [lia | rewrite repeat_length; unfold cap'; lia | reflexivity |].
    intros mn2 Hfr Hw2. cbn [Nat.add] in Hw2.
    assert (C2 : conc s nv mn2 ma a ws cs).
    { apply (conc_frame _ _ _ _ _ _ _ _ C1). intros b ys Hb Hy. apply Hfr; [exact Hy|].
      intros y Hy1 Hy2. apply (Ho y Hy1). eapply in_cells_own; [exact Hb | exact Hy2]. }
    set (ys := firstn (length L) S ++ skipn (length L) (repeat 0 cap')) in *.
    assert (Hys : length ys = cap').
    { unfold ys. rewrite length_app, length_firstn, length_skipn, repeat_length. unfold cap'. lia. }
    assert (Hlw : length L < asize w') by (change (asize w') with cap'; unfold cap'; lia).
    eapply safe_write_n_bind; [exact Hw2 | lia |].
    pose proof (conc_scratch _ _ _ _ _ _ _ w' (length L) (off (db st) ci) C2 Ho Hlw) as C3.
    pose proof (arr_awrite_same (V := Solver.Vn) _ _ (length L) (off (db st) ci) _ Hw2 ltac:(lia)) as Hw3.
    set (mn3 := awrite mn2 w' (length L) (off (db st) ci)) in *.
    set (ys' := lset ys (length L) (off (db st) ci)) in *.
    eapply safe_write_a_bind; [exact Hwd | lia |].
    pose proof (conc_wdata _ _ _ _ _ _ _ l w' ys' C3 Hl Hw3 Ho) as C4.
    set (ma4 := awrite ma (wdata s) l w') in *.
    set (cs4 := lset cs (13 + l) ys') in *.
    assert (Hl11 : l < length (cwc cs4)) by (unfold cs4; rewrite nth_lset_ne by lia; lia).
    eapply safe_write_n; [exact (conc_arr _ _ _ _ _ _ _ 11 _ C4 eq_refl) | exact Hl11 |].
    assert (Hpre' : pre (map (off (db st)) L) ys').
    { unfold ys', ys. destruct Hpre as [pad Hp]. rewrite Hp, firstn_app, length_map, Nat.sub_diag, firstn_O,
        app_nil_r, <- length_map with (f := off (db st)), firstn_all. apply pre_lset_out; [|lia].
      exists (skipn (length (map (off (db st)) L)) (repeat 0 cap')). reflexivity. }
    apply (Fin _ _ (lset ws l w') (lset cs4 11 (lset (cwc cs4) l cap'))).
    + apply (conc_awrite s nv mn3 ma4 a (lset ws l w') cs4 11 _ l _ C4); [reflexivity | exact Hl11].
    + unfold cs4. rewrite nth_lset_ne by lia. unfold cs4 in Hl11. rewrite nth_lset_ne in Hl11 by lia.
      replace cap' with (length ys') by (unfold ys'; rewrite lset_length; exact Hys).
      now apply abs_wmove.
    + rewrite lset_length. lia.
    + rewrite nth_lset_ne by lia. unfold cs4. rewrite nth_lset_eq by lia. unfold ys'.
      apply nth_error_lset_eq. lia.
    + intros a' Ha'. apply (refp_awrite (V := Solver.Va)); [exact Ha'|]. intros E.
      apply (c_vsep _ _ _ _ _ _ _ C). rewrite E. apply cell_in. rewrite <- (arr_length _ _ _ Hwd). lia.
    + intros l' w0 Hne (W & HW & Hl'). exists (lset ws l w'). split.
      * apply (arr_awrite_same (V := Solver.Va)); [exact Hwd | lia].
      * rewrite nth_error_lset_neq by auto. rewrite <- (arr_inj _ _ _ _ HW Hwd). exact Hl'.
Qed.


(** Replacing a clause by one of the same length keeps every offset. *)
Lemma off_dset D ci cl cl' k :
  nth_error D ci = Some cl -> length cl' = length cl -> off (lset D ci cl') k = off D k.
Proof. intros Hc E. apply off_ext. eapply map_length_lset; eauto. Qed.

(** [attach a x] watches the first two literals of clause [ci] (at offset
    [x]), which no watch list held yet. *)
Lemma attach_sp a ci cl x Q mn ma st :
  R mn ma st -> SIc nv st -> refp ma (arena s) a -> nth_error (db st) ci = Some cl -> 2 <= length cl ->
  x = off (db st) ci -> Wch (db st) (wl st) -> (forall l, l < length (wl st) -> cnt (wl st) l ci = 0) ->
  (forall mn' ma' st', R mn' ma' st' -> SIc nv st' -> db st' = db st -> (forall f, fv st' f = fv st f) ->
     Wch (db st') (wl st') -> refp ma' (arena s) a -> Q tt (mn', ma')) ->
  safe (attach s a x) Q (mn, ma).
Proof.
  intros Hr Hs Ha Hc Hlen -> W W0 HQ. unfold attach.
  destruct cl as [|c0 [|c1 cl']]; cbn [length] in Hlen; try lia.
  eapply (rd_cl a ci _ 0 c0); [exact Hr | exact Ha | exact Hc | reflexivity | lia |].
  eapply (rd_cl a ci _ 1 c1); [exact Hr | exact Ha | exact Hc | reflexivity | lia |].
  pose proof (si_wl _ _ Hs) as Hwl.
  assert (H0 : c0 < 2 * nv) by exact (db_lit nv st ci _ 0 c0 Hs Hc eq_refl).
  assert (H1 : c1 < 2 * nv) by exact (db_lit nv st ci _ 1 c1 Hs Hc eq_refl).
  assert (Hw : wok (db st) ci) by (exists (c0 :: c1 :: cl'); split; [exact Hc | cbn; lia]).
  assert (He : forall l, expect (db st) ci l = expect_cl (c0 :: c1 :: cl') l) by (intros; now apply expect_nth).
  apply safe_bind. eapply (watch_sp c0 ci); [exact Hr | exact H0 | reflexivity |].
  intros mn1 ma1 R1 Ha1 _. cbv beta.
  eapply (watch_sp c1 ci); [exact R1 | exact H1 | reflexivity |].
  intros mn2 ma2 R2 Ha2 _. eapply HQ; [exact R2 | | reflexivity | intros; reflexivity | | auto].
  - assert (S1 : SIc nv (wset st (lset (wl st) c0 (nth c0 (wl st) [] ++ [ci])))).
    { apply sic_wl_lset; [exact Hs|]. apply Forall_app. split; [|auto].
      apply (wl_ok nv st c0); [exact Hs | apply nth_error_nth'; lia]. }
    apply (sic_wl_lset nv _ c1 _ S1). apply Forall_app. split; [|auto].
    apply (wl_ok nv _ c1 _ S1). apply nth_error_nth'. cbn [wl wset]. rewrite lset_length. lia.
  - cbn [wl wset db].
    assert (W1 : Wch (db st) (lset (wl st) c0 (nth c0 (wl st) [] ++ [ci]))).
    { apply wch_push; [exact W | apply nth_error_nth'; lia |]. rewrite W0, He by lia. unfold expect_cl.
      cbn [length nth]. destruct (Nat.leb_spec 2 (S (S (length cl')))); [|lia]. rewrite Nat.eqb_refl. lia. }
    apply wch_push; [exact W1 | apply nth_error_nth'; rewrite lset_length; lia |]. rewrite He. unfold expect_cl.
    cbn [length nth]. destruct (Nat.leb_spec 2 (S (S (length cl')))); [|lia].
    rewrite cnt_lset by lia. rewrite ?Nat.eqb_refl.
    destruct (Nat.eqb_spec c0 c1) as [<- | E].
    + rewrite ?Nat.eqb_refl. rewrite count_occ_app. cbn [count_occ].
      pose proof (W0 c0 ltac:(lia)) as X. unfold cnt in X. rewrite X.
      destruct (Nat.eq_dec ci ci); [lia | congruence].
    + rewrite (W0 c1) by lia. lia.
Qed.

(** [find_watch a x k m] looks at the last [m] literals of clause [ci] (at
    offset [x]) from position [k]: 0 when all are false, else one plus the
    position of the first that is not. *)
Lemma find_watch_sp a ci cl x : forall m k Q mn ma st,
  R mn ma st -> SIc nv st -> refp ma (arena s) a -> nth_error (db st) ci = Some cl -> x = off (db st) ci ->
  k + m = length cl ->
  (forall r, (r = 0 -> forall j, k <= j < length cl -> lval (asg st) (nth j cl 0) = 2) ->
             (r <> 0 -> k <= r - 1 < length cl /\ lval (asg st) (nth (r - 1) cl 0) <> 2) -> Q r (mn, ma)) ->
  safe (find_watch s a x k m) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros k Q mn ma st Hr Hs Ha Hc -> Hkm HQ; cbn [find_watch].
  - apply safe_ret, HQ; intros; lia.
  - assert (Hk : nth_error cl k = Some (nth k cl 0)) by (apply nth_error_nth'; lia).
    eapply (rd_cl a ci cl k); [exact Hr | exact Ha | exact Hc | exact Hk | reflexivity |].
    apply safe_bind. eapply lit_value_sp; [exact Hr | exact Hs | exact (db_lit nv st ci cl k _ Hs Hc Hk) |].
    destruct (Nat.eqb_spec (lval (asg st) (nth k cl 0)) 2) as [E | E].
    + eapply IH; [exact Hr | exact Hs | exact Ha | exact Hc | reflexivity | lia |]. intros r H0 H1. apply HQ.
      * intros -> j Hj. destruct (Nat.eq_dec j k) as [-> | Hne]; [exact E|]. apply H0; auto; lia.
      * intros Hr0. specialize (H1 Hr0). lia.
    + apply safe_ret, HQ; [lia|]. intros _. replace (k + 1 - 1) with k by lia. split; [lia | exact E].
Qed.

(** [copy_rest fl w i j m] slides the last [m] entries of [fl]'s watch list
    from [i] down to [j] and cuts the list there: it becomes
    [firstn j L ++ skipn i L]. *)
Lemma copy_rest_sp fl w : forall m i j Q mn ma st,
  R mn ma st -> wd s ma fl w -> fl < 2 * nv -> i + m = length (nth fl (wl st) []) -> j <= i ->
  (forall mn', R mn' ma (wset st (lset (wl st) fl (firstn j (nth fl (wl st) []) ++ skipn i (nth fl (wl st) []))))
     -> Q tt (mn', ma)) ->
  safe (copy_rest s fl w i j m) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros i j Q mn ma st Hr Hw Hfl Him Hji HQ; cbn [copy_rest].
  - apply safe_unbind. eapply (wr_wlen s nv fl j); [exact Hr | exact Hfl | lia |].
    intros mn' R'. apply safe_ret, HQ. now rewrite (skipn_all2 (nth fl (wl st) [])), app_nil_r by lia.
  - set (L := nth fl (wl st) []) in *.
    assert (Hi : nth_error L i = Some (nth i L 0)) by (apply nth_error_nth'; lia).
    eapply (rd_ws s nv fl w i); [exact Hr | exact Hw | exact Hi |].
    eapply (wr_ws s nv fl w j (nth i L 0)); [exact Hr | exact Hw | unfold L in *; lia | reflexivity |].
    intros mn1 R1. destruct (repr_counts _ _ _ _ _ Hr) as (_ & _ & _ & _ & _ & Hwl).
    eapply IH; [exact R1 | exact Hw | exact Hfl | | lia |].
    + cbn [wl wset]. rewrite nth_lset_eq by lia. rewrite lset_length. fold L. lia.
    + intros mn' R'. apply HQ. cbn [wl wset] in R'. rewrite nth_lset_eq, lset_lset in R' by lia.
      fold L in R'. rewrite !Nat.add_1_r, keep_step in R' by (auto; lia). exact R'.
Qed.

(** The answer of [prop_watch] and [propagate]: none (0), or a conflict
    clause [ci], as its offset plus one. *)
Definition confl_ok (st : astate) (r : nat) : Prop :=
  r = 0 \/ exists ci, r = S (off (db st) ci) /\ conflict st (S ci).

(** Visiting the watch list of the false literal [fl] (storage [w]) from
    entry [i], keeping entries up to [j]: [Inv] and [SI] hold at the end,
    with no conflict or a [conflict].  Throughout, the logical list
    [firstn j L ++ skipn i L] satisfies [Wch]. *)
Lemma prop_watch_sp a fl w : forall m i j Q mn ma st,
  R mn ma st -> SI nv st -> refp ma (arena s) a -> wd s ma fl w -> lit_ok nv fl ->
  i + m = length (nth fl (wl st) []) -> j <= i ->
  Core val st -> Wch (db st) (lset (wl st) fl (firstn j (nth fl (wl st) []) ++ skipn i (nth fl (wl st) []))) ->
  Seen0 st -> lval (asg st) fl = 2 -> cur_lit st fl ->
  (forall r mn' ma' st', R mn' ma' st' -> SI nv st' -> Inv val st' -> refp ma' (arena s) a ->
     confl_ok st' r -> Q r (mn', ma')) ->
  safe (prop_watch s a fl w i j m) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros i j Q mn ma st Hr HS Ha Hw Hfl Him Hji C W S0 Hff Hcur HQ;
    cbn [prop_watch]; set (L := nth fl (wl st) []) in *;
    destruct (repr_counts _ _ _ _ _ Hr) as (_ & _ & _ & _ & _ & Hwll);
    assert (Hflw : fl < length (wl st)) by (unfold lit_ok in Hfl; ulia).
  { (* the end of the list *)
    eapply (wr_wlen s nv fl j); [exact Hr | exact Hfl | unfold L; ulia |].
    intros mn' R'. apply safe_ret. apply (HQ 0 mn' ma _ R'); [| | exact Ha | now left].
    - apply si_wl_lset; [exact HS|]. apply Forall_firstn'. apply (wl_ok nv st fl); [apply HS|].
      apply nth_error_nth'. ulia.
    - fold L. rewrite (skipn_all2 L), app_nil_r in W by ulia.
      split; [now apply core_wset | split; [exact W | exact S0]]. }
  assert (HiL : nth_error L i = Some (nth i L 0)) by (apply nth_error_nth'; ulia).
  set (ci := nth i L 0) in *.
  eapply (rd_ws s nv fl w i ci); [exact Hr | exact Hw | exact HiL |].
  assert (Hci_in : In ci (nth fl (lset (wl st) fl (firstn j L ++ skipn i L)) [])).
  { rewrite nth_lset_eq by ulia. apply in_or_app. right. rewrite (skipn_nth_error L i ci HiL). now left. }
  destruct (wch_in _ _ fl ci W ltac:(rewrite lset_length; ulia) Hci_in) as (cl & Hd & Hlen & H01).
  assert (Hc0 : nth_error cl 0 = Some (nth 0 cl 0)) by (apply nth_error_nth'; ulia).
  eapply (rd_cl a ci cl 0); [exact Hr | exact Ha | exact Hd | exact Hc0 | ulia |].
  (* Afterwards [c[1] = fl], whichever way the first test went. *)
  apply safe_seq with (P := fun _ h1 => exists mn1 cl1, h1 = (mn1, ma) /\
    R mn1 ma (dset st (lset (db st) ci cl1)) /\ Core val (dset st (lset (db st) ci cl1)) /\
    SI nv (dset st (lset (db st) ci cl1)) /\
    Wch (lset (db st) ci cl1) (lset (wl st) fl (firstn j L ++ skipn i L)) /\
    length cl1 = length cl /\ nth 1 cl1 0 = fl /\ Forall (lit_ok nv) cl1 /\ Permutation cl cl1).
  { assert (Hcl : Forall (lit_ok nv) cl) by (eapply Forall_nth_error; [apply (si_db _ _ (proj1 HS)) | exact Hd]).
    destruct (Nat.eqb_spec (nth 0 cl 0) fl) as [E0 | Hne].
    - assert (Hc1 : nth_error cl 1 = Some (nth 1 cl 0)) by (apply nth_error_nth'; ulia).
      eapply (rd_cl a ci cl 1); [exact Hr | exact Ha | exact Hd | exact Hc1 | ulia |].
      eapply (wr_ar s nv a ci cl 0); [exact Hr | exact Ha | exact Hd | ulia | ulia |]. intros mn1 R1.
      apply safe_unbind.
      eapply (wr_ar s nv a ci (lset cl 0 (nth 1 cl 0)) 1); [exact R1 | exact Ha | | rewrite lset_length; ulia | |].
      { cbn [dset db]. apply nth_error_lset_eq. apply nth_error_Some. congruence. }
      { cbn [dset db]. rewrite (off_dset _ _ cl) by (auto; now rewrite lset_length). ulia. }
      intros mn2 R2. apply safe_ret. cbn [dset db] in R2. rewrite lset_lset in R2.
      set (cl1 := lset (lset cl 0 (nth 1 cl 0)) 1 fl).
      assert (Hp : Permutation cl cl1) by (unfold cl1; rewrite <- E0; apply perm_swap; ulia).
      exists mn2, cl1. split; [reflexivity|]. split; [exact R2|].
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply core_dset; [exact C | exact Hd | exact Hp |].
        eapply not_reason; [exact C | exact Hd |]. intros x Hx.
        rewrite (nth_of_error cl 0 x 0 Hx) in E0. subst x. ulia.
      + apply (si_dset nv st ci cl); [exact HS | exact Hd | unfold cl1; now rewrite !lset_length |].
        eapply Permutation_Forall; [exact Hp | exact Hcl].
      + eapply wch_same_expect; [exact W | exact Hd |]. intros l. unfold cl1. rewrite <- E0. now apply expect_swap01.
      + unfold cl1. now rewrite !lset_length.
      + unfold cl1. rewrite nth_lset_eq; [reflexivity | rewrite lset_length; ulia].
      + eapply Permutation_Forall; [exact Hp | exact Hcl].
      + exact Hp.
    - apply safe_ret. exists mn, cl. split; [reflexivity|]. rewrite (lset_same _ _ _ Hd), dset_id.
      split; [exact Hr|]. split; [exact C|]. split; [exact HS|]. split; [exact W|]. split; [reflexivity|].
      split; [destruct H01; [contradiction | assumption]|]. split; [exact Hcl | reflexivity]. }
  intros _ h1 (mn1 & cl1 & -> & R1 & C1 & S1 & W1 & Hlen1 & H11 & Hok1 & Hp1).
  set (st1 := dset st (lset (db st) ci cl1)) in *.
  assert (Hci : ci < length (db st)) by (apply nth_error_Some; congruence).
  assert (Hd1 : nth_error (db st1) ci = Some cl1) by (now apply nth_error_lset_eq).
  assert (Hoff : off (db st1) ci = off (db st) ci) by (apply (off_dset _ _ cl); auto).
  assert (Hf1 : nth_error cl1 0 = Some (nth 0 cl1 0)) by (apply nth_error_nth'; ulia).
  set (first := nth 0 cl1 0) in *.
  eapply (rd_cl a ci cl1 0); [exact R1 | exact Ha | exact Hd1 | exact Hf1 | ulia |].
  assert (Hfok : lit_ok nv first) by (eapply Forall_nth_error; [exact Hok1 | exact Hf1]).
  apply safe_bind. eapply lit_value_sp; [exact R1 | apply S1 | exact Hfok |].
  set (fv1 := lval (asg st1) first).
  assert (Hfv : fv1 <= 2) by apply (asg_lval_le2 val st1 C1).
  assert (Hkeep : forall st2, wl st2 = wl st -> j < length L ->
            let st2' := wset st2 (lset (wl st2) fl (lset (nth fl (wl st2) []) j ci)) in
            lset (wl st2') fl (firstn (j + 1) (nth fl (wl st2') []) ++ skipn (i + 1) (nth fl (wl st2') [])) =
            lset (wl st) fl (firstn j L ++ skipn i L) /\
            nth fl (wl st2') [] = lset L j ci).
  { intros st2 Ew Hj st2'. unfold st2'. cbn [wl wset]. rewrite Ew. fold L.
    rewrite nth_lset_eq by ulia. rewrite lset_lset, !Nat.add_1_r, keep_step by (first [exact HiL | ulia]).
    split; reflexivity. }
  assert (Hwrite : forall st2, db st2 = db st1 -> off (db st) ci = off (db st2) ci) by (intros st2 E; rewrite E; symmetry; exact Hoff).
  destruct (Nat.eqb_spec fv1 1) as [Etrue | Hnt].
  { (* satisfied: keep watching *)
    eapply (wr_ws s nv fl w j ci); [exact R1 | exact Hw | cbn [dset wl]; ulia | exact (Hwrite st1 eq_refl) |].
    intros mn2 R2. destruct (Hkeep st1 eq_refl ltac:(ulia)) as [Hlog HL2].
    eapply IH; [exact R2 | | exact Ha | exact Hw | exact Hfl | rewrite HL2, lset_length; ulia | ulia | | | | | | exact HQ].
    - apply si_wl_lset; [exact S1|]. apply Forall_lset; [apply (wl_ok nv st1 fl); [apply S1 | apply nth_error_nth'; cbn; ulia]|].
      exists cl1. split; [exact Hd1 | ulia].
    - now apply core_wset.
    - rewrite Hlog. exact W1.
    - exact S0.
    - exact Hff.
    - exact Hcur. }
  eapply (rd_clen a ci cl1); [exact R1 | exact Ha | exact Hd1 | ulia |].
  apply safe_bind. eapply (find_watch_sp a ci cl1 _ (length cl1 - 2) 2); [exact R1 | apply S1 | exact Ha | exact Hd1 | ulia | ulia |].
  intros k1 Hk0 Hk1.
  destruct (Nat.eqb_spec k1 0) as [-> | Hk1nz].
  { (* no other literal to watch: unit or conflict *)
    specialize (Hk0 eq_refl).
    assert (Hrest : forall p, 1 <= p < length cl1 -> lval (asg st1) (nth p cl1 0) = 2).
    { intros p Hp. destruct (Nat.eq_dec p 1) as [-> | ?]; [rewrite H11; exact Hff | apply Hk0; ulia]. }
    eapply (wr_ws s nv fl w j ci); [exact R1 | exact Hw | cbn [dset wl]; ulia | exact (Hwrite st1 eq_refl) |].
    intros mn2 R2. destruct (Hkeep st1 eq_refl ltac:(ulia)) as [Hlog HL2].
    set (st2 := wset st1 (lset (wl st1) fl (lset L j ci))) in *.
    assert (S2 : SI nv st2).
    { apply si_wl_lset; [exact S1|]. apply Forall_lset; [apply (wl_ok nv st1 fl); [apply S1 | apply nth_error_nth'; cbn; ulia]|].
      exists cl1. split; [exact Hd1 | ulia]. }
    destruct (Nat.eqb_spec fv1 2) as [Efalse | Hnf].
    - (* conflict *)
      apply safe_bind. eapply (copy_rest_sp fl w m (i + 1) (j + 1)); [exact R2 | exact Hw | exact Hfl | rewrite HL2, lset_length; ulia | ulia |].
      intros mn3 R3. apply safe_ret. rewrite Hlog in R3.
      apply (HQ _ mn3 ma _ R3).
      + apply (si_wl_lset nv st1 fl _ S1).
        apply Forall_app; split; [apply Forall_firstn' | apply Forall_skipn'];
          (apply (wl_ok nv st1 fl); [apply S1 | apply nth_error_nth'; ulia]).
      + split; [apply core_wset, core_wset, C1 | split; [exact W1 | exact S0]].
      + exact Ha.
      + right. exists ci. split; [cbn [db wset dset]; rewrite <- Hoff; ulia|].
        exists ci, cl1. split; [reflexivity|]. split; [exact Hd1|]. split.
        * rewrite <- (skipn_O cl1). apply all_false_cl. intros p Hp.
          destruct p as [|p]; [exact Efalse | apply Hrest; ulia].
        * apply Exists_exists. exists fl. split; [rewrite <- H11; apply nth_In; ulia | exact Hcur].
    - (* unit: propagate [first] *)
      assert (Hfv0 : fv1 = 0) by ulia.
      apply safe_bind. eapply (enqueue_sp first (S ci)); [exact R2 | apply S2 | apply core_wset; exact C1 | exact Hfok | exact Hfv0 | cbn; ulia |].
      intros mn3 R3. cbv beta.
      assert (Hvne : lvar fl <> lvar first).
      { intros E. assert (Hz : nth (lvar first) (asg st) 0 = 0) by (apply (lval_zero _ _ (i_asg _ _ C _)); exact Hfv0).
        rewrite <- E in Hz. pose proof (i_asg _ _ C (lvar fl)).
        assert (lval (asg st) fl = 0) by (apply (lval_zero _ _ ltac:(eauto)); exact Hz). ulia. }
      eapply IH; [exact R3 | | exact Ha | exact Hw | exact Hfl | | ulia | | | | | | exact HQ].
      + apply si_enqA; [exact S2 | exact Hfok | cbn; rewrite lset_length; ulia].
      + unfold enqA, enq. cbn [wl fset]. rewrite HL2, lset_length. ulia.
      + apply (core_enqA nv); [apply core_wset; exact C1 | apply S2 | exact Hfok | exact Hfv0 | intros; ulia | |].
        * intros ci' E. assert (ci' = ci) as -> by ulia. exists cl1. split; [exact Hd1|].
          split; [exact Hf1|]. rewrite tl_skipn1. apply all_false_cl. exact Hrest.
        * intros H0. eapply unit_true; [exact C1 | exact Hd1 | exact H0 | exact Hf1 | exact Hrest].
      + unfold enqA, enq. cbn [wl fset db]. rewrite Hlog. exact W1.
      + intros v. unfold enqA, enq. cbn [fv fset fld_eqb wset dset]. apply S0.
      + unfold enqA, enq. cbn [fv fset fld_eqb wset dset]. rewrite lval_lset_neq by auto. exact Hff.
      + destruct Hcur as (k & Hk & Hlim). exists k. unfold enqA, enq. cbn [fv fset fld_eqb wset dset].
        split; [now apply at_pos_snoc | exact Hlim]. }
  (* another literal to watch: move [ci] to the list of [ck] *)
  destruct (Hk1 Hk1nz) as [Hkr Hck2]. cbv zeta.
  set (k := k1 - 1) in *.
  assert (Hk : nth_error cl1 k = Some (nth k cl1 0)) by (apply nth_error_nth'; ulia).
  set (ck := nth k cl1 0) in *.
  eapply (rd_cl a ci cl1 k); [exact R1 | exact Ha | exact Hd1 | exact Hk | ulia |].
  eapply (wr_ar s nv a ci cl1 1); [exact R1 | exact Ha | exact Hd1 | ulia | ulia |]. intros mn2 R2.
  eapply (wr_ar s nv a ci (lset cl1 1 ck) k); [exact R2 | exact Ha | | rewrite lset_length; ulia | |].
  { cbn [dset db]. apply nth_error_lset_eq. ulia. }
  { cbn [dset db]. rewrite (off_dset _ _ cl1) by (auto; now rewrite lset_length). ulia. }
  intros mn3 R3. cbn [dset db] in R3. unfold st1 in R3. cbn [dset db] in R3. rewrite !lset_lset in R3.
  set (cl2 := lset (lset cl1 1 ck) k fl) in *.
  set (st3 := dset st (lset (db st) ci cl2)) in *.
  assert (Hckfl : ck <> fl) by (intros E; rewrite E in Hck2; contradiction).
  assert (Hp2 : Permutation cl1 cl2) by (unfold cl2; rewrite <- H11; apply perm_swap; ulia).
  assert (Hckok : lit_ok nv ck) by (eapply Forall_nth_error; [exact Hok1 | exact Hk]).
  assert (Hd3 : nth_error (db st3) ci = Some cl2) by (now apply nth_error_lset_eq).
  assert (S3 : SI nv st3).
  { pose proof (si_dset nv st1 ci cl1 cl2 S1 Hd1 ltac:(unfold cl2; now rewrite !lset_length)
      (Permutation_Forall Hp2 Hok1)) as X. unfold st1 in X. cbn [dset db] in X. rewrite lset_lset in X. exact X. }
  assert (C3 : Core val st3).
  { pose proof (core_dset val st1 ci cl1 cl2 C1 Hd1 Hp2) as X. unfold st1 in X. cbn [dset db] in X.
    rewrite lset_lset in X. apply X. eapply not_reason; [exact C1 | exact Hd1 |]. intros x Hx.
    rewrite Hf1 in Hx. injection Hx as <-. exact Hnt. }
  apply safe_bind. eapply (watch_sp ck ci); [exact R3 | exact Hckok | cbn [db dset]; rewrite (off_dset _ _ cl) by (auto; unfold cl2; rewrite !lset_length; ulia); reflexivity |].
  intros mn4 ma4 R4 Ha4 Hw4. cbv beta.
  assert (Hckw : ck < length (wl st)) by (unfold lit_ok in Hckok; ulia).
  eapply IH; [exact R4 | | exact (Ha4 a Ha) | exact (Hw4 fl w ltac:(auto) Hw) | exact Hfl | | ulia | | | | | | exact HQ].
  - apply si_wl_lset; [exact S3|]. apply Forall_app. split.
    + apply (wl_ok nv st3 ck); [apply S3 | apply nth_error_nth'; cbn; ulia].
    + constructor; [|constructor]. exists cl2. split; [exact Hd3 | unfold cl2; rewrite !lset_length; ulia].
  - cbn [wl wset dset]. rewrite nth_lset_ne by auto. fold L. ulia.
  - now apply core_wset.
  - cbn [wl wset dset db]. rewrite nth_lset_ne by auto. fold L. rewrite Nat.add_1_r.
    eapply wch_rehome; [exact W1 | exact HiL | ulia | ulia | auto | apply nth_error_nth'; ulia | ulia |].
    intros l. unfold cl2. rewrite <- H11. apply expect_swap1k. ulia.
  - exact S0.
  - exact Hff.
  - exact Hcur.
Qed.

(** [propagate] keeps [Inv] and [SI], and either drains the queue
    (answer 0) or answers a conflict. *)
Lemma propagate_sp : forall fuel Q mn ma st,
  R mn ma st -> SI nv st -> Inv val st ->
  (forall r mn' ma' st', R mn' ma' st' -> SI nv st' -> Inv val st' ->
     (r = 0 -> length (tr st') <= qhead st') -> confl_ok st' r -> Q r (mn', ma')) ->
  safe (propagate s fuel) Q (mn, ma).
Proof.
  induction fuel as [|f IH]; intros Q mn ma st Hr HS (C & W & S0) HQ; cbn [propagate].
  { apply safe_out_of_fuel. }
  unfold get, put. destruct (repr_counts _ _ _ _ _ Hr) as (Etl & _ & _ & _ & Hmisc & Hwll).
  eapply (rd_misc s nv QHEAD); [exact Hr | unfold QHEAD, NMISC; ulia |].
  eapply (rd_misc s nv TLEN); [exact Hr | unfold TLEN, NMISC; ulia |]. rewrite Etl.
  destruct (Nat.leb_spec (length (tr st)) (qhead st)).
  { apply safe_ret. apply (HQ 0 mn ma st Hr HS); [split; auto | intros; ulia | now left]. }
  assert (Hqh : nth_error (tr st) (qhead st) = Some (nth (qhead st) (tr st) 0)) by (apply nth_error_nth'; ulia).
  set (p := nth (qhead st) (tr st) 0) in *.
  eapply (rd_fld s nv FTr (qhead st) p); [exact Hr | discriminate | exact Hqh |].
  eapply (wr_plain s nv FMisc QHEAD); [exact Hr | unfold plain; tauto | intros _; unfold kept, QHEAD, TLEN, TLLEN, LLEN, ALEN, ACAP; ulia | rewrite Hmisc; unfold QHEAD, NMISC; ulia |].
  intros mn1 R1. cbv zeta.
  set (st1 := fset st FMisc (lset (fv st FMisc) QHEAD (qhead st + 1))) in *.
  assert (Hpok : lit_ok nv p) by exact (tr_lit nv st _ p (proj1 HS) Hqh).
  assert (Hfl : lit_ok nv (lneg p)) by (apply lit_ok_lneg; exact Hpok).
  assert (Hq1 : qhead st1 = qhead st + 1).
  { unfold st1. cbn [fv fset fld_eqb]. apply nth_lset_eq. rewrite Hmisc. unfold QHEAD, NMISC. ulia. }
  assert (C1 : Core val st1).
  { apply core_fset_misc; [exact C|]. fold st1. cbn [fv fset fld_eqb] in Hq1 |- *. unfold st1 in Hq1. cbn [fv fset fld_eqb] in Hq1. ulia. }
  assert (S1 : SI nv st1) by (split; [apply sic_lset; [apply HS | tauto] | apply HS]).
  eapply (rd_wdata s nv (lneg p)); [exact R1 | exact Hfl |]. intros ws Hws.
  eapply (rd_wlen s nv (lneg p)); [exact R1 | exact Hfl |].
  eapply (rd_ref s nv); [exact R1 |]. intros a Ha.
  apply safe_bind. eapply (prop_watch_sp a (lneg p) ws _ 0 0); [exact R1 | exact S1 | exact Ha | exact Hws | exact Hfl | ulia | ulia | exact C1 | | exact S0 | | |].
  - cbn [firstn skipn app]. unfold st1. cbn [wl db fset]. rewrite (lset_same (wl st) (lneg p) (nth (lneg p) (wl st) [])); [exact W | apply nth_error_nth'; unfold lit_ok in Hfl; lia].
  - unfold st1. cbn [fv fset fld_eqb]. apply (lneg_trail_false val st p C). eapply nth_error_In; eauto.
  - exists (qhead st). unfold st1. cbn [fv fset fld_eqb]. split.
    + exists p. split; [exact Hqh | symmetry; apply lvar_lneg].
    + apply (i_limq _ _ C).
  - intros confl mn2 ma2 st2 R2 S2 I2 _ Hc. cbv beta. destruct (Nat.eqb_spec confl 0) as [-> | Hne].
    + eapply IH; [exact R2 | exact S2 | exact I2 | exact HQ].
    + apply safe_ret. apply (HQ _ _ _ _ R2 S2 I2); [ulia | exact Hc].
Qed.


(** * Backjumping *)

(** What [unassign] leaves: the variables of [seg] unassigned, and only
    the assignment, the reasons and the phases written. *)
Definition unas (st st' : astate) (seg : list nat) : Prop :=
  db st' = db st /\ wl st' = wl st /\
  (forall f, f <> FAsg -> f <> FRsn -> f <> FPh -> fv st' f = fv st f) /\
  (forall w, In w seg -> nth w (asg st') 0 = 0) /\
  (forall w, ~ In w seg -> nth w (asg st') 0 = nth w (asg st) 0) /\
  (forall w, ~ In w seg -> nth w (rsn st') 0 = nth w (rsn st) 0).

(** [unassign i m] unassigns the variables at trail positions [i - m] up to
    [i], exclusive, in the sense of [unas]. *)
Lemma unassign_sp : forall m i Q mn ma st,
  R mn ma st -> SIc nv st -> m <= i -> i <= length (tr st) ->
  (forall mn' st', R mn' ma st' -> SIc nv st' -> unas st st' (map lvar (skipn (i - m) (firstn i (tr st)))) ->
     Q tt (mn', ma)) ->
  safe (unassign s i m) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros i Q mn ma st Hr Hs Hm Hi HQ; cbn [unassign].
  { apply safe_ret. apply (HQ mn st Hr Hs). rewrite Nat.sub_0_r, skipn_all2 by (rewrite length_firstn; lia).
    repeat split; auto; intros w []. }
  assert (Hl : nth_error (tr st) (i - 1) = Some (nth (i - 1) (tr st) 0)) by (apply nth_error_nth'; lia).
  set (l := nth (i - 1) (tr st) 0) in *.
  assert (Hv : lvar l < nv) by (apply lit_ok_var; exact (tr_lit nv st _ l Hs Hl)).
  pose proof (si_asg _ _ Hs) as La. pose proof (si_rsn _ _ Hs) as Lr. pose proof (si_ph _ _ Hs) as Lp.
  eapply (rd_fld s nv FTr (i - 1) l); [exact Hr | discriminate | exact Hl |]. cbv zeta.
  eapply (rd_fld s nv FAsg (lvar l)); [exact Hr | discriminate | apply nth_error_nth'; lia |].
  eapply (wr_plain s nv FPh); [exact Hr | unfold plain; tauto | discriminate | lia |]. intros mn1 R1.
  eapply (wr_plain s nv FAsg); [exact R1 | unfold plain; tauto | discriminate | cbn; lia |]. intros mn2 R2.
  eapply (wr_rsn s nv (lvar l) 0); [exact R2 | cbn; lia | reflexivity |]. intros mn3 R3.
  set (st3 := fset (fset (fset st FPh (lset (fv st FPh) (lvar l) (nth (lvar l) (asg st) 0))) FAsg
                (lset (asg (fset st FPh (lset (fv st FPh) (lvar l) (nth (lvar l) (asg st) 0)))) (lvar l) 0)) FRsn
                (lset (rsn (fset (fset st FPh (lset (fv st FPh) (lvar l) (nth (lvar l) (asg st) 0))) FAsg
                (lset (asg (fset st FPh (lset (fv st FPh) (lvar l) (nth (lvar l) (asg st) 0)))) (lvar l) 0))) (lvar l) 0)) in *.
  assert (S3 : SIc nv st3).
  { unfold st3. apply sic_rsn; [|cbn; lia]. apply sic_lset; [|tauto]. apply sic_lset; [exact Hs | tauto]. }
  eapply IH; [exact R3 | exact S3 | lia | unfold st3; cbn [fv fset fld_eqb]; lia |].
  intros mn' st' R' S' (E1 & E2 & Ef & Az & Ak & Rk). apply (HQ mn' st' R' S').
  unfold st3 in *. cbn [fv fset fld_eqb db wl] in *.
  assert (Hseg : map lvar (skipn (i - S m) (firstn i (tr st))) =
                 map lvar (skipn (i - 1 - m) (firstn (i - 1) (tr st))) ++ [lvar l]).
  { replace i with (S (i - 1)) at 2 by lia. rewrite (firstn_S_snoc _ _ _ Hl), skipn_snoc, map_app.
    - f_equal. f_equal. f_equal. lia.
    - rewrite length_firstn. lia. }
  rewrite Hseg. split; [exact E1|]. split; [exact E2|]. split; [|split; [|split]].
  - intros g H1 H2 H3. rewrite Ef by auto. destruct g; try reflexivity; congruence.
  - intros w Hw. apply in_app_or in Hw as [Hw | [<- | []]].
    + now apply Az.
    + destruct (in_dec Nat.eq_dec (lvar l) (map lvar (skipn (i - 1 - m) (firstn (i - 1) (tr st))))) as [Hin | Hin].
      * now apply Az.
      * rewrite Ak by exact Hin. apply nth_lset_eq. lia.
  - intros w Hw. rewrite Ak by (intros Hx; apply Hw, in_or_app; auto).
    apply nth_lset_ne. intros E. apply Hw, in_or_app. right. now left.
  - intros w Hw. rewrite Rk by (intros Hx; apply Hw, in_or_app; auto).
    apply nth_lset_ne. intros E. apply Hw, in_or_app. right. now left.
Qed.

(** What [backtrack] keeps: the clauses, watch lists, levels, stamps,
    marks, learnt clause, and the counters other than the trail length,
    the level count and the queue head. *)
Definition bt_keep (st st' : astate) : Prop :=
  db st' = db st /\ wl st' = wl st /\ lvl st' = lvl st /\ fv st' FSt = fv st FSt /\ sn st' = sn st /\
  lrn st' = lrn st /\ length (fv st' FMisc) = length (fv st FMisc) /\
  (forall k, k <> TLEN -> k <> TLLEN -> k <> QHEAD -> nth k (fv st' FMisc) 0 = nth k (fv st FMisc) 0).

(** [backtrack lv] keeps [Inv] and [SI], and for [lv] below the current
    level performs the jump [bt_rel]; otherwise it changes nothing. *)
Lemma backtrack_sp lv Q mn ma st :
  R mn ma st -> SI nv st -> Inv val st ->
  (forall mn' st', R mn' ma st' -> SI nv st' -> Inv val st' -> bt_keep st st' ->
     (lv < length (lim st) -> bt_rel st st' lv) -> Q tt (mn', ma)) ->
  safe (backtrack s lv) Q (mn, ma).
Proof.
  intros Hr HS (C & W & S0) HQ. unfold backtrack, decision_level, get, put.
  destruct (repr_counts _ _ _ _ _ Hr) as (Etl & Etll & _ & _ & Hmisc & _).
  eapply (rd_misc s nv TLLEN); [exact Hr | unfold TLLEN, NMISC; lia |]. rewrite Etll.
  destruct (Nat.leb_spec (length (lim st)) lv).
  { apply safe_ret. apply (HQ mn st Hr HS); [split; auto | repeat split; auto | intros; lia]. }
  assert (Hm : nth_error (lim st) lv = Some (nth lv (lim st) 0)) by (apply nth_error_nth'; lia).
  set (m := nth lv (lim st) 0) in *.
  eapply (rd_fld s nv FLim lv m); [exact Hr | discriminate | exact Hm |].
  eapply (rd_misc s nv TLEN); [exact Hr | unfold TLEN, NMISC; lia |]. rewrite Etl.
  assert (Hmq : m <= length (tr st)).
  { pose proof (i_limq _ _ C) as F. rewrite Forall_forall in F.
    pose proof (F m ltac:(apply nth_In; lia)). pose proof (i_qtr _ _ C). lia. }
  apply safe_bind. eapply (unassign_sp (length (tr st) - m) (length (tr st))); [exact Hr | apply HS | lia | lia |].
  intros mn1 st1 R1 S1 (E1 & E2 & Ef & Az & Ak & Rk). cbv beta.
  replace (length (tr st) - (length (tr st) - m)) with m in Az, Ak, Rk by lia.
  rewrite firstn_all in Az, Ak, Rk.
  assert (Et1 : tr st1 = tr st) by (apply Ef; discriminate).
  assert (El1 : lim st1 = lim st) by (apply Ef; discriminate).
  assert (Em1 : fv st1 FMisc = fv st FMisc) by (apply Ef; discriminate).
  eapply (wr_shrink s nv FTr m); [exact R1 | unfold seqf; tauto | rewrite Et1; lia |]. intros mn2 R2.
  eapply (wr_shrink s nv FLim lv); [exact R2 | unfold seqf; tauto | cbn [fv fset fld_eqb]; rewrite El1; lia |].
  intros mn3 R3. apply safe_unbind.
  eapply (wr_plain s nv FMisc QHEAD m); [exact R3 | unfold plain; tauto | intros _; unfold kept, QHEAD, TLEN, TLLEN, LLEN, ALEN, ACAP; lia | cbn [fv fset fld_eqb]; rewrite !lset_length, Em1, Hmisc; unfold QHEAD, NMISC; lia |].
  intros mn4 R4. apply safe_ret.
  match type of R4 with repr _ _ _ _ ?X => set (st4 := X) in R4 end.
  cbn [slot] in st4.
  assert (Hq4 : qhead st4 = m).
  { unfold st4. cbn [fv fset fld_eqb]. apply nth_lset_eq. rewrite !lset_length, Em1, Hmisc. unfold QHEAD, NMISC. lia. }
  assert (Hbt : bt_rel st st4 lv).
  { unfold bt_rel. cbv zeta. fold m. unfold st4. cbn [fv fset fld_eqb db].
    rewrite Et1, El1, (Ef FLvl) by discriminate.
    split; [exact E1|]. split; [exact Az|]. split; [exact Ak|]. split; [reflexivity|].
    split; [exact Rk|]. split; [reflexivity|]. split; [reflexivity|]. exact Hq4. }
  apply (HQ mn4 st4 R4).
  - apply (si_bt nv st st4 lv HS); [| lia | unfold st4; cbn [fv fset fld_eqb]; now rewrite Et1
                                      | unfold st4; cbn [fv fset fld_eqb]; now rewrite El1].
    unfold st4. apply sic_lset; [|tauto]. apply sic_lim; [|cbn [fv fset fld_eqb]; rewrite El1; apply incr_firstn, (si_inc _ _ (proj1 HS))].
    apply sic_lset; [|tauto]. apply sic_tr; [|cbn [fv fset fld_eqb]; rewrite Et1; apply Forall_firstn', (si_tr _ _ (proj1 HS))].
    apply sic_lset; [exact S1 | tauto].
  - split; [eapply core_bt; eauto|]. split.
    + unfold st4. cbn [fv fset fld_eqb db wl]. rewrite E1, E2. exact W.
    + intros v. unfold st4. cbn [fv fset fld_eqb]. rewrite (Ef FSn) by discriminate. apply S0.
  - unfold bt_keep, st4. cbn [fv fset fld_eqb db wl]. split; [exact E1|]. split; [exact E2|].
    rewrite !(Ef FLvl), !(Ef FSt), !(Ef FSn), !(Ef FLrn) by discriminate. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. rewrite Em1, !lset_length.
    split; [reflexivity|]. intros k H1 H2 H3. rewrite !nth_lset_ne by (unfold TLEN, TLLEN, QHEAD in *; lia).
    reflexivity.
  - intros _. exact Hbt.
Qed.


(** * Conflict analysis *)

(** A property of the valuation, when there is one. *)
Definition opt (P : (nat -> bool) -> Prop) : Prop := forall v, val = Some v -> P v.

(** A state of the conflict analysis begun in [st0]: only the marks, the
    stamps, the learnt clause and its length counter differ. *)
Definition an_st (st0 st : astate) : Prop :=
  db st = db st0 /\ wl st = wl st0 /\
  (forall f, f <> FSn -> f <> FSt -> f <> FLrn -> f <> FMisc -> fv st f = fv st0 f) /\
  length (fv st FMisc) = length (fv st0 FMisc) /\
  (forall k, k <> LLEN -> nth k (fv st FMisc) 0 = nth k (fv st0 FMisc) 0) /\ SIc nv st.

(** The analysis starts in [st0]. *)
Lemma an_refl st0 : SIc nv st0 -> an_st st0 st0.
Proof. intros H. unfold an_st; split; [|split; [|split; [|split; [|split]]]]; auto. Qed.

(** Writing a mark or a stamp keeps [an_st]. *)
Lemma an_mark st0 st f i x :
  an_st st0 st -> f = FSn \/ f = FSt -> an_st st0 (fset st f (lset (fv st f) i x)).
Proof.
  intros (E1 & E2 & Ef & Em & Ek & Hs) Hf. unfold an_st; split; [|split; [|split; [|split; [|split]]]]; cbn [fv fset db wl]; auto.
  - intros g H1 H2 H3 H4. destruct (fld_eqb g f) eqn:E; [apply fld_eqb_eq in E; subst; destruct Hf; congruence | auto].
  - destruct (fld_eqb FMisc f) eqn:E; [apply fld_eqb_eq in E; destruct Hf; congruence | auto].
  - intros k Hk. destruct (fld_eqb FMisc f) eqn:E; [apply fld_eqb_eq in E; destruct Hf; congruence | auto].
  - apply sic_lset; [exact Hs | tauto].
Qed.

(** Writing the learnt clause and its counter keeps [an_st]. *)
Lemma an_lrn st0 st n xs :
  an_st st0 st -> an_st st0 (fset (fset st FMisc (lset (fv st FMisc) LLEN n)) FLrn xs).
Proof.
  intros (E1 & E2 & Ef & Em & Ek & Hs). unfold an_st; split; [|split; [|split; [|split; [|split]]]]; cbn [fv fset fld_eqb db wl]; auto.
  - intros g H1 H2 H3 H4. destruct g; cbn; auto; congruence.
  - now rewrite lset_length.
  - intros k Hk. rewrite nth_lset_ne by auto. auto.
  - apply sic_lrn. apply sic_lset; [exact Hs | tauto].
Qed.

(** Writing the learnt clause keeps [an_st]. *)
Lemma an_lrn_set st0 st xs : an_st st0 st -> an_st st0 (fset st FLrn xs).
Proof.
  intros (E1 & E2 & Ef & Em & Ek & Hs). unfold an_st; split; [|split; [|split; [|split; [|split]]]]; cbn [fv fset fld_eqb db wl]; auto.
  - intros g H1 H2 H3 H4. destruct g; cbn; auto; congruence.
  - apply sic_lrn, Hs.
Qed.

(** An analysis state satisfies [Core] like [st0]. *)
Lemma an_core st0 st : Core val st0 -> an_st st0 st -> Core val st.
Proof.
  intros C (E1 & E2 & Ef & Em & Ek & Hs). apply (core_ext val st0 st); auto; try (apply Ef; discriminate).
  apply Ek. unfold QHEAD, LLEN. lia.
Qed.

(** The head slot of the learnt clause does not matter to [AInv]. *)
Lemma ainv_head st M a b t index pathC : AInv st M (a :: t) index pathC -> AInv st M (b :: t) index pathC.
Proof. intros []. constructor; cbn [tl] in *; auto. discriminate. Qed.

(** [push_learnt q] appends [q] to the learnt clause. *)
Lemma push_learnt_sp q Q mn ma st :
  R mn ma st -> length (lrn st) < nv + 1 ->
  (forall mn', R mn' ma (fset (fset st FMisc (lset (fv st FMisc) LLEN (length (lrn st) + 1))) FLrn (lrn st ++ [q])) ->
     Q tt (mn', ma)) ->
  safe (push_learnt s q) Q (mn, ma).
Proof.
  intros Hr Hl HQ. unfold push_learnt, get, put. destruct (repr_counts _ _ _ _ _ Hr) as (_ & _ & Ell & _).
  eapply (rd_misc s nv LLEN); [exact Hr | unfold LLEN, NMISC; lia |]. rewrite Ell.
  eapply (wr_push_end s nv FLrn q Q mn ma st Hr); [unfold seqf; tauto | exact Hl | exact HQ].
Qed.

Section Analyze.
(** The analysis of a conflict in [st0], at a nonzero level; [now] is the
    stamp for newly marked variables. *)
Variables (st0 : astate) (a : narr) (now : nat).
Hypotheses (C0 : Core val st0) (Hne0 : lim st0 <> []) (S0c : SIc nv st0).

(** One pass over clause [ci] from position [j]: a false literal above
    level 0 is marked, and goes into the learnt clause below the current
    level or counts in [pathC] at it.  [AInv] holds throughout, and marks
    only grow. *)
Lemma analyze_lits_sp ci cl : forall m j pathC index Q mn ma stc,
  R mn ma stc -> an_st st0 stc -> refp ma (arena s) a -> nth_error (db st0) ci = Some cl -> j + m = length cl ->
  AInv st0 (sn stc) (lrn stc) index pathC ->
  (forall p, j <= p < length cl -> lval (asg st0) (nth p cl 0) = 2 /\
                                    exists k, at_pos (tr st0) k (lvar (nth p cl 0)) /\ k <= index) ->
  (forall r mn' stc', R mn' ma stc' -> an_st st0 stc' -> AInv st0 (sn stc') (lrn stc') index r ->
     (forall u, marked (sn stc) u -> marked (sn stc') u) ->
     (forall p, j <= p < length cl -> 0 < nth (lvar (nth p cl 0)) (lvl st0) 0 ->
                marked (sn stc') (lvar (nth p cl 0))) ->
     Q r (mn', ma)) ->
  safe (analyze_lits s a (off (db st0) ci) j m (length (lim st0)) pathC now) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros j pathC index Q mn ma stc Hr Han Ha Hd Hjm A Hpend HQ; cbn [analyze_lits].
  { apply safe_ret. apply (HQ pathC mn stc Hr Han A); [auto | intros; lia]. }
  pose proof Han as (E1 & E2 & Ef & Em & Ek & Hs).
  assert (Hj : nth_error cl j = Some (nth j cl 0)) by (apply nth_error_nth'; lia).
  set (q := nth j cl 0) in *.
  eapply (rd_cl a ci cl j q); [exact Hr | exact Ha | rewrite E1; exact Hd | exact Hj | now rewrite E1 |]. cbv zeta.
  assert (Hqok : lit_ok nv q) by exact (db_lit nv st0 ci cl j q S0c Hd Hj).
  assert (Hvn : lvar q < nv) by (apply lit_ok_var; exact Hqok).
  pose proof (si_sn _ _ Hs) as Lsn. pose proof (si_st _ _ Hs) as Lst.
  destruct (Hpend j ltac:(lia)) as [Hqf (k & Hk & Hki)].
  assert (Hlv : nth (lvar q) (lvl st0) 0 = count_le (lim st0) k) by (eapply lvl_at; eauto).
  eapply (rd_fld s nv FSn (lvar q) (nth (lvar q) (sn stc) 0)); [exact Hr | discriminate | apply nth_error_nth'; lia |].
  eapply (rd_fld s nv FLvl (lvar q) (nth (lvar q) (lvl stc) 0)); [exact Hr | discriminate | apply nth_error_nth'; rewrite (si_lvl _ _ Hs); lia |].
  rewrite (Ef FLvl), Hlv by discriminate.
  (* every later step keeps the marks this one leaves *)
  assert (Hrest : forall mn1 stc1 pathC1, R mn1 ma stc1 -> an_st st0 stc1 ->
            AInv st0 (sn stc1) (lrn stc1) index pathC1 -> (forall u, marked (sn stc) u -> marked (sn stc1) u) ->
            (0 < count_le (lim st0) k -> marked (sn stc1) (lvar q)) ->
            safe (analyze_lits s a (off (db st0) ci) (j + 1) m (length (lim st0)) pathC1 now) Q (mn1, ma)).
  { intros mn1 stc1 pathC1 Hr1 Han1 A1 Hmono1 Hq1.
    eapply IH; [exact Hr1 | exact Han1 | exact Ha | exact Hd | lia | exact A1 | |].
    - intros p' Hp'. apply Hpend. lia.
    - intros r mn' stc' Hr' Han' A' Hmono' Hpend'. apply (HQ r mn' stc' Hr' Han' A').
      + intros u Hu. auto.
      + intros p' Hp'' Hlvp. destruct (Nat.eq_dec p' j) as [-> | Hne].
        * apply Hmono'. apply Hq1. fold q in Hlvp. lia.
        * apply Hpend'; [lia | exact Hlvp]. }
  destruct (Nat.eqb_spec (nth (lvar q) (sn stc) 0) 0) as [Hs0 | Hs0];
    destruct (Nat.ltb_spec 0 (count_le (lim st0) k)) as [Hl0 | Hl0]; cbn [andb].
  - (* a new mark *)
    eapply (wr_plain s nv FSn (lvar q) 1); [exact Hr | unfold plain; tauto | discriminate | lia |]. intros mn1 R1.
    eapply (wr_plain s nv FSt (lvar q) now); [exact R1 | unfold plain; tauto | discriminate | cbn; lia |].
    intros mn2 R2.
    set (stc2 := fset (fset stc FSn (lset (sn stc) (lvar q) 1)) FSt
                   (lset (fv (fset stc FSn (lset (sn stc) (lvar q) 1)) FSt) (lvar q) now)) in *.
    assert (Han2 : an_st st0 stc2) by (apply an_mark; [apply an_mark; auto | auto]).
    assert (Hnm : ~ marked (sn stc) (lvar q)) by (unfold marked; lia).
    assert (Hmono : forall u, marked (sn stc) u -> marked (lset (sn stc) (lvar q) 1) u)
      by (intros; apply marked_mono1; [lia | auto]).
    assert (Hqm : marked (lset (sn stc) (lvar q) 1) (lvar q))
      by (apply marked_lset; [lia | rewrite Nat.eqb_refl; lia]).
    destruct (Nat.leb_spec (length (lim st0)) (count_le (lim st0) k)) as [Hcur | Hlow].
    + (* current level: one more path *)
      pose proof (count_le_max (lim st0) k).
      assert (Hbk : base st0 <= k) by (apply (cur_iff val st0 C0 Hne0); lia).
      eapply Hrest; [exact R2 | exact Han2 | | | ].
      * unfold stc2. cbn [fv fset fld_eqb]. rewrite Nat.add_1_r. eapply ainv_mark_cur; eauto. lia.
      * unfold stc2. cbn [fv fset fld_eqb]. exact Hmono.
      * unfold stc2. cbn [fv fset fld_eqb]. intros _. exact Hqm.
    + (* lower level: into the learnt clause *)
      apply safe_bind. eapply (push_learnt_sp q); [exact R2 | |].
      { unfold stc2. cbn [fv fset fld_eqb].
        pose proof (learnt_room nv val st0 (sn stc) (lrn stc) index pathC q C0 S0c A Hqf Hnm). lia. }
      intros mn3 R3. cbv beta.
      eapply Hrest; [exact R3 | apply an_lrn; exact Han2 | | | ].
      * unfold stc2. cbn [fv fset fld_eqb]. eapply ainv_mark_low; eauto. lia.
      * unfold stc2. cbn [fv fset fld_eqb]. exact Hmono.
      * unfold stc2. cbn [fv fset fld_eqb]. intros _. exact Hqm.
  - (* level 0: nothing to do *)
    eapply Hrest; [exact Hr | exact Han | exact A | auto | intros; lia].
  - (* already marked *)
    eapply Hrest; [exact Hr | exact Han | exact A | auto | intros _; exact Hs0].
  - eapply Hrest; [exact Hr | exact Han | exact A | auto | intros; lia].
Qed.

(** [next_seen i] finds the highest marked trail position at or below [i],
    given one at or above the current level's [base]. *)
Lemma next_seen_sp : forall fuel i Q mn ma stc,
  R mn ma stc -> an_st st0 stc -> i < length (tr st0) ->
  (exists k, base st0 <= k <= i /\ marked (sn stc) (lvar (nth k (tr st0) 0))) ->
  (forall idx, base st0 <= idx <= i -> marked (sn stc) (lvar (nth idx (tr st0) 0)) ->
     (forall k, idx < k <= i -> ~ marked (sn stc) (lvar (nth k (tr st0) 0))) -> Q idx (mn, ma)) ->
  safe (next_seen s fuel i) Q (mn, ma).
Proof.
  induction fuel as [|f IH]; intros i Q mn ma stc Hr Han Hi Hex HQ; cbn [next_seen].
  { apply safe_out_of_fuel. }
  pose proof Han as (_ & _ & Ef & _ & _ & Hs).
  assert (Et : tr stc = tr st0) by (apply Ef; discriminate).
  eapply (rd_fld s nv FTr i (nth i (tr st0) 0)); [exact Hr | discriminate | rewrite Et; apply nth_error_nth'; lia |].
  assert (Hv : lvar (nth i (tr st0) 0) < nv).
  { apply lit_ok_var. apply (tr_lit nv st0 i _ S0c). apply nth_error_nth'. lia. }
  eapply (rd_fld s nv FSn _ (nth (lvar (nth i (tr st0) 0)) (sn stc) 0)); [exact Hr | discriminate | apply nth_error_nth'; rewrite (si_sn _ _ Hs); exact Hv |].
  destruct (Nat.eqb_spec (nth (lvar (nth i (tr st0) 0)) (sn stc) 0) 0) as [E | E].
  - destruct Hex as (k & Hk & Hm).
    assert (Hki : k <> i) by (intros ->; unfold marked in Hm; lia).
    eapply IH; [exact Hr | exact Han | lia | exists k; split; [lia | exact Hm] |].
    intros idx Hidx Hmi Hnone. apply HQ; [lia | exact Hmi |].
    intros k' Hk'. destruct (Nat.eq_dec k' i) as [-> | ?]; [unfold marked; lia | apply Hnone; lia].
  - apply safe_ret. destruct Hex as (k & Hk & _). apply HQ; [lia | exact E | intros; lia].
Qed.

(** The first-UIP loop resolves backwards along the trail until one
    marked literal [p] is left at the current level.  The learnt clause's
    tail then holds false literals at lower nonzero levels, and the
    valuation (if any) makes [lneg p] or one of them true. *)
Lemma analyze_loop_sp : forall fuel ci cl start index pathC Q mn ma stc,
  R mn ma stc -> an_st st0 stc -> refp ma (arena s) a -> nth_error (db st0) ci = Some cl -> start <= length cl ->
  AInv st0 (sn stc) (lrn stc) index pathC ->
  (forall p, start <= p < length cl -> lval (asg st0) (nth p cl 0) = 2 /\
                                       exists k, at_pos (tr st0) k (lvar (nth p cl 0)) /\ k <= index) ->
  (1 <= pathC \/ exists p k, start <= p < length cl /\ at_pos (tr st0) k (lvar (nth p cl 0)) /\ base st0 <= k) ->
  opt (fun v => (exists u, marked (sn stc) u /\ disagree v (asg st0) u) \/ Exists (lit_true v) (skipn start cl)) ->
  (forall p mn' stc', R mn' ma stc' -> an_st st0 stc' ->
     (exists idx, nth_error (tr st0) idx = Some p /\ base st0 <= idx) ->
     (forall u, marked (sn stc') u -> exists q, In q (tl (lrn stc')) /\ lvar q = u) ->
     lrn stc' <> [] ->
     Forall (fun q => lval (asg st0) q = 2 /\ 0 < nth (lvar q) (lvl st0) 0 < length (lim st0)) (tl (lrn stc')) ->
     opt (fun v => lit_true v (lneg p) \/ Exists (lit_true v) (tl (lrn stc'))) ->
     Q p (mn', ma)) ->
  safe (analyze_loop s fuel a (off (db st0) ci) start index pathC (length (lim st0)) now) Q (mn, ma).
Proof.
  induction fuel as [|f IH]; intros ci cl start index pathC Q mn ma stc Hr Han Ha Hd Hst A Hpend Hpath Hsound HQ;
    cbn [analyze_loop].
  { apply safe_out_of_fuel. }
  pose proof Han as (E1 & E2 & Ef & Em & Ek & Hs).
  assert (Hasg : forall u, nth u (asg st0) 0 <= 2) by apply (i_asg _ _ C0).
  eapply (rd_clen a ci cl); [exact Hr | exact Ha | rewrite E1; exact Hd | now rewrite E1 |].
  apply safe_bind. eapply (analyze_lits_sp ci cl (length cl - start) start);
    [exact Hr | exact Han | exact Ha | exact Hd | lia | exact A | exact Hpend |].
  intros pathC1 mn1 stc1 Hr1 Han1 A1 Hmono Hmarked. cbv beta.
  pose proof Han1 as (F1 & F2 & Ff & Fm & Fk & Fs).
  (* at least one marked literal at the current level *)
  assert (Hpc1 : 1 <= pathC1).
  { rewrite (a_cnt _ _ _ _ _ A1). destruct Hpath as [Hpc | (p & k & Hp' & Hk & Hbk)].
    - rewrite (a_cnt _ _ _ _ _ A) in Hpc. etransitivity; [exact Hpc | now apply cntm_mono].
    - destruct (Hpend p Hp') as [_ (k' & Hk' & Hk'i)].
      rewrite <- (pos_unique val st0 C0 _ _ _ Hk Hk') in Hk'i.
      apply (cntm_pos _ _ _ _ k); [lia|].
      apply at_pos_nth in Hk as [Hkt Ek0]. rewrite Ek0. apply Hmarked; [lia|].
      rewrite (lvl_at val st0 C0 k) by (apply at_pos_nth; auto).
      pose proof (proj2 (cur_iff val st0 C0 Hne0 k) Hbk). destruct (lim st0); [congruence | cbn [length] in *; lia]. }
  (* a marked literal the valuation disagrees with *)
  assert (Hdis : opt (fun v => exists u, marked (sn stc1) u /\ disagree v (asg st0) u)).
  { intros v Hv. destruct (Hsound v Hv) as [(u & Hu & Hdu) | Hex].
    - exists u. auto.
    - apply Exists_exists in Hex as (q & Hq & Ht). apply in_skipn_nth in Hq as (p & Hp' & <-).
      destruct (Hpend p Hp') as [Hf (k & Hk & _)].
      exists (lvar (nth p cl 0)). split; [|now apply false_true_disagree].
      apply Hmarked; [exact Hp'|]. destruct (Nat.eq_dec (nth (lvar (nth p cl 0)) (lvl st0) 0) 0) as [E0 | ?]; [|lia].
      exfalso. assert (C0v : Core (Some v) st0) by (rewrite <- Hv; exact C0). exact (false_l0 v st0 C0v _ Hf E0 Ht). }
  assert (Hidx_ok : index < length (tr st0)) by apply (a_idx _ _ _ _ _ A1).
  apply safe_bind. eapply (next_seen_sp (S f) index); [exact Hr1 | exact Han1 | exact Hidx_ok | |].
  { destruct (cntm_exists (tr st0) (sn stc1) (base st0) (S index)) as (k & Hk & Hm);
      [rewrite <- (a_cnt _ _ _ _ _ A1); lia|].
    exists k. split; [lia | exact Hm]. }
  intros idx Hidx Hmi Hnone. cbv beta.
  assert (Hidxt : idx < length (tr st0)) by lia.
  assert (Hp' : nth_error (tr st0) idx = Some (nth idx (tr st0) 0)) by (apply nth_error_nth'; lia).
  set (p := nth idx (tr st0) 0) in *.
  assert (Et1 : tr stc1 = tr st0) by (apply Ff; discriminate).
  eapply (rd_fld s nv FTr idx p); [exact Hr1 | discriminate | rewrite Et1; exact Hp' |]. cbv zeta.
  assert (Hv : lvar p < nv) by (apply lit_ok_var; exact (tr_lit nv st0 idx p S0c Hp')).
  assert (Er1 : rsn stc1 = rsn st0) by (apply Ff; discriminate).
  eapply (rd_rsn s nv (lvar p) (nth (lvar p) (rsn st0) 0)); [exact Hr1 | rewrite Er1; apply nth_error_nth'; rewrite (si_rsn _ _ S0c); exact Hv |].
  rewrite F1.
  eapply (wr_plain s nv FSn (lvar p) 0); [exact Hr1 | unfold plain; tauto | discriminate | rewrite (si_sn _ _ Fs); exact Hv |].
  intros mn2 R2.
  set (stc2 := fset stc1 FSn (lset (sn stc1) (lvar p) 0)) in *.
  assert (Han2 : an_st st0 stc2) by (apply an_mark; auto).
  assert (Hv1 : lvar p < length (sn stc1)) by (rewrite (si_sn _ _ Fs); exact Hv).
  assert (Hptrue : lval (asg st0) p = 1) by (apply (true_on_trail val st0 C0); eapply nth_error_In; eauto).
  destruct (Nat.leb_spec pathC1 1) as [Hle | Hgt].
  - (* the first UIP *)
    apply safe_ret. apply (HQ p mn2 stc2 R2 Han2).
    + exists idx. split; [exact Hp' | lia].
    + unfold stc2. cbn [fv fset fld_eqb]. eapply ainv_final; eauto.
    + apply (a_lr_ne _ _ _ _ _ A1).
    + eapply Forall_impl; [|apply (a_lr _ _ _ _ _ A1)]. intros q (H1 & _ & H3). auto.
    + intros v Hvv. destruct (Hdis v Hvv) as (u & Hu & Hdu). destruct (Nat.eq_dec u (lvar p)) as [-> | Hne].
      * left. eapply true_disagree_false; eauto.
      * right. destruct (ainv_final val st0 C0 Hne0 _ _ _ _ idx A1 ltac:(lia) Hmi Hnone Hle Hv1 u)
          as (q & Hq & Eq).
        { apply marked_lset; [exact Hv1|]. fold p. destruct (Nat.eqb_spec (lvar p) u); [congruence | exact Hu]. }
        apply Exists_exists. exists q. split; [exact Hq|].
        pose proof (proj1 (Forall_forall _ _) (a_lr _ _ _ _ _ A1) q Hq) as (Hqf & _).
        subst u. eapply false_disagree_true; eauto.
  - (* resolve with the reason of [p] *)
    destruct (ainv_pop val st0 C0 Hne0 _ _ _ _ idx A1 ltac:(lia) Hmi Hnone ltac:(lia) Hv1) as [Hb A2].
    pose proof (reason_exists val st0 C0 Hne0 idx Hb Hidxt) as Hrnz.
    destruct (nth (lvar p) (rsn st0) 0) as [|r'] eqn:Er; [contradiction|].
    destruct (i_rsn _ _ C0 idx p r' Hp' Er) as (c' & Hc' & Hc0 & Hrest).
    cbn [tr_rsn]. replace (S (off (db st0) r') - 1) with (off (db st0) r') by lia.
    eapply IH; [exact R2 | exact Han2 | exact Ha | exact Hc' | | unfold stc2; cbn [fv fset fld_eqb]; exact A2 | | left; lia | | exact HQ].
    + destruct c'; [discriminate | cbn; lia].
    + intros p' Hp''. rewrite Forall_forall in Hrest.
      destruct (Hrest (nth p' c' 0) (in_tl_nth c' p' Hp'')) as [Hf (k' & Hk' & Hpos)].
      split; [exact Hf|]. exists k'. split; [exact Hpos | lia].
    + intros v Hvv. destruct (Hdis v Hvv) as (u & Hu & Hdu). destruct (Nat.eq_dec u (lvar p)) as [-> | Hne].
      * right. pose proof (true_disagree_false v _ _ Hptrue Hdu) as Hneg.
        apply lit_true_lneg in Hneg. assert (C0v : Core (Some v) st0) by (rewrite <- Hvv; exact C0).
        pose proof (Forall_nth_error _ _ _ _ (i_db _ _ C0v) Hc') as Hex.
        destruct c' as [|a' c']; [discriminate|]. cbn in Hc0. injection Hc0 as ->.
        cbn [cholds] in Hex. inversion Hex; subst; [contradiction | cbn; assumption].
      * left. exists u. split; [|exact Hdu]. unfold stc2. cbn [fv fset fld_eqb]. apply marked_lset; [exact Hv1|].
        destruct (Nat.eqb_spec (lvar p) u); [congruence | exact Hu].
Qed.

(** [finish_learnt] clears the marks, permutes the learnt clause's tail
    so that a deepest literal is at position 1, and answers the deepest
    level (0 if none). *)
Lemma finish_learnt_sp : forall m i best bestlv Q mn ma stc,
  R mn ma stc -> an_st st0 stc -> 1 <= i -> i + m = length (lrn stc) ->
  Forall (lit_ok nv) (tl (lrn stc)) ->
  (forall k, 1 <= k < i -> nth (lvar (nth k (lrn stc) 0)) (lvl st0) 0 <= bestlv) ->
  ((best = 0 /\ bestlv = 0) \/ (1 <= best < i /\ nth (lvar (nth best (lrn stc) 0)) (lvl st0) 0 = bestlv)) ->
  (forall u, marked (sn stc) u -> exists k, i <= k < length (lrn stc) /\ lvar (nth k (lrn stc) 0) = u) ->
  (forall r mn' stc', R mn' ma stc' -> an_st st0 stc' -> (forall u, nth u (sn stc') 0 = 0) ->
     (exists a t t', lrn stc = a :: t /\ lrn stc' = a :: t' /\ Permutation t t') ->
     fv stc' FMisc = fv stc FMisc ->
     (forall q, In q (tl (lrn stc)) -> nth (lvar q) (lvl st0) 0 <= r) ->
     (r = 0 \/ exists q, In q (tl (lrn stc)) /\ nth (lvar q) (lvl st0) 0 = r) ->
     Q r (mn', ma)) ->
  safe (finish_learnt s i m best bestlv) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros i best bestlv Q mn ma stc Hr Han Hi Him Hok Hle Hbest Hmarks HQ;
    cbn [finish_learnt].
  - (* move the deepest literal to position 1 *)
    destruct (lrn stc) as [|a0 t] eqn:EL; [cbn in Him; lia|].
    apply safe_seq with (P := fun _ h1 => exists mn1 t', h1 = (mn1, ma) /\
      R mn1 ma (fset stc FLrn (a0 :: t')) /\ Permutation t t').
    + destruct (Nat.ltb_spec 1 best).
      * destruct Hbest as [[-> _] | [Hb _]]; [lia|]. unfold Global.swap_array.
        assert (H1 : nth_error (lrn stc) 1 = Some (nth 1 (lrn stc) 0)) by (apply nth_error_nth'; rewrite EL; cbn in *; lia).
        assert (Hb' : nth_error (lrn stc) best = Some (nth best (lrn stc) 0)) by (apply nth_error_nth'; rewrite EL; cbn in *; lia).
        eapply (rd_fld s nv FLrn 1); [exact Hr | discriminate | exact H1 |].
        eapply (rd_fld s nv FLrn best); [exact Hr | discriminate | exact Hb' |].
        eapply (wr_seq s nv FLrn 1); [exact Hr | unfold seqf; tauto | rewrite EL; cbn in *; lia |]. intros mn1 R1.
        apply safe_unbind.
        eapply (wr_seq s nv FLrn best); [exact R1 | unfold seqf; tauto | cbn [fv fset fld_eqb]; rewrite lset_length, EL; cbn in *; lia |].
        intros mn2 R2. apply safe_ret. rewrite EL in R2. cbn [fv fset fld_eqb] in R2.
        destruct best as [|best]; [lia|]. cbn [nth] in R2.
        exists mn2, (lset (lset t 0 (nth best t 0)) best (nth 0 t 0)). split; [reflexivity|]. split.
        -- eapply repr_sim; [exact R2|]. solve_sim.
        -- apply perm_swap; cbn in *; lia.
      * apply safe_ret. exists mn, t. split; [reflexivity|]. split; [|reflexivity].
        eapply repr_sim; [exact Hr|]. split; [reflexivity | split; [reflexivity|]]. intros []; cbn; auto.
    + intros _ h1 (mn1 & t' & -> & R1 & Hperm). apply safe_ret.
      apply (HQ bestlv mn1 _ R1); [now apply an_lrn_set | | | reflexivity | |].
      * intros u. cbn [fv fset fld_eqb]. destruct (Nat.eq_dec (nth u (sn stc) 0) 0) as [E | E]; [exact E|].
        destruct (Hmarks u E) as (k & Hk & _). cbn in Hk, Him. lia.
      * exists a0, t, t'. split; [reflexivity|]. split; [reflexivity | exact Hperm].
      * intros q Hq. apply In_nth with (d := 0) in Hq as (k & Hk & <-).
        specialize (Hle (S k)). cbn [nth] in Hle. apply Hle. cbn [length tl] in *. lia.
      * destruct Hbest as [[_ ->] | [Hb Hlv]]; [now left|]. right.
        exists (nth best (a0 :: t) 0). split; [apply in_tl_nth; cbn in *; lia | exact Hlv].
  - assert (Hq : nth_error (lrn stc) i = Some (nth i (lrn stc) 0)) by (apply nth_error_nth'; lia).
    set (q := nth i (lrn stc) 0) in *.
    eapply (rd_fld s nv FLrn i q); [exact Hr | discriminate | exact Hq |]. cbv zeta.
    pose proof Han as (E1 & E2 & Ef & Em & Ek & Hs).
    assert (Hv : lvar q < nv).
    { apply lit_ok_var. eapply Forall_forall; [exact Hok|]. apply in_tl_nth. lia. }
    eapply (wr_plain s nv FSn (lvar q) 0); [exact Hr | unfold plain; tauto | discriminate | rewrite (si_sn _ _ Hs); exact Hv |].
    intros mn1 R1.
    eapply (rd_fld s nv FLvl (lvar q) (nth (lvar q) (lvl stc) 0)); [exact R1 | discriminate | cbn [fv fset fld_eqb]; apply nth_error_nth'; rewrite (si_lvl _ _ Hs); exact Hv |].
    cbn [fv fset fld_eqb]. rewrite (Ef FLvl) by discriminate.
    set (stc1 := fset stc FSn (lset (sn stc) (lvar q) 0)) in *.
    assert (Han1 : an_st st0 stc1) by (apply an_mark; auto).
    assert (Hv1 : lvar q < length (sn stc)) by (rewrite (si_sn _ _ Hs); exact Hv).
    assert (Hmarks1 : forall u, marked (sn stc1) u ->
              exists k, i + 1 <= k < length (lrn stc1) /\ lvar (nth k (lrn stc1) 0) = u).
    { intros u Hu. unfold stc1 in Hu |- *. cbn [fv fset fld_eqb] in Hu |- *. apply marked_lset in Hu; [|exact Hv1].
      destruct (Nat.eqb_spec (lvar q) u); [lia|].
      destruct (Hmarks u Hu) as (k & Hk & Ek'). exists k. split; [|exact Ek'].
      destruct (Nat.eq_dec k i) as [-> | ?]; [exfalso; apply n; exact Ek' | lia]. }
    assert (Hfin : forall best' bestlv', ((best' = 0 /\ bestlv' = 0) \/
               (1 <= best' < i + 1 /\ nth (lvar (nth best' (lrn stc) 0)) (lvl st0) 0 = bestlv')) ->
               (forall k, 1 <= k < i + 1 -> nth (lvar (nth k (lrn stc) 0)) (lvl st0) 0 <= bestlv') ->
               safe (finish_learnt s (i + 1) m best' bestlv') Q (mn1, ma)).
    { intros best' bestlv' Hb' Hle'.
      eapply IH; [exact R1 | exact Han1 | lia | unfold stc1; cbn [fv fset fld_eqb]; lia | exact Hok | exact Hle' | exact Hb' | exact Hmarks1 |].
      intros r mn' stc' R' Han' Hz' Hp' Hm1 Hr1 Hr2. apply (HQ r mn' stc' R' Han' Hz' Hp' Hm1 Hr1 Hr2). }
    destruct (Nat.ltb_spec bestlv (nth (lvar q) (lvl st0) 0)).
    + apply Hfin; [right; split; [lia | reflexivity] |].
      intros k Hk. destruct (Nat.eq_dec k i) as [-> | ?]; [unfold q in *; lia|]. specialize (Hle k ltac:(lia)). lia.
    + apply Hfin; [destruct Hbest as [? | [? ?]]; [now left | right; split; [lia | assumption]] |].
      intros k Hk. destruct (Nat.eq_dec k i) as [-> | ?]; [unfold q in *; lia|]. apply Hle. lia.
Qed.

End Analyze.


(** * Learning *)

(** Two states that differ at most in the counters other than the queue
    head. *)
Definition mo (st st' : astate) : Prop :=
  db st' = db st /\ wl st' = wl st /\ (forall f, f <> FMisc -> fv st' f = fv st f) /\
  length (fv st' FMisc) = length (fv st FMisc) /\ qhead st' = qhead st.

(** [Core], [Wch] and the marks ignore the counters. *)
Lemma inv_mo st st' : Inv val st -> mo st st' -> Inv val st'.
Proof.
  intros (C & W & S0) (E1 & E2 & Ef & Em & Eq). split; [|split].
  - apply (core_ext val st st'); auto; apply Ef; discriminate.
  - now rewrite E1, E2.
  - intros v. rewrite Ef by discriminate. apply S0.
Qed.

(** [SI] ignores the counters' values. *)
Lemma si_mo st st' : SI nv st -> mo st st' -> SI nv st'.
Proof.
  intros [[] Hl] (E1 & E2 & Ef & Em & Eq). split.
  - constructor; rewrite ?E1, ?E2, ?Ef by discriminate; auto. congruence.
  - unfold lim_lt in *. rewrite !Ef by discriminate. exact Hl.
Qed.

(** [reserve need] returns the arena and the end of its clauses, with room
    for [need] more cells past it; only the arena capacity changes. *)
Lemma reserve_sp need Q mn ma st :
  R mn ma st ->
  (forall mn' ma' a' ws cs st', rep s nv mn' ma' st' a' ws cs ->
     length (enc (db st)) + need <= length (car cs) -> mo st st' ->
     (forall k, k <> ACAP -> nth k (fv st' FMisc) 0 = nth k (fv st FMisc) 0) ->
     Q (a', length (enc (db st))) (mn', ma')) ->
  safe (reserve s need) Q (mn, ma).
Proof.
  intros Hr HQ. pose proof Hr as (a & ws & cs & C & A). unfold reserve, get, put.
  pose proof (a_alen _ _ _ A) as Ea. pose proof (a_acap _ _ _ A) as Ec. pose proof (a_miscn _ _ _ A) as Em.
  pose proof (pre_length _ _ (a_ar _ _ _ A)) as Hle.
  eapply (rd_ref s nv); [exact Hr |]. intros a0 Ha0. rewrite (ref_rep _ _ _ _ _ _ _ _ _ (conj C A) Ha0).
  eapply (rd_misc s nv ALEN); [exact Hr | unfold ALEN, NMISC; lia |]. rewrite Ea.
  eapply (rd_misc s nv ACAP); [exact Hr | unfold ACAP, NMISC; lia |]. rewrite Ec.
  destruct (Nat.leb_spec (length (enc (db st)) + need) (length (car cs))).
  { apply safe_ret. apply (HQ mn ma a ws cs st (conj C A)); [lia | repeat split | auto]. }
  cbv zeta. set (cap' := Nat.max (2 * length (car cs)) (length (enc (db st)) + need)).
  eapply safe_new_n_bind. set (a' := afresh mn cap'). set (mn1 := anew mn cap' 0).
  pose proof (conc_fresh _ _ _ _ _ _ _ cap' C) as Ho. fold a' in Ho.
  pose proof (conc_anew _ _ _ _ _ _ _ cap' 0 C) as C1. fold mn1 in C1.
  pose proof (arr_anew (V := Solver.Vn) mn cap' 0) as Ha'. fold a' mn1 in Ha'.
  pose proof (conc_arr _ _ _ _ _ _ _ 12 _ C1 eq_refl) as Ha1.
  assert (Hdisj : forall y, In y (cells a') -> ~ In y (cells a)).
  { intros y Hy Hy'. apply (Ho y Hy). eapply in_cells_own; [apply (nth_error_In _ 12); reflexivity | exact Hy']. }
  apply safe_bind. apply (copy_safe a a' (length (enc (db st))) 0 (car cs) (repeat 0 cap') _ mn1 ma Ha1 Ha' Hdisj);
    [lia | rewrite repeat_length; unfold cap'; lia | reflexivity |].
  intros mn2 Hfr Hw2. cbn [Nat.add] in Hw2. cbv beta.
  assert (C2 : conc s nv mn2 ma a ws cs).
  { apply (conc_frame _ _ _ _ _ _ _ _ C1). intros b ys Hb Hy. apply Hfr; [exact Hy|].
    intros y Hy1 Hy2. apply (Ho y Hy1). eapply in_cells_own; [exact Hb | exact Hy2]. }
  set (ys := firstn (length (enc (db st))) (car cs) ++ skipn (length (enc (db st))) (repeat 0 cap')) in *.
  assert (Hys : length ys = cap').
  { unfold ys. rewrite length_app, length_firstn, length_skipn, repeat_length. unfold cap'. lia. }
  assert (Hpre : pre (enc (db st)) ys).
  { unfold ys. destruct (a_ar _ _ _ A) as [pad Hp]. rewrite Hp, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
    exists (skipn (length (enc (db st))) (repeat 0 cap')). reflexivity. }
  eapply safe_write_ref_bind.
  pose proof (conc_arena _ _ _ _ _ _ _ a' ys C2 Hw2 Ho) as C3.
  assert (E8 : cfld (lset cs 12 ys) FMisc = cfld cs FMisc) by (apply nth_lset_ne; cbn; lia).
  pose proof (rep_fld s nv _ _ _ _ _ FMisc C3) as Hm3. rewrite E8 in Hm3.
  assert (Hac : ACAP < length (cfld cs FMisc)) by (rewrite (a_fld _ _ _ A FMisc) by (unfold plain; tauto); rewrite Em; unfold ACAP, NMISC; lia).
  eapply safe_write_n_bind; [exact Hm3 | exact Hac |]. apply safe_ret.
  pose proof (conc_awrite _ _ _ _ _ _ _ (fidx FMisc) _ ACAP cap' C3 (own_fld s a' ws FMisc)) as C4.
  rewrite E8 in C4. specialize (C4 Hac).
  pose proof (abs_newar _ _ _ ys A Hpre) as A4. rewrite Hys in A4.
  apply (HQ _ _ a' ws _ _ (conj C4 A4)).
  - rewrite nth_lset_ne by (cbn; lia). rewrite nth_lset_eq by (rewrite (a_len _ _ _ A); lia). unfold cap'. lia.
  - split; [reflexivity | split; [reflexivity | split]].
    + intros f Hf. cbn [fv fset]. destruct (fld_eqb f FMisc) eqn:E; [apply fld_eqb_eq in E; contradiction | reflexivity].
    + cbn [fv fset fld_eqb]. split; [apply lset_length|]. apply nth_lset_ne. unfold QHEAD, ACAP. lia.
  - intros k Hk. cbn [fv fset fld_eqb]. now apply nth_lset_ne.
Qed.

(** [store_learnt a x i m] copies the learnt clause from position [i] into
    the arena [a] after the clauses' end [x] and a length cell. *)
Lemma store_learnt_sp : forall m i Q mn ma st a ws cs P y,
  rep s nv mn ma st a ws cs -> car cs = enc (db st) ++ (y :: firstn i (lrn st)) ++ P ->
  i + m = length (lrn st) -> m <= length P ->
  (forall mn' cs' P', rep s nv mn' ma st a ws cs' -> car cs' = enc (db st) ++ (y :: lrn st) ++ P' -> Q tt (mn', ma)) ->
  safe (store_learnt s a (length (enc (db st))) i m) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros i Q mn ma st a ws cs P y [C A] Hc Him HP HQ; cbn [store_learnt].
  - apply safe_ret. apply (HQ mn cs P (conj C A)). rewrite Hc, firstn_all2 by lia. reflexivity.
  - assert (Hq : nth_error (lrn st) i = Some (nth i (lrn st) 0)) by (apply nth_error_nth'; lia).
    eapply (rd_fld s nv FLrn i); [exact (repr_of _ _ _ _ _ _ _ _ C A) | discriminate | exact Hq |].
    destruct P as [|p0 P0]; [cbn in HP; lia|].
    assert (Hi : length (enc (db st)) + 1 + i < length (car cs)).
    { rewrite Hc, !length_app. cbn [length]. rewrite length_firstn. lia. }
    eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 12 _ C eq_refl) | exact Hi |].
    eapply IH.
    + split; [apply (conc_awrite s nv mn ma a ws cs 12 _ _ _ C); [reflexivity | exact Hi]|].
      apply abs_arpad; [exact A | lia].
    + rewrite nth_lset_eq by (rewrite (a_len _ _ _ A); lia). rewrite Hc.
      rewrite lset_app_r by lia. replace (length (enc (db st)) + 1 + i - length (enc (db st))) with (S i) by lia.
      cbn [app lset]. rewrite lset_consS. rewrite lset_app_r by (rewrite length_firstn; lia).
      rewrite length_firstn. replace (i - Nat.min i (length (lrn st))) with 0 by lia. rewrite lset_cons0.
      rewrite Nat.add_1_r, (firstn_S_snoc _ _ _ Hq), <- app_assoc. reflexivity.
    + lia.
    + cbn in HP. lia.
    + exact HQ.
Qed.


(** A literal true under the valuation, if any, holds. *)
Lemma holds_opt l : opt (fun v => lit_true v l) -> holds val l.
Proof. unfold opt, holds. destruct val as [v|]; auto. Qed.

(** A clause true under the valuation, if any, holds. *)
Lemma cholds_opt c : opt (fun v => Exists (lit_true v) c) -> cholds val c.
Proof. unfold opt, cholds. destruct val as [v|]; auto. Qed.

(** A false literal's negation is on the trail, so it is below [2 * nv]. *)
Lemma false_lit_ok st q : Core val st -> SIc nv st -> lval (asg st) q = 2 -> lit_ok nv q.
Proof.
  intros C Hs Hq. destruct (false_trail val st C q Hq) as (k & Hk). apply lit_ok_lneg. eapply tr_lit; eauto.
Qed.

(** [learn fuel x] turns the conflict at clause [ci] (offset [x]) into a
    learnt clause, backjumps and asserts the UIP, keeping [Inv] and [SI]:
    the valuation, if any, satisfies the learnt clause. *)
Lemma learn_sp fuel ci Q mn ma st :
  R mn ma st -> SI nv st -> Inv val st -> conflict st (S ci) -> lim st <> [] ->
  (forall mn' ma' st', R mn' ma' st' -> SI nv st' -> Inv val st' -> Q tt (mn', ma')) ->
  safe (learn s fuel (off (db st) ci)) Q (mn, ma).
Proof.
  intros Hr HS (C & W & S0) Hconf Hne HQ. unfold learn, decision_level, get, put.
  destruct Hconf as (ci' & cl & Eci & Hd & Hfalse & Hcur). injection Eci as <-.
  destruct (repr_counts _ _ _ _ _ Hr) as (Etl & Etll & Ell & Eal & Hmisc & Hwll).
  assert (Hasg : forall u, nth u (asg st) 0 <= 2) by apply (i_asg _ _ C).
  eapply (rd_misc s nv TLLEN); [exact Hr | unfold TLLEN, NMISC; lia |]. rewrite Etll.
  eapply (rd_misc s nv CONFLICTS); [exact Hr | unfold CONFLICTS, NMISC; lia |].
  eapply (wr_len s nv FLrn 1); [exact Hr | unfold seqf; tauto | cbn; lia |].
  intros mn0 C0l Hpre0 Hlen0 R0. cbn [slot capf] in R0, Hlen0.
  destruct C0l as [|x0 C0l]; [cbn in Hlen0; lia|]. cbn [firstn] in R0.
  set (now := nth CONFLICTS (fv st FMisc) 0).
  set (st0 := fset (fset st FMisc (lset (fv st FMisc) LLEN 1)) FLrn [x0]) in *.
  assert (Hq0 : qhead st0 = qhead st) by (unfold st0; cbn [fv fset fld_eqb]; apply nth_lset_ne; unfold QHEAD, LLEN; lia).
  assert (C0 : Core val st0) by (apply (core_ext val st st0); auto).
  assert (S0c : SIc nv st0) by (unfold st0; apply sic_lrn, sic_lset; [apply HS | tauto]).
  assert (Hne0 : lim st0 <> []) by exact Hne.
  eapply (rd_misc s nv TLEN); [exact R0 | unfold TLEN, NMISC; lia |].
  replace (nth TLEN (fv st0 FMisc) 0) with (length (tr st))
    by (unfold st0; cbn [fv fset fld_eqb]; rewrite nth_lset_ne by (unfold TLEN, LLEN; lia); auto).
  eapply (rd_ref s nv); [exact R0 |]. intros a Ha.
  (* the conflict clause has a literal at the current level, so the trail is not empty *)
  destruct (proj1 (Exists_exists _ _) Hcur) as (q0 & Hq0' & (k0 & Hk0 & Hk0lim)).
  assert (Htr : tr st <> []) by (intros E; apply at_pos_lt in Hk0; rewrite E in Hk0; cbn in Hk0; lia).
  apply safe_bind.
  eapply (analyze_loop_sp st0 a now C0 Hne0 S0c fuel ci cl 0 (length (tr st) - 1) 0 _ mn0 ma st0);
    [exact R0 | now apply an_refl | exact Ha | exact Hd | lia | | | | |].
  { apply (ainv_head _ _ 0). apply (ainv_init st0); [exact Htr | exact S0]. }
  { intros p Hp. rewrite Forall_forall in Hfalse. pose proof (Hfalse _ (nth_In cl 0 (proj2 Hp))) as Hf.
    split; [exact Hf|]. destruct (false_at_pos val st C _ Hf) as (k & Hk). exists k. split; [exact Hk|].
    pose proof (at_pos_lt _ _ _ Hk). lia. }
  { right. apply In_nth with (d := 0) in Hq0' as (p & Hp & Ep). exists p, k0. split; [lia|].
    rewrite Ep. split; [exact Hk0|]. rewrite Forall_forall in Hk0lim. apply Hk0lim, base_in, Hne. }
  { intros v Hv. right. rewrite skipn_O. pose proof (i_db _ _ C) as D. rewrite Hv in D.
    exact (Forall_nth_error _ _ _ _ D Hd). }
  intros p mn2 stc2 R2 Han2 (idx & Hidx & Hbidx) Hmarks2 Hne2 Hlr2 Hsound2. cbv beta zeta. change (nth_error (tr st) idx = Some p) in Hidx. change (base st <= idx) in Hbidx.
  destruct (lrn stc2) as [|x2 t] eqn:EL2; [congruence|]. cbn [tl] in Hmarks2, Hlr2, Hsound2.
  assert (Hpok : lit_ok nv p) by exact (tr_lit nv st idx p (proj1 HS) Hidx).
  eapply (wr_seq s nv FLrn 0 (lneg p)); [exact R2 | unfold seqf; tauto | rewrite EL2; cbn; lia |].
  intros mn3 R3. rewrite EL2 in R3. rewrite lset_cons0 in R3.
  set (stc3 := fset stc2 FLrn (lneg p :: t)) in *.
  assert (Han3 : an_st st0 stc3) by (now apply an_lrn_set).
  destruct (repr_counts _ _ _ _ _ R3) as (_ & _ & Ell3 & _).
  eapply (rd_misc s nv LLEN); [exact R3 | unfold LLEN, NMISC; lia |]. rewrite Ell3.
  replace (length (lrn stc3)) with (S (length t)) by reflexivity.
  assert (Htok : Forall (lit_ok nv) t).
  { eapply Forall_impl; [|exact Hlr2]. intros q (Hq & _). exact (false_lit_ok st q C (proj1 HS) Hq). }
  replace (S (length t) - 1) with (length t) by lia.
  apply safe_bind. eapply (finish_learnt_sp st0 (length t) 1 0 0 _ mn3 ma stc3);
    [exact R3 | exact Han3 | lia | reflexivity | exact Htok | intros; lia | now left | |].
  { intros u Hu. destruct (Hmarks2 u Hu) as (q & Hq & <-). apply In_nth with (d := 0) in Hq as (k & Hk & <-).
    exists (S k). cbn. split; [lia | reflexivity]. }
  intros bt mn4 stc4 R4 Han4 Hz4 (a' & t0 & t' & Ea & ELr4 & Hperm) Hm4 Hbt_le Hbt. cbv beta.
  injection Ea as <- <-. cbn [tl] in Hbt_le, Hbt.
  pose proof Han4 as (G1 & G2 & Gf & Gm & Gk & Gs).
  assert (Hlvl : forall q, In q t -> 0 < nth (lvar q) (lvl st) 0 < length (lim st)).
  { intros q Hq. rewrite Forall_forall in Hlr2. apply Hlr2, Hq. }
  assert (Hbt_lt : bt < length (lim st)).
  { destruct Hbt as [-> | (q & Hq & <-)]; [destruct (lim st); [congruence | cbn; lia] | now apply Hlvl]. }
  assert (I4 : Inv val stc4) by (split; [exact (an_core st0 stc4 C0 Han4) | split; [rewrite G1, G2; exact W | exact Hz4]]).
  assert (S4 : SI nv stc4) by (split; [exact Gs | unfold lim_lt; rewrite !Gf by discriminate; apply HS]).
  apply safe_bind. eapply (backtrack_sp bt); [exact R4 | exact S4 | exact I4 |].
  intros mn5 st5 R5 S5 I5 Hk5 Hbtr. cbv beta.
  rewrite (Gf FLim) in Hbtr by discriminate. specialize (Hbtr Hbt_lt).
  destruct Hbtr as (Edb & Az & Ak & Elv & Rk & Etr & Elim & Eq).
  rewrite (Gf FTr) in Az, Ak, Rk, Etr by discriminate. rewrite (Gf FLim) in Az, Ak, Rk, Etr, Elim by discriminate. rewrite (Gf FAsg) in Ak by discriminate. change (fv st0 FLim) with (lim st) in *. change (fv st0 FTr) with (tr st) in *. change (fv st0 FAsg) with (asg st) in *. change (fv st0 FLvl) with (lvl st) in *.
  set (m := nth bt (lim st) 0) in *.
  destruct Hk5 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
  assert (Hlr5 : lrn st5 = lneg p :: t') by (rewrite K6; exact ELr4).
  (* the learnt literals stay false, the UIP becomes unassigned *)
  assert (Hlow : forall q, In q t -> lval (asg st5) q = 2).
  { intros q Hq. pose proof (proj1 (Forall_forall _ _) Hlr2 q Hq) as (Hqf & _).
    destruct (false_at_pos val st C q Hqf) as (k & Hk).
    assert (Hkm : k < m).
    { apply (count_le_lt_iff (lim st) bt k (i_sorted _ _ C) Hbt_lt). rewrite <- (lvl_at val st C k (lvar q) Hk).
      now apply Hbt_le. }
    rewrite lval_ext with (A := asg st); [exact Hqf|]. apply Ak.
    eapply at_pos_not_skipn; eauto. apply (i_nd _ _ C). }
  assert (Hlow' : Forall (fun q => lval (asg st5) q = 2) t').
  { apply Forall_forall. intros q Hq. apply Hlow. eapply Permutation_in; [symmetry; exact Hperm | exact Hq]. }
  assert (Huip : lval (asg st5) (lneg p) = 0).
  { apply lval_zero; [apply (i_asg _ _ (proj1 I5))|]. rewrite lvar_lneg. apply Az.
    assert (Hidxm : m <= idx).
    { destruct (Nat.leb_spec m idx) as [|Hlt]; [assumption|]. exfalso.
      apply (count_le_lt_iff (lim st) bt idx (i_sorted _ _ C) Hbt_lt) in Hlt.
      pose proof (proj2 (cur_iff val st C Hne idx) Hbidx). lia. }
    apply in_map_iff. exists p. split; [reflexivity|].
    rewrite <- (firstn_skipn m (tr st)) in Hidx. rewrite nth_error_app2 in Hidx.
    - eapply nth_error_In. exact Hidx.
    - rewrite length_firstn. lia. }
  assert (Hlim5 : length (lim st5) = bt) by (rewrite Elim, length_firstn; lia).
  assert (Hsat : opt (fun v => Exists (lit_true v) (lneg p :: t'))).
  { intros v Hv. destruct (Hsound2 v Hv) as [Ht | Hex]; [now left | right].
    apply Exists_exists in Hex as (q & Hq & Ht). apply Exists_exists. exists q. split; [|exact Ht].
    eapply Permutation_in; [exact Hperm | exact Hq]. }
  assert (Huok : lit_ok nv (lneg p)) by (apply lit_ok_lneg; exact Hpok).
  destruct (Nat.eqb_spec (S (length t)) 1) as [Hl1 | Hl1].
  - (* a unit clause: learnt at level 0 *)
    assert (t = []) as -> by (destruct t; [reflexivity | cbn in Hl1; lia]).
    assert (bt = 0) as Hbt0 by (destruct Hbt as [-> | (q & [] & _)]; reflexivity).
    eapply (enqueue_sp (lneg p) 0); [exact R5 | apply S5 | apply I5 | exact Huok | exact Huip | reflexivity |].
    intros mn6 R6. apply (HQ _ _ _ R6).
    + apply si_enqA; [exact S5 | exact Huok | lia].
    + apply enqA_wch; [exact I5|]. apply (core_enqA nv); [apply I5 | apply S5 | exact Huok | exact Huip | | intros; lia |].
      * intros _. left. rewrite Elim, Hbt0. constructor.
      * intros _. apply holds_opt. intros v Hv. destruct (Hsound2 v Hv) as [Ht | Hex]; [exact Ht | inversion Hex].
  - (* store and watch the clause, then propagate the UIP from it *)
    assert (Ht' : t' <> []) by (intros ->; apply Permutation_sym, Permutation_nil in Hperm; subst t; cbn in Hl1; lia).
    assert (Hbt1 : 1 <= bt).
    { destruct t as [|q t]; [cbn in Hl1; lia|].
      pose proof (Hbt_le q (or_introl eq_refl)). pose proof (Hlvl q (or_introl eq_refl)). lia. }
    assert (Hlen' : length t' = length t) by (symmetry; apply Permutation_length; exact Hperm).
    set (cl' := lneg p :: t') in *.
    apply safe_bind. eapply (reserve_sp (1 + S (length t))); [exact R5 |].
    intros mn6 ma6 a6 ws cs st6 [C6 A6] Hroom (E61 & E62 & E6f & E6m & E6q) E6k. cbv beta iota.
    assert (I6 : Inv val st6) by (apply (inv_mo st5); [exact I5 | repeat split; auto]).
    assert (S6 : SI nv st6) by (apply (si_mo st5); [exact S5 | repeat split; auto]).
    assert (Hlr6 : lrn st6 = cl') by (rewrite E6f by discriminate; exact Hlr5).
    destruct (a_ar _ _ _ A6) as [pad Hpad].
    rewrite <- E61 in Hroom |- *.
    assert (Hco : length (enc (db st6)) < length (car cs)) by lia.
    eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 12 _ C6 eq_refl) | exact Hco |].
    pose proof (conc_awrite s nv _ _ _ _ _ 12 _ _ (S (length t)) C6 eq_refl Hco) as C7.
    pose proof (abs_arpad _ _ _ (length (enc (db st6))) (S (length t)) A6 ltac:(lia)) as A7.
    destruct pad as [|p0 pad]; [rewrite Hpad, length_app in Hroom; cbn in Hroom; lia|].
    apply safe_bind. eapply (store_learnt_sp (S (length t)) 0 _ _ _ st6 a6 ws _ pad (S (length t)) (conj C7 A7)).
    { rewrite nth_lset_eq by (rewrite (a_len _ _ _ A6); lia). rewrite Hpad, lset_app_r, Nat.sub_diag by lia.
      rewrite lset_cons0. reflexivity. }
    { rewrite Hlr6. cbn. lia. }
    { rewrite Hpad, length_app in Hroom. cbn in Hroom. lia. }
    intros mn8 cs8 P8 [C8 A8] Hc8. cbv beta.
    rewrite Hlr6 in Hc8. replace (S (length t)) with (length cl') in Hc8 by (cbn; lia).
    pose proof (rep_fld s nv _ _ _ _ _ FMisc C8) as Hm8.
    assert (Hal : ALEN < length (cfld cs8 FMisc))
      by (rewrite (a_fld _ _ _ A8 FMisc), (a_miscn _ _ _ A8) by (unfold plain; tauto); unfold ALEN, NMISC; lia).
    replace (length (enc (db st6)) + 1 + S (length t)) with (length (enc (db st6)) + S (length cl'))
      by (cbn; lia).
    eapply safe_write_n_bind; [exact Hm8 | exact Hal |].
    pose proof (conc_awrite s nv _ _ _ _ _ (fidx FMisc) _ ALEN (length (enc (db st6)) + S (length cl')) C8 (own_fld _ _ _ FMisc) Hal) as C9.
    assert (Hrb : Forall (fun r => r <= length (db st6)) (rsn st6)) by apply (si_r _ _ (proj1 S6)).
    assert (Hwb : Forall (Forall (fun ci => ci < length (db st6))) (wl st6)).
    { eapply Forall_impl; [|apply (si_w _ _ (proj1 S6))]. intros L HL. eapply Forall_impl; [|exact HL].
      intros c (c' & Hc' & _). apply nth_error_Some. congruence. }
    pose proof (abs_cpush _ _ _ cl' P8 A8 Hrb Hwb Hc8) as A9.
    rewrite (a_fld _ _ _ A8 FMisc) in C9 by (unfold plain; tauto).
    set (st7 := fset (cpush st6 cl') FMisc (lset (fv st6 FMisc) ALEN (length (enc (db st6)) + S (length cl')))) in *.
    rewrite (a_fld _ _ _ A8 FMisc) in A9 by (unfold plain; tauto).
    assert (R7 : R _ ma6 st7) by (eapply repr_of; [exact C9 | exact A9]).
    assert (Hd7 : nth_error (db st7) (length (db st6)) = Some cl').
    { unfold st7. cbn [db fset cpush]. now rewrite nth_error_app2, Nat.sub_diag by lia. }
    assert (Hcl'ok : Forall (lit_ok nv) cl').
    { constructor; [exact Huok|]. apply Forall_forall. intros q Hq. apply (false_lit_ok st q C (proj1 HS)).
      apply (proj1 (Forall_forall _ _) Hlr2). eapply Permutation_in; [symmetry; exact Hperm | exact Hq]. }
    assert (S7 : SIc nv st7) by (exact (sic_lset nv (cpush st6 cl') FMisc ALEN _ (sic_cpush nv st6 cl' (proj1 S6) Hcl'ok) ltac:(tauto))).
    assert (C7c : Core val st7).
    { unfold st7. apply core_fset_misc; [apply core_cpush; [apply I6 | apply cholds_opt, Hsat]|].
      cbn [fv fset fld_eqb cpush]. rewrite nth_lset_ne by (unfold QHEAD, ALEN; lia). pose proof (i_qtr _ _ (proj1 I6)). lia. }
    apply safe_bind. eapply (attach_sp a6 (length (db st6)) cl'); [exact R7 | exact S7 | apply (c_ref _ _ _ _ _ _ _ C6) | exact Hd7 | unfold cl'; destruct t'; [congruence | cbn; lia] | | | |].
    { unfold st7. cbn [db fset cpush]. symmetry. apply off_snoc. }
    { unfold st7. cbn [db wl fset cpush]. apply wch_snoc, (proj1 (proj2 I6)). }
    { intros l Hl. unfold st7. cbn [db wl fset cpush] in Hl |- *. apply (wch_fresh _ _ l (proj1 (proj2 I6))). exact Hl. }
    intros mn10 ma10 st8 R8 S8 Edb8 Efv8 W8 Ha8. cbv beta.
    assert (C8c : Core val st8) by (apply (core_ext val st7 st8); rewrite ?Edb8, ?Efv8; auto).
    assert (Ha8' : lval (asg st8) (lneg p) = 0).
    { rewrite Efv8. unfold st7. cbn [fv fset fld_eqb cpush]. rewrite E6f by discriminate. exact Huip. }
    assert (Hlim8 : lim st8 = lim st5) by (rewrite Efv8; unfold st7; cbn [fv fset fld_eqb cpush]; apply E6f; discriminate).
    assert (Htr8 : tr st8 = tr st5) by (rewrite Efv8; unfold st7; cbn [fv fset fld_eqb cpush]; apply E6f; discriminate).
    assert (SI8 : SI nv st8) by (split; [exact S8 | unfold lim_lt; rewrite Hlim8, Htr8; apply S5]).
    eapply (enqueue_sp (lneg p) (S (length (db st6)))); [exact R8 | exact S8 | exact C8c | exact Huok | exact Ha8' | |].
    { rewrite Edb8. unfold st7. cbn [db fset cpush tr_rsn]. rewrite off_snoc. lia. }
    intros mn11 R11. apply (HQ _ _ _ R11).
    + apply si_enqA; [exact SI8 | exact Huok | rewrite Edb8; unfold st7; cbn [db fset cpush]; rewrite length_app; cbn; lia].
    + apply enqA_wch.
      * split; [exact C8c | split; [exact W8|]]. intros v. rewrite Efv8. unfold st7. cbn [fv fset fld_eqb cpush].
        rewrite E6f by discriminate. apply (proj2 (proj2 I5)).
      * apply (core_enqA nv); [exact C8c | exact S8 | exact Huok | exact Ha8' | intros; lia | |].
        -- intros ci'' E. assert (ci'' = length (db st6)) as -> by lia. exists cl'.
           rewrite Edb8. split; [exact Hd7|]. split; [reflexivity|]. cbn [tl cl']. rewrite Efv8.
           unfold st7. cbn [fv fset fld_eqb cpush]. rewrite E6f by discriminate. exact Hlow'.
        -- intros H0. rewrite Hlim8, Hlim5 in H0. lia.
Qed.


(** * Search *)

(** [pick v m best bs] answers 0 or one plus an unassigned variable. *)
Lemma pick_sp : forall m v best bs Q mn ma st,
  R mn ma st -> SIc nv st -> v + m <= nv ->
  (best = 0 \/ (best - 1 < nv /\ nth (best - 1) (asg st) 0 = 0)) ->
  (forall r, (r = 0 \/ (r - 1 < nv /\ nth (r - 1) (asg st) 0 = 0)) -> Q r (mn, ma)) ->
  safe (pick s v m best bs) Q (mn, ma).
Proof.
  induction m as [|m IH]; intros v best bs Q mn ma st Hr Hs Hvm Hb HQ; cbn [pick].
  { apply safe_ret, HQ, Hb. }
  eapply (rd_fld s nv FAsg v (nth v (asg st) 0)); [exact Hr | discriminate | apply nth_error_nth'; rewrite (si_asg _ _ Hs); lia |].
  destruct (Nat.eqb_spec (nth v (asg st) 0) 0) as [E | E].
  - eapply (rd_fld s nv FSt v (nth v (fv st FSt) 0)); [exact Hr | discriminate | apply nth_error_nth'; rewrite (si_st _ _ Hs); lia |].
    destruct (Nat.eqb best 0 || Nat.ltb bs (nth v (fv st FSt) 0)).
    + eapply IH; [exact Hr | exact Hs | lia | right; replace (v + 1 - 1) with v by lia; split; [lia | exact E] | exact HQ].
    + eapply IH; [exact Hr | exact Hs | lia | exact Hb | exact HQ].
  - eapply IH; [exact Hr | exact Hs | lia | exact Hb | exact HQ].
Qed.

(** [decide v] opens a decision level and assigns the unassigned variable
    [v], once propagation is done. *)
Lemma decide_sp v Q mn ma st :
  R mn ma st -> SI nv st -> Inv val st -> v < nv -> nth v (asg st) 0 = 0 -> qhead st = length (tr st) ->
  (forall mn' st', R mn' ma st' -> SI nv st' -> Inv val st' -> Q tt (mn', ma)) ->
  safe (decide s v) Q (mn, ma).
Proof.
  intros Hr HS (C & W & S0) Hv Ha Hq HQ. unfold decide, get, put.
  destruct (repr_counts _ _ _ _ _ Hr) as (Etl & Etll & _ & _ & Hmisc & _).
  eapply (rd_fld s nv FPh v (nth v (fv st FPh) 0)); [exact Hr | discriminate | apply nth_error_nth'; rewrite (si_ph _ _ (proj1 HS)); lia |].
  eapply (rd_misc s nv TLEN); [exact Hr | unfold TLEN, NMISC; lia |]. rewrite Etl.
  eapply (rd_misc s nv TLLEN); [exact Hr | unfold TLLEN, NMISC; lia |]. rewrite Etll.
  set (l := lit_of v (nth v (fv st FPh) 0)).
  assert (Hlv : lvar l = v) by apply lvar_lit_of.
  assert (Hl0 : lval (asg st) l = 0) by (apply lval_zero; [apply (i_asg _ _ C) | now rewrite Hlv]).
  assert (Hlok : lit_ok nv l) by (apply lit_ok_var; lia).
  eapply (wr_push s nv FLim (length (tr st))); [exact Hr | unfold seqf; tauto | |].
  { cbn [capf]. apply (lim_room nv val st l C HS); [lia | exact Hl0]. }
  intros mn1 R1. cbn [slot] in R1.
  set (st1 := fset (fset st FMisc (lset (fv st FMisc) TLLEN (length (lim st) + 1))) FLim (lim st ++ [length (tr st)])) in *.
  assert (C1 : Core val st1).
  { pose proof (core_decide val st C Hq) as X. apply (core_fset_misc _ _ (lset (fv st FMisc) TLLEN (length (lim st) + 1))) in X.
    - eapply core_ext; [| | | | | | | exact X]; reflexivity.
    - cbn [fv fset fld_eqb]. rewrite nth_lset_ne by (unfold QHEAD, TLLEN; lia). pose proof (i_qtr _ _ C). lia. }
  assert (S1 : SIc nv st1).
  { unfold st1. apply sic_lim; [apply sic_lset; [apply HS | tauto]|]. cbn [fv fset fld_eqb].
    apply incr_snoc; [apply (si_inc _ _ (proj1 HS)) | apply (proj2 HS)]. }
  eapply (enqueue_sp l 0 0); [exact R1 | exact S1 | exact C1 | exact Hlok | exact Hl0 | reflexivity |].
  intros mn2 R2. apply (HQ _ _ R2).
  - split.
    + exact (sic_lset nv (enq st1 l 0) FMisc TLEN _ (enq_sic nv st1 l 0 S1 Hlok ltac:(lia)) ltac:(tauto)).
    + apply lim_lt_enq. unfold st1. cbn [fv fset fld_eqb]. apply Forall_app. split; [|constructor; auto].
      eapply Forall_impl; [|apply (proj2 HS)]. cbn. lia.
  - apply enqA_wch; [split; [exact C1 | split; [exact W | exact S0]]|].
    apply (core_enqA nv); [exact C1 | exact S1 | exact Hlok | exact Hl0 | | intros; lia |].
    + intros _. right. unfold st1. cbn [fv fset fld_eqb]. apply in_or_app. right. now left.
    + unfold st1. cbn [fv fset fld_eqb]. rewrite length_app. cbn. lia.
Qed.

(** [restart_tick] counts a conflict and may restart, keeping [Inv] and [SI]. *)
Lemma restart_tick_sp Q mn ma st :
  R mn ma st -> SI nv st -> Inv val st ->
  (forall mn' st', R mn' ma st' -> SI nv st' -> Inv val st' -> Q tt (mn', ma)) ->
  safe (restart_tick s) Q (mn, ma).
Proof.
  intros Hr HS I HQ. unfold restart_tick, get, put.
  destruct (repr_counts _ _ _ _ _ Hr) as (_ & _ & _ & _ & Hmisc & _).
  assert (Hk : forall i, i = RCOUNT \/ i = RLIMIT -> kept i /\ i <> QHEAD /\ i < length (fv st FMisc)).
  { intros i Hi. rewrite Hmisc. unfold kept, RCOUNT, RLIMIT, QHEAD, TLEN, TLLEN, LLEN, ALEN, ACAP, NMISC in *. lia. }
  assert (Hmo : forall st' i x, i = RCOUNT \/ i = RLIMIT -> SI nv st' -> Inv val st' ->
            SI nv (fset st' FMisc (lset (fv st' FMisc) i x)) /\ Inv val (fset st' FMisc (lset (fv st' FMisc) i x))).
  { intros st' i x Hi HS' I'. split.
    - split; [apply sic_lset; [apply HS' | tauto] | apply HS'].
    - apply inv_misc_other; [unfold RCOUNT, RLIMIT, QHEAD in *; lia | exact I']. }
  eapply (rd_misc s nv RCOUNT); [exact Hr | unfold RCOUNT, NMISC; lia |].
  eapply (rd_misc s nv RLIMIT); [exact Hr | unfold RLIMIT, NMISC; lia |].
  destruct (Nat.leb (nth RLIMIT (fv st FMisc) 0) (nth RCOUNT (fv st FMisc) 0 + 1)).
  - destruct (Hk RCOUNT (or_introl eq_refl)) as (Hk1 & _ & Hl1).
    eapply (wr_plain s nv FMisc RCOUNT 0); [exact Hr | unfold plain; tauto | auto | exact Hl1 |]. intros mn1 R1.
    destruct (Hmo st RCOUNT 0 (or_introl eq_refl) HS I) as [S1 I1].
    eapply (wr_plain s nv FMisc RLIMIT); [exact R1 | unfold plain; tauto | intros _; apply Hk; auto | cbn [fv fset fld_eqb]; rewrite lset_length; apply Hk; auto |].
    intros mn2 R2. destruct (Hmo _ RLIMIT (nth RLIMIT (fv st FMisc) 0 + nth RLIMIT (fv st FMisc) 0 / 2) (or_intror eq_refl) S1 I1) as [S2 I2].
    eapply (backtrack_sp 0); [exact R2 | exact S2 | exact I2 |].
    intros mn3 st3 R3 S3 I3 _ _. exact (HQ _ _ R3 S3 I3).
  - destruct (Hk RCOUNT (or_introl eq_refl)) as (Hk1 & _ & Hl1). apply safe_unbind.
    eapply (wr_plain s nv FMisc RCOUNT); [exact Hr | unfold plain; tauto | auto | exact Hl1 |]. intros mn1 R1.
    apply safe_ret. destruct (Hmo st RCOUNT (nth RCOUNT (fv st FMisc) 0 + 1) (or_introl eq_refl) HS I) as [S1 I1].
    exact (HQ _ _ R1 S1 I1).
Qed.

(** [search] keeps [Inv] and [SI], and answers 0 only when there is no
    valuation: 0 means a conflict at level 0. *)
Lemma search_sp fuel : forall budget Q mn ma st,
  R mn ma st -> SI nv st -> Inv val st ->
  (forall r mn' ma' st', R mn' ma' st' -> SI nv st' -> Inv val st' -> r <= 2 -> (r = 0 -> opt (fun _ => False)) ->
     Q r (mn', ma')) ->
  safe (search s fuel budget nv) Q (mn, ma).
Proof.
  induction budget as [|b IH]; intros Q mn ma st Hr HS I HQ; cbn [search].
  { apply safe_ret. apply (HQ 2 mn ma st Hr HS I); [lia | discriminate]. }
  apply safe_bind. eapply (propagate_sp fuel); [exact Hr | exact HS | exact I |].
  intros confl mn1 ma1 st1 R1 S1 I1 Hq1 Hc1. cbv beta.
  destruct (Nat.eqb_spec confl 0) as [-> | Hne].
  - apply safe_bind. eapply (pick_sp nv 0 0 0); [exact R1 | apply S1 | lia | now left |].
    intros v1 Hv1. cbv beta.
    destruct (Nat.eqb_spec v1 0) as [-> | Hv0].
    + apply safe_ret. apply (HQ 1 mn1 ma1 st1 R1 S1 I1); [lia | discriminate].
    + destruct Hv1 as [? | [Hvl Hva]]; [lia|].
      apply safe_bind. eapply (decide_sp (v1 - 1)); [exact R1 | exact S1 | exact I1 | exact Hvl | exact Hva | |].
      { pose proof (i_qtr _ _ (proj1 I1)). specialize (Hq1 eq_refl). lia. }
      intros mn2 st2 R2 S2 I2. eapply IH; [exact R2 | exact S2 | exact I2 | exact HQ].
  - destruct Hc1 as [? | (ci & -> & Hconf)]; [lia|].
    unfold decision_level, get, put. destruct (repr_counts _ _ _ _ _ R1) as (_ & Etll & _ & _ & Hmisc & _).
    eapply (rd_misc s nv TLLEN); [exact R1 | unfold TLLEN, NMISC; lia |]. rewrite Etll.
    destruct (Nat.eqb_spec (length (lim st1)) 0) as [E0 | E0].
    + apply safe_ret. apply (HQ 0 mn1 ma1 st1 R1 S1 I1); [lia|]. intros _ v Hv.
      destruct Hconf as (ci' & cl & Eci & Hd & Hfalse & _).
      pose proof (proj1 I1) as C1. rewrite Hv in C1.
      apply (no_false_clause_l0 v st1 C1 cl E0); [eapply nth_error_In; eauto | exact Hfalse].
    + eapply (rd_misc s nv CONFLICTS); [exact R1 | unfold CONFLICTS, NMISC; lia |].
      eapply (wr_plain s nv FMisc CONFLICTS); [exact R1 | unfold plain; tauto | intros _; unfold kept, CONFLICTS, TLEN, TLLEN, LLEN, ALEN, ACAP; lia | rewrite Hmisc; unfold CONFLICTS, NMISC; lia |].
      intros mn2 R2.
      set (st2 := fset st1 FMisc (lset (fv st1 FMisc) CONFLICTS (nth CONFLICTS (fv st1 FMisc) 0 + 1))) in *.
      assert (S2 : SI nv st2) by (split; [apply sic_lset; [apply S1 | tauto] | apply S1]).
      assert (I2 : Inv val st2) by (apply inv_misc_other; [unfold CONFLICTS, QHEAD; lia | exact I1]).
      replace (S (off (db st1) ci) - 1) with (off (db st2) ci) by (cbn; lia).
      apply safe_bind. eapply (learn_sp fuel ci); [exact R2 | exact S2 | exact I2 | exact Hconf | intros E; apply E0; change (lim st2) with (lim st1) in E; rewrite E; reflexivity |].
      intros mn3 ma3 st3 R3 S3 I3. cbv beta.
      apply safe_bind. eapply restart_tick_sp; [exact R3 | exact S3 | exact I3 |].
      intros mn4 st4 R4 S4 I4. eapply IH; [exact R4 | exact S4 | exact I4 | exact HQ].
Qed.

End Spec.
