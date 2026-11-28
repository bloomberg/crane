(** The top-level theorem: what [Solver.solve_dimacs], the function the
    drivers call, guarantees about the bytes of any file.

    From any pair of stores in which [bytes] holds [bs], no configuration
    of [solve_dimacs] is stuck (every access is in bounds and on a live
    cell; giving up with "out of fuel" is allowed), and an answer [r]
    satisfies [answer bs r]: it is exactly right about whether [bs] is a
    DIMACS CNF file ([DimacsSpec.dimacs]), and whenever it says SAT or
    UNSAT it is right about the formula the file spells.  Termination is
    not claimed; the step budget makes the answer 2 ("unknown") instead.
    [solve_dimacs_model] reads the same through [Global.interp]. *)
From ITree Require Import ITree ITreeFacts.
From Crane Require Import Monads.Global Monads.GlobalFacts Monads.Indices.
From Stdlib Require Import List PeanoNat Lia Bool.
Require Import Solver Cnf DimacsSpec Abstract Inv Sem Repr SolverSpec.
Import ListNotations.
Import Solver.
Local Set Warnings "-unused-intro-pattern".

(** What the result [r] of [solve_dimacs] says about the file [bs]. *)
Definition answer (bs : list nat) (r : nat) : Prop :=
  match r mod 8 with
  | 0 => exists F, dimacs bs F /\ ~ exists val, satisfies val F    (* UNSAT *)
  | 1 => exists F, dimacs bs F /\ exists val, satisfies val F      (* SAT *)
  | 2 | 3 => exists F, dimacs bs F             (* out of budget; model check failed *)
  | 4 => ~ exists F, dimacs bs F               (* not a DIMACS CNF file *)
  | _ => False
  end.

(** * Reading the bytes *)

(** [read_bytes] stays in bounds and returns the first [i] bytes before
    [acc], leaving the stores alone. *)
Lemma read_bytes_sp bytes bs : forall i acc Q mn ma,
  arr mn bytes bs -> i <= length bs -> Q (firstn i bs ++ acc) (mn, ma) ->
  safe (read_bytes bytes i acc) Q (mn, ma).
Proof.
  induction i as [|i IH]; intros acc Q mn ma Hb Hi HQ; cbn [read_bytes].
  - apply safe_ret. exact HQ.
  - assert (Hn : nth_error bs i = Some (nth i bs 0)) by (apply nth_error_nth'; lia).
    eapply safe_read_n_bind; [exact Hb | exact Hn |].
    apply IH; [exact Hb | lia |]. rewrite (firstn_S_snoc _ _ _ Hn), <- app_assoc in HQ. exact HQ.
Qed.

(** * The initial state *)

(** The abstract state [new_state nv cap] makes: no clause, no watch,
    nothing assigned, every phase false, the restart limit 100 and the
    arena capacity [cap]. *)
Definition init_st (nv cap : nat) : astate :=
  AS [] (repeat [] (2 * nv))
     (fun f => match f with
               | FPh => repeat 2 nv
               | FTr | FLim | FLrn => []
               | FMisc => lset (lset (repeat 0 NMISC) RLIMIT 100) ACAP cap
               | _ => repeat 0 nv
               end).

(** [repeat] read anywhere. *)
Lemma nth_repeat' {A} (x : A) n i : nth i (repeat x n) x = x.
Proof. revert i; induction n as [|n IH]; intros [|i]; cbn; auto. Qed.

(** [repeat] read anywhere, with any default equal to the element. *)
Lemma nth_repeat_eq {A} (x : A) n i d : d = x -> nth i (repeat x n) d = x.
Proof. intros ->. apply nth_repeat'. Qed.

(** The initial state satisfies [Inv] for any valuation. *)
Lemma init_inv val nv cap : Inv val (init_st nv cap).
Proof.
  split; [|split].
  - constructor; cbn [db fv init_st].
    + constructor.
    + intros w. rewrite nth_repeat_eq; lia.
    + constructor.
    + intros w. rewrite nth_repeat_eq by reflexivity. cbn. tauto.
    + constructor.
    + intros k l H. destruct k; discriminate.
    + intros i j H. cbn in H. lia.
    + constructor.
    + unfold QHEAD. rewrite !nth_lset_ne by (unfold RLIMIT, ACAP; lia). cbn. lia.
    + intros k l r H. destruct k; discriminate.
    + intros k l H. destruct k; discriminate.
    + intros l [].
  - intros ci l Hl. unfold cnt. cbn [wl init_st]. rewrite nth_repeat_eq by reflexivity. cbn. lia.
  - intros v. cbn [fv init_st]. apply nth_repeat_eq. reflexivity.
Qed.

(** The initial state satisfies [SI]. *)
Lemma init_si nv cap : SI nv (init_st nv cap).
Proof.
  split; [|constructor].
  constructor; cbn [db wl fv init_st]; rewrite ?repeat_length, ?lset_length; auto; try constructor.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. constructor.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. cbn. lia.
  - intros i j a b _ H. destruct i; discriminate.
Qed.

(** The empty array placeholder: no cells. *)
Definition e0 : narr := MkArray 0 0.

(** Arrays held with contents [C] and pairwise disjoint. *)
Definition held (m : Mn) (L : list narr) (C : list (list nat)) : Prop :=
  Forall2 (arr m) L C /\ NoDup (concat (map cells L)).

(** A new array at position [i] keeps the others held and disjoint. *)
Lemma held_alloc m L C i n x :
  held m L C -> held (anew m n x) (lset L i (afresh m n)) (lset C i (repeat x n)).
Proof.
  intros [HF Hn]. split.
  - apply F2_lset; [|apply (arr_anew (V := Solver.Vn))].
    eapply F2_impl; [|exact HF]. intros b ys _ H. now apply (arr_anew_old (V := Solver.Vn)).
  - apply sep_lset; [exact Hn|]. intros y Hy Hin. apply in_concat in Hin as (cl & Hcl & Hy').
    apply in_map_iff in Hcl as (b & <- & Hb). destruct (In_nth_error _ _ Hb) as (p & Hp).
    exact (afresh_disjoint (V := Solver.Vn) _ n _ _ _ (F2_nth _ _ _ _ _ [] HF Hp) Hy' Hy).
Qed.

(** A new array kept nowhere leaves the held arrays held. *)
Lemma held_skip m L C n x : held m L C -> held (anew m n x) L C.
Proof.
  intros [HF Hn]. split; [|exact Hn]. eapply F2_impl; [|exact HF]. intros b ys _ H.
  now apply (arr_anew_old (V := Solver.Vn)).
Qed.

(** An array of size 0 holds the empty list anywhere. *)
Lemma arr_empty (m : Mn) (b : narr) : asize b = 0 -> arr m b [].
Proof. intros H. split; [cbn; lia | intros i Hi; lia]. Qed.

(** Copies of an array of size 0 hold empty lists. *)
Lemma f2_repeat_empty (m : Mn) (b : narr) k : asize b = 0 -> Forall2 (arr m) (repeat b k) (repeat [] k).
Proof. intros H. induction k as [|k IH]; constructor; auto. now apply arr_empty. Qed.

(** Copies of an array of size 0 have no cells. *)
Lemma cells_repeat_empty (b : narr) k : asize b = 0 -> concat (map cells (repeat b k)) = [].
Proof. intros H. induction k as [|k IH]; cbn; auto. unfold cells. rewrite H. exact IH. Qed.

(** Allocate the next [nat] array of [new_state], at position [i]. *)
Ltac alloc i :=
  eapply safe_new_n_bind;
  match goal with
  | H : held ?m ?L ?C |- safe _ _ (anew ?m ?n ?x, _) =>
      pose proof (held_alloc m L C i n x H) as ?H; clear H
  end.

(** [new_state nv cap] makes arrays representing [init_st nv cap]. *)
Lemma new_state_sp nv cap Q mn ma :
  (forall s mn' ma', repr s nv mn' ma' (init_st nv cap) -> Q s (mn', ma')) ->
  safe (new_state nv cap) Q (mn, ma).
Proof.
  intros HQ. unfold new_state.
  assert (H0 : held mn (repeat e0 13) (repeat [] 13)).
  { split; [|cbn; constructor]. cbn. repeat constructor; apply arr_empty; reflexivity. }
  alloc 12.
  set (a := afresh mn cap) in *.
  eapply safe_new_ref_bind. set (ar := rfresh ma) in *.
  pose proof (refp_rnew (V := Solver.Va) ma a) as Hr1. fold ar in Hr1.
  eapply safe_new_n_bind. set (empty := afresh (anew mn cap 0) 0).
  match goal with H : held _ _ _ |- _ => apply (held_skip _ _ _ 0 0) in H end.
  eapply safe_new_a_bind. set (ma1 := rnew ma a) in *. set (wd := afresh ma1 (2 * nv)).
  pose proof (arr_anew (V := Solver.Va) ma1 (2 * nv) empty) as Hwd. fold wd in Hwd.
  pose proof (refp_anew (V := Solver.Va) ma1 (2 * nv) empty _ _ Hr1) as Hr2.
  assert (Hv : ~ In (Global.ref_index narr ar) (cells wd)).
  { intros Hin. apply in_cells in Hin. pose proof (refp_lt_fresh (V := Solver.Va) _ _ _ Hr1) as X.
    unfold wd in Hin. cbn [abase asize afresh] in Hin. lia. }
  alloc 10. alloc 11. alloc 0. alloc 1. alloc 2. alloc 3. alloc 4. alloc 5. alloc 6. alloc 7.
  alloc 9. alloc 8.
  match goal with H : held ?m ?L ?C |- _ => destruct H as [HF Hnd]; cbn [repeat] in HF, Hnd end.
  repeat (first [rewrite lset_cons0 in HF | rewrite lset_consS in HF]).
  repeat (first [rewrite lset_cons0 in Hnd | rewrite lset_consS in Hnd]).
  match goal with |- safe _ _ (?m, _) => set (mnA := m) in * end.
  match type of HF with Forall2 _ [?asg; ?lvl; ?rsn; ?ph; ?st; ?sn; ?tr; ?tlim; ?m; ?lr; ?wl; ?wc; _] _ =>
    set (s := mk_state ar wd wl wc asg lvl rsn ph st sn tr tlim lr m) end.
  set (ws := repeat empty (2 * nv)).
  assert (C0 : conc s nv mnA (anew ma1 (2 * nv) empty) a ws
                 ([repeat 0 nv; repeat 0 nv; repeat 0 nv; repeat 2 nv; repeat 0 nv; repeat 0 nv; repeat 0 nv;
                   repeat 0 nv; repeat 0 NMISC; repeat 0 (nv + 1); repeat 0 (2 * nv); repeat 0 (2 * nv);
                   repeat 0 cap] ++ repeat [] (2 * nv))).
  { constructor.
    - exact Hr2.
    - exact Hwd.
    - apply repeat_length.
    - exact Hv.
    - unfold own. apply Forall2_app; [exact HF|]. apply f2_repeat_empty. reflexivity.
    - unfold own, ws. rewrite map_app, concat_app, (cells_repeat_empty empty) by reflexivity.
      rewrite app_nil_r. exact Hnd. }
  eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 8 _ C0 eq_refl) | cbn; rewrite ?repeat_length; unfold RLIMIT, NMISC; lia |].
  pose proof (conc_awrite _ _ _ _ _ _ _ 8 _ RLIMIT 100 C0 eq_refl ltac:(cbn; rewrite ?repeat_length; unfold RLIMIT, NMISC; lia)) as C1.
  eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 8 _ C1 eq_refl) | simpl; rewrite ?lset_length, ?repeat_length; unfold ACAP, NMISC; lia |].
  pose proof (conc_awrite _ _ _ _ _ _ _ 8 _ ACAP cap C1 eq_refl ltac:(simpl; rewrite ?lset_length, ?repeat_length; unfold ACAP, NMISC; lia)) as C2.
  apply safe_ret. apply HQ. eapply repr_of; [exact C2|].
  match type of C2 with conc _ _ _ _ _ _ ?cs => set (cs2 := cs) in C2 |- * end.
  assert (Ecs : cs2 = [repeat 0 nv; repeat 0 nv; repeat 0 nv; repeat 2 nv; repeat 0 nv; repeat 0 nv; repeat 0 nv;
                       repeat 0 nv; lset (lset (repeat 0 NMISC) RLIMIT 100) ACAP cap; repeat 0 (nv + 1);
                       repeat 0 (2 * nv); repeat 0 (2 * nv); repeat 0 cap] ++ repeat [] (2 * nv)) by reflexivity.
  rewrite Ecs. clear.
  assert (Hw : forall l, nth (13 + l) ([repeat 0 nv; repeat 0 nv; repeat 0 nv; repeat 2 nv; repeat 0 nv; repeat 0 nv; repeat 0 nv;
                       repeat 0 nv; lset (lset (repeat 0 NMISC) RLIMIT 100) ACAP cap; repeat 0 (nv + 1);
                       repeat 0 (2 * nv); repeat 0 (2 * nv); repeat 0 cap] ++ repeat [] (2 * nv)) [] = [])
    by (intros l; cbn [app nth Nat.add]; apply nth_repeat_eq; reflexivity).
  constructor; cbn [fidx db wl fv init_st]; rewrite ?Hw.
  - rewrite length_app, repeat_length. reflexivity.
  - intros f Hf. destruct Hf as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
  - now rewrite !lset_length, repeat_length.
  - cbn. rewrite map_repeat. reflexivity.
  - exists (repeat 0 nv). reflexivity.
  - apply repeat_length.
  - reflexivity.
  - exists (repeat 0 nv). reflexivity.
  - apply repeat_length.
  - reflexivity.
  - exists (repeat 0 (nv + 1)). reflexivity.
  - apply repeat_length.
  - reflexivity.
  - exists (repeat 0 cap). reflexivity.
  - reflexivity.
  - cbn. symmetry. apply repeat_length.
  - apply repeat_length.
  - apply repeat_length.
  - apply repeat_length.
  - intros l _. cbn [app nth]. rewrite !nth_repeat_eq by reflexivity. reflexivity.
  - intros l _. rewrite Hw. cbn [app nth]. rewrite !nth_repeat_eq by reflexivity. reflexivity.
  - intros l _. rewrite Hw, !nth_repeat_eq by reflexivity. exists []. reflexivity.
Qed.

(** * Loading *)

(** The tail-recursive [tlen] is [length]. *)
Lemma tlen_eq {A} (l : list A) n : tlen l n = n + length l.
Proof. revert n; induction l as [|x l IH]; intros n; cbn; [lia | rewrite IH; lia]. Qed.

(** [cnf_size] with a starting count. *)
Lemma cnf_size_acc F k : fold_left (fun n c => n + 1 + tlen c 0) F k = k + cnf_size F.
Proof.
  unfold cnf_size. revert k; induction F as [|c F IH]; intros k; cbn [fold_left]; [lia|].
  rewrite (IH (k + 1 + tlen c 0)), (IH (0 + 1 + tlen c 0)). lia.
Qed.

(** The arena size of one more clause. *)
Lemma cnf_size_cons c F : cnf_size (c :: F) = 1 + length c + cnf_size F.
Proof. unfold cnf_size at 1. cbn. rewrite cnf_size_acc, tlen_eq. lia. Qed.

(** [store_lits a c pos] writes [c] into the arena from [pos] on, past the
    clauses. *)
Lemma store_lits_sp s nv : forall c pos Q mn ma st a ws cs X P,
  rep s nv mn ma st a ws cs -> car cs = X ++ P -> length X = pos -> length (enc (db st)) <= pos ->
  length c <= length P ->
  (forall mn' cs', rep s nv mn' ma st a ws cs' -> car cs' = X ++ c ++ skipn (length c) P -> Q tt (mn', ma)) ->
  safe (store_lits a c pos) Q (mn, ma).
Proof.
  induction c as [|l c IH]; intros pos Q mn ma st a ws cs X P [C A] Hc HX Hp HP HQ; cbn [store_lits].
  - apply safe_ret. apply (HQ mn cs (conj C A)). now rewrite Hc.
  - destruct P as [|p0 P]; [cbn in HP; lia|].
    assert (Hi : pos < length (car cs)) by (rewrite Hc, length_app; cbn; lia).
    eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 12 _ C eq_refl) | exact Hi |].
    apply (IH (pos + 1) Q (awrite mn a pos l) ma st a ws (lset cs 12 (lset (car cs) pos l)) (X ++ [l]) P).
    + split; [apply (conc_awrite s nv mn ma a ws cs 12 _ _ _ C); [reflexivity | exact Hi]|].
      apply abs_arpad; [exact A | lia].
    + rewrite nth_lset_eq by (rewrite (a_len _ _ _ A); lia). rewrite Hc, lset_app_r by lia.
      rewrite HX, Nat.sub_diag, lset_cons0, <- app_assoc. reflexivity.
    + rewrite length_app. cbn. lia.
    + lia.
    + cbn in HP. lia.
    + intros mn' cs' R' Hc'. apply (HQ mn' cs' R'). rewrite Hc', <- app_assoc. reflexivity.
Qed.

Section Load.
(** The solver's handles, its number of variables, and the optional
    valuation, as in [SolverSpec]. *)
Variables (s : state) (nv : nat) (val : option (nat -> bool)).

(** The representation relation for these handles. *)
Local Notation R := (repr s nv).

(** [load a F pos] stores the clauses [F] at the end of the arena [a],
    watching the longer ones and asserting the unit ones at level 0; it
    answers false only when [F] has no model. *)
Lemma load_sp a : forall F Q mn ma st,
  R mn ma st -> SI nv st -> Inv val st -> lim st = [] -> refp ma (arena s) a ->
  length (enc (db st)) + cnf_size F <= nth ACAP (fv st FMisc) 0 ->
  lits_below (2 * nv) F -> opt val (fun v => satisfies v F) ->
  (forall r mn' ma' st', R mn' ma' st' -> SI nv st' -> Inv val st' -> (r = false -> opt val (fun _ => False)) ->
     Q r (mn', ma')) ->
  safe (load s a F (length (enc (db st)))) Q (mn, ma).
Proof.
  induction F as [|c F IH]; intros Q mn ma st Hr HS I Hl0 Ha Hcap Hlit Hsat HQ; cbn [load].
  { apply safe_ret. apply (HQ true mn ma st Hr HS I). discriminate. }
  cbv zeta. rewrite tlen_eq. cbn [Nat.add].
  rewrite cnf_size_cons in Hcap.
  pose proof Hr as (a0 & ws & cs & C & A). pose proof (ref_rep _ _ _ _ _ _ _ _ _ (conj C A) Ha) as ->.
  pose proof (a_acap _ _ _ A) as Ecap. destruct (a_ar _ _ _ A) as [P0 HP0].
  assert (HlP0 : 1 + length c + cnf_size F <= length P0).
  { rewrite Ecap, HP0, length_app in Hcap. lia. }
  destruct P0 as [|p0 P1]; [cbn in HlP0; lia|].
  assert (Hi : length (enc (db st)) < length (car cs)) by (rewrite HP0, length_app; cbn; lia).
  eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 12 _ C eq_refl) | exact Hi |].
  pose proof (conc_awrite s nv mn ma a0 ws cs 12 _ _ (length c) C eq_refl Hi) as C1.
  pose proof (abs_arpad _ _ _ (length (enc (db st))) (length c) A ltac:(lia)) as A1.
  apply safe_bind. apply (store_lits_sp s nv c (length (enc (db st)) + 1) _ _ ma st a0 ws _
                           (enc (db st) ++ [length c]) P1 (conj C1 A1)); [| rewrite length_app; cbn; lia | lia | cbn in HlP0; lia |].
  { rewrite nth_lset_eq by (rewrite (a_len _ _ _ A); lia). rewrite HP0, lset_app_r, Nat.sub_diag, lset_cons0 by lia.
    rewrite <- app_assoc. reflexivity. }
  intros mn2 cs2 [C2 A2] Hc2. cbv beta.
  assert (Hc2' : car cs2 = enc (db st) ++ (length c :: c) ++ skipn (length c) P1) by (rewrite Hc2, <- app_assoc; reflexivity).
  assert (Hrb : Forall (fun r => r <= length (db st)) (rsn st)) by apply (si_r _ _ (proj1 HS)).
  assert (Hwb : Forall (Forall (fun ci => ci < length (db st))) (wl st)).
  { eapply Forall_impl; [|apply (si_w _ _ (proj1 HS))]. intros L HL. eapply Forall_impl; [|exact HL].
    intros c' (c'' & Hc' & _). apply nth_error_Some. congruence. }
  pose proof (abs_cpush _ _ _ c _ A2 Hrb Hwb Hc2') as A3.
  pose proof (rep_fld s nv _ _ _ _ _ FMisc C2) as Hm2.
  assert (Hal : ALEN < length (cfld cs2 FMisc))
    by (rewrite (a_fld _ _ _ A2 FMisc), (a_miscn _ _ _ A2) by (unfold plain; tauto); unfold ALEN, NMISC; lia).
  unfold put. replace (length (enc (db st)) + 1 + length c) with (length (enc (db st)) + S (length c)) by lia.
  eapply safe_write_n_bind; [exact Hm2 | exact Hal |].
  pose proof (conc_awrite s nv _ _ _ _ _ (fidx FMisc) _ ALEN (length (enc (db st)) + S (length c)) C2 (own_fld _ _ _ FMisc) Hal) as C3.
  rewrite (a_fld _ _ _ A2 FMisc) in C3, A3 by (unfold plain; tauto).
  set (st3 := fset (cpush st c) FMisc (lset (fv st FMisc) ALEN (length (enc (db st)) + S (length c)))) in *.
  assert (R3 : R _ ma st3) by (eapply repr_of; [exact C3 | exact A3]).
  assert (Hcok : Forall (lit_ok nv) c) by (inversion Hlit; auto).
  assert (Hlit' : lits_below (2 * nv) F) by (inversion Hlit; auto).
  assert (Hsat' : opt val (fun v => satisfies v F)) by (intros v Hv; specialize (Hsat v Hv); inversion Hsat; auto).
  assert (Hcl : cholds val c) by (apply (cholds_opt val); intros v Hv; specialize (Hsat v Hv); inversion Hsat; auto).
  assert (S3 : SI nv st3).
  { split; [|apply HS]. exact (sic_lset nv (cpush st c) FMisc ALEN _ (sic_cpush nv st c (proj1 HS) Hcok) ltac:(tauto)). }
  assert (I3 : Inv val st3).
  { destruct I as (Cc & W & S0). split; [|split].
    - unfold st3. apply core_fset_misc; [apply core_cpush; [exact Cc | exact Hcl]|].
      cbn [fv fset fld_eqb cpush]. rewrite nth_lset_ne by (unfold QHEAD, ALEN; lia). pose proof (i_qtr _ _ Cc). lia.
    - unfold st3. cbn [db wl fset cpush]. apply wch_snoc, W.
    - intros v. apply S0. }
  assert (Hdb3 : db st3 = db st ++ [c]) by reflexivity.
  assert (Hpos : length (enc (db st)) + S (length c) = length (enc (db st3))).
  { rewrite Hdb3, enc_app, length_app. cbn. rewrite app_nil_r. lia. }
  assert (Hcap3 : forall st', db st' = db st3 -> nth ACAP (fv st' FMisc) 0 = nth ACAP (fv st FMisc) 0 ->
                    length (enc (db st')) + cnf_size F <= nth ACAP (fv st' FMisc) 0).
  { intros st' E1 E2. rewrite E1, E2, <- Hpos. lia. }
  assert (Hac3 : nth ACAP (fv st3 FMisc) 0 = nth ACAP (fv st FMisc) 0)
    by (unfold st3; cbn [fv fset fld_eqb cpush]; apply nth_lset_ne; unfold ALEN, ACAP; lia).
  rewrite Hpos. rewrite Hpos in R3.
  destruct c as [|l [|l2 c']]; cbv beta iota.
  - (* an empty clause: no model *)
    apply safe_ret. apply (HQ false _ ma st3 R3 S3 I3). intros _ v Hv. specialize (Hsat v Hv).
    inversion Hsat as [|? ? Hx]; subst. inversion Hx.
  - (* a unit clause *)
    apply safe_bind. eapply (lit_value_sp s nv l); [exact R3 | apply S3 | inversion Hcok; auto |]. cbv beta.
    assert (Hd3 : In [l] (db st3)) by (rewrite Hdb3; apply in_or_app; right; now left).
    destruct (Nat.eqb_spec (lval (asg st3) l) 2) as [E2 | E2].
    + apply safe_ret. apply (HQ false _ ma st3 R3 S3 I3). intros _ v Hv. pose proof (proj1 I3) as C3v. rewrite Hv in C3v.
      apply (no_false_clause_l0 v st3 C3v [l]); [unfold st3; cbn [fv fset fld_eqb cpush]; now rewrite Hl0 | exact Hd3 |].
      constructor; [exact E2 | constructor].
    + apply safe_seq with (P := fun _ h => exists mn4 st4, h = (mn4, ma) /\ R mn4 ma st4 /\ SI nv st4 /\
        Inv val st4 /\ lim st4 = [] /\ db st4 = db st3 /\ nth ACAP (fv st4 FMisc) 0 = nth ACAP (fv st FMisc) 0).
      * destruct (Nat.eqb_spec (lval (asg st3) l) 0) as [E0 | E0].
        -- eapply (enqueue_sp s nv val l 0 0); [exact R3 | apply S3 | apply I3 | inversion Hcok; auto | exact E0 | reflexivity |].
           intros mn4 R4. exists mn4, (enqA st3 l 0). split; [reflexivity|]. split; [exact R4|].
           assert (Hlok : lit_ok nv l) by (inversion Hcok; auto).
           split; [apply si_enqA; [exact S3 | exact Hlok | lia]|]. split.
           ++ apply enqA_wch; [exact I3|]. apply (core_enqA nv); [apply I3 | apply S3 | exact Hlok | exact E0 | | intros; lia |].
              ** intros _. left. unfold st3. cbn [fv fset fld_eqb cpush]. rewrite Hl0. constructor.
              ** intros _. apply (holds_opt val). intros v Hv. specialize (Hsat v Hv). inversion Hsat as [|? ? Hx]; subst.
                 inversion Hx as [? ? Hx' | ? ? Hx']; subst; [exact Hx' | inversion Hx'].
           ++ unfold enqA, enq. cbn [fv fset fld_eqb db]. split; [unfold st3; cbn [fv fset fld_eqb cpush]; exact Hl0|].
              split; [reflexivity|]. rewrite nth_lset_ne by (unfold TLEN, ACAP; lia). exact Hac3.
        -- apply safe_ret. eexists; exists st3. split; [reflexivity|]. split; [exact R3|]. split; [exact S3|]. split; [exact I3|].
           split; [unfold st3; cbn [fv fset fld_eqb cpush]; exact Hl0|]. split; [reflexivity | exact Hac3].
      * intros _ h (mn4 & st4 & -> & R4 & S4 & I4 & Hl4 & Hd4 & Hc4). rewrite <- Hd4.
        eapply IH; [exact R4 | exact S4 | exact I4 | exact Hl4 | exact Ha | apply Hcap3; auto | exact Hlit' | exact Hsat' | exact HQ].
  - (* a longer clause: watch it *)
    apply safe_bind. eapply (attach_sp s nv a0 (length (db st)) (l :: l2 :: c')); [exact R3 | apply S3 | exact Ha | | cbn; lia | | | |].
    { rewrite Hdb3, nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite Hdb3, off_snoc. reflexivity. }
    { apply (proj1 (proj2 I3)). }
    { intros l0 Hl. unfold st3 in Hl |- *. cbn [db wl fset cpush] in Hl |- *. apply (wch_fresh _ _ l0 (proj1 (proj2 I))). exact Hl. }
    intros mn4 ma4 st4 R4 S4c Ed4 Ef4 W4 Ha4. cbv beta.
    rewrite <- Ed4. eapply IH; [exact R4 | | | | exact Ha4 | apply Hcap3; [exact Ed4 | rewrite Ef4; exact Hac3] | exact Hlit' | exact Hsat' | exact HQ].
    + split; [exact S4c | unfold lim_lt; rewrite !Ef4; apply S3].
    + split; [apply (core_ext val st3 st4); rewrite ?Ed4, ?Ef4; auto; apply I3|]. split; [exact W4|].
      intros v. rewrite Ef4. apply (proj2 (proj2 I3)).
    + rewrite Ef4. unfold st3. cbn [fv fset fld_eqb cpush]. exact Hl0.
Qed.

End Load.

(** * Checking the model *)

(** The valuation the assignment [A] spells: true exactly for value 1. *)
Definition model_of (A : list nat) : nat -> bool := fun v => Nat.eqb (nth v A 0) 1.

(** A literal true under the assignment is true under [model_of]. *)
Lemma lval_true_model A l : lval A l = 1 -> lit_true (model_of A) l.
Proof.
  unfold lval, lval_of, lit_true, model_of. intros H.
  destruct (lit_cases l) as [[E M] | [E M]]; rewrite M in H; cbn [Nat.eqb] in H; rewrite E at 2.
  - rewrite even_2v. destruct (Nat.eqb_spec (nth (lvar l) A 0) 0); [discriminate|]. rewrite H. reflexivity.
  - rewrite even_2v1. destruct (Nat.eqb_spec (nth (lvar l) A 0) 0); [discriminate|].
    destruct (Nat.eqb_spec (nth (lvar l) A 0) 1); [|reflexivity]. lia.
Qed.

(** [clause_sat c] answers true only when [model_of] the assignment makes a
    literal of [c] true. *)
Lemma clause_sat_sp s nv : forall c Q mn ma st,
  repr s nv mn ma st -> SIc nv st -> Forall (lit_ok nv) c ->
  (forall b, (b = true -> Exists (lit_true (model_of (asg st))) c) -> Q b (mn, ma)) ->
  safe (clause_sat s c) Q (mn, ma).
Proof.
  induction c as [|l c IH]; intros Q mn ma st Hr Hs Hc HQ; cbn [clause_sat].
  - apply safe_ret, HQ. discriminate.
  - inversion Hc as [|? ? Hl Hc']; subst.
    apply safe_bind. eapply lit_value_sp; [exact Hr | exact Hs | exact Hl |]. cbv beta.
    destruct (Nat.eqb_spec (lval (asg st) l) 1) as [E | E].
    + apply safe_ret, HQ. intros _. left. now apply lval_true_model.
    + eapply IH; [exact Hr | exact Hs | exact Hc' |]. intros b Hb. apply HQ. intros Ht. right. auto.
Qed.

(** [check_model F] answers true only when [model_of] the assignment
    satisfies [F]. *)
Lemma check_model_sp s nv : forall F Q mn ma st,
  repr s nv mn ma st -> SIc nv st -> lits_below (2 * nv) F ->
  (forall b, (b = true -> satisfies (model_of (asg st)) F) -> Q b (mn, ma)) ->
  safe (check_model s F) Q (mn, ma).
Proof.
  induction F as [|c F IH]; intros Q mn ma st Hr Hs HF HQ; cbn [check_model].
  - apply safe_ret, HQ. intros _. constructor.
  - inversion HF as [|? ? Hc HF']; subst.
    apply safe_bind. eapply (clause_sat_sp s nv c); [exact Hr | exact Hs | exact Hc |]. intros ok Hok. cbv beta.
    destruct ok.
    + eapply IH; [exact Hr | exact Hs | exact HF' |]. intros b Hb. apply HQ. intros Ht.
      constructor; [now apply Hok | now apply Hb].
    + apply safe_ret, HQ. discriminate.
Qed.

(** * Running *)

(** [code + 8 * k] modulo 8 is the code. *)
Lemma mod8_code c k : c < 8 -> (c + 8 * k) mod 8 = c.
Proof. intros H. symmetry. apply (Nat.mod_unique _ _ k); lia. Qed.

(** [run] on clauses [F] over [nvars] variables is safe; its code says SAT
    only with a model, and, for a valuation [val] satisfying [F], never
    says UNSAT. *)
Lemma run_sp (val : option (nat -> bool)) fuel budget nvars F Q mn ma :
  lits_below (2 * nvars) F -> opt val (fun v => satisfies v F) ->
  (forall r h, (r mod 8 = 0 -> opt val (fun _ => False)) -> (r mod 8 = 1 -> exists v, satisfies v F) ->
     r mod 8 <= 3 -> Q r h) ->
  safe (run fuel budget nvars F) Q (mn, ma).
Proof.
  intros Hlit Hsat HQ. unfold run.
  apply safe_bind. apply new_state_sp. intros s mn1 ma1 R1. cbv beta.
  eapply (rd_ref s nvars); [exact R1 |]. intros a Ha.
  apply safe_bind. replace (load s a F 0) with (load s a F (length (enc (db (init_st nvars (cnf_size F)))))) by reflexivity.
  eapply (load_sp s nvars val a F); [exact R1 | apply init_si | apply init_inv | reflexivity | exact Ha | | exact Hlit | exact Hsat |].
  { change (0 + cnf_size F <= cnf_size F). lia. }
  intros ok mn2 ma2 st2 R2 S2 I2 Hok. cbv beta.
  apply safe_seq with (P := fun code h => exists mn3 ma3 st3, h = (mn3, ma3) /\ repr s nvars mn3 ma3 st3 /\
    (code = 0 -> opt val (fun _ => False)) /\ (code = 1 -> exists v, satisfies v F) /\ code <= 3).
  - destruct ok.
    + apply safe_bind. eapply (search_sp s nvars val fuel budget); [exact R2 | exact S2 | exact I2 |].
      intros r mn3 ma3 st3 R3 S3 I3 Hr2 Hr0. cbv beta.
      destruct (Nat.eqb_spec r 1) as [-> | Hr1].
      * apply safe_bind. eapply (check_model_sp s nvars F); [exact R3 | apply S3 | exact Hlit |].
        intros good Hgood. cbv beta. apply safe_ret. exists mn3, ma3, st3. split; [reflexivity|]. split; [exact R3|].
        destruct good; split; try discriminate; split; try lia; intros _.
        -- exists (model_of (asg st3)). now apply Hgood.
      * apply safe_ret. exists mn3, ma3, st3. split; [reflexivity|]. split; [exact R3|].
        split; [exact Hr0|]. split; [intros; lia | lia].
    + apply safe_ret. exists mn2, ma2, st2. split; [reflexivity|]. split; [exact R2|].
      split; [intros _; apply Hok; reflexivity|]. split; [discriminate | lia].
  - intros code h (mn3 & ma3 & st3 & -> & R3 & Hc0 & Hc1 & Hc3). unfold get.
    eapply (rd_misc s nvars CONFLICTS); [exact R3 | unfold CONFLICTS, NMISC; lia |].
    apply safe_ret. apply HQ; rewrite mod8_code by lia; auto.
Qed.

(** * The theorem *)

(** The guarantee of the module header: [solve_dimacs] is safe from any
    stores in which [bytes] holds [bs], and its answer is [answer bs]. *)
Theorem solve_dimacs_correct fuel budget bytes bs mn ma :
  arr mn bytes bs ->
  safe (Solver.solve_dimacs fuel budget bytes (length bs)) (fun r _ => answer bs r) (mn, ma).
Proof.
  intros Hb. unfold solve_dimacs.
  apply safe_bind. eapply read_bytes_sp; [exact Hb | lia |]. cbv beta.
  rewrite firstn_all, app_nil_r.
  destruct (parse bs) as [[nvars F] |] eqn:Hp.
  2: { apply safe_ret. unfold answer. cbn. now apply parse_none. }
  destruct (parse_sound _ _ _ Hp) as (HD & HB & _).
  pose proof (run_sp None fuel budget nvars F (fun r _ => (r mod 8 = 1 -> exists v, satisfies v F) /\ r mod 8 <= 3)
                mn ma HB ltac:(intros v Hv; discriminate) ltac:(intros r h _ H1 H3; cbv beta; split; assumption)) as H0.
  assert (Hv : forall v, satisfies v F ->
            safe (run fuel budget nvars F) (fun r _ => r mod 8 = 0 -> False) (mn, ma)).
  { intros v Hv. apply (run_sp (Some v)); [exact HB | intros v' E; injection E as <-; exact Hv |].
    intros r h H0' _ _ E. exact (H0' E v eq_refl). }
  eapply safe_conseq; [exact (safe_conj_all _ _ _ _ _ H0 Hv) |].
  intros r h ((H1 & H3) & Hall). unfold answer.
  destruct (r mod 8) as [|[|[|[|]]]] eqn:E; try lia.
  - exists F. split; [exact HD|]. intros (v & Hsv). exact (Hall v Hsv eq_refl).
  - exists F. split; [exact HD | auto].
  - exists F. exact HD.
  - exists F. exact HD.
Qed.

(** The same through the model: every run of the two-layer
    [Global.interp] of [solve_dimacs] either throws "out of fuel" or
    returns an answer satisfying [answer bs]; no access ever fails. *)
Corollary solve_dimacs_model fuel budget bytes bs (mn : Mn) (ma : Ma) :
  arr mn bytes bs ->
  model_safe (fun '(_, (_, r)) => answer bs r)
    (Global.interp Nat.le _ (Global.interp Nat.le _ (Solver.solve_dimacs fuel budget bytes (length bs)) mn) ma).
Proof. intros Hb. exact (safe_model _ _ mn ma (solve_dimacs_correct fuel budget bytes bs mn ma Hb)). Qed.
