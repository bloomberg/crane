(** Layer 1 of the proof: the abstract state a heap represents.

    The solver's mutable state is a [state] record of handles.  [repr]
    relates a heap to an abstract state [astate]: the handles and contents
    of the clause vectors, the handles and contents of the watch lists, and
    the contents of the nine per-variable / trail / counter vectors, read
    through [fv] by field name.

    Cells are untyped ([{A : Type & list A}]), so typing separates nothing
    (see the Stage 1–2 log in PLAN.md).  Separation is one explicit fact:
    the locations of [input], the two vectors of handles, the nine fields,
    every clause and every watch list are pairwise distinct ([r_nd]).  Each
    write then changes exactly one component of the abstract state, and the
    lemmas below ([set_f], [set_cl], [set_w], ...) give the [wp] of each
    event in those terms.  A vector outside [locs] -- the learnt clause
    while it is built, a clause while [load] reads it -- is a scratch cell:
    [keeps] says a write to the state leaves it alone. *)
From Stdlib Require Import List PeanoNat Lia Bool Permutation.
From Crane Require Import Monads.ITree.
Require Import SatVec VecSem Solver.
Import ListNotations.
Import Solver.

Local Notation cellof := (fun T : Type => list T).

(** * Fields *)

Inductive fld := FAsg | FLvl | FRsn | FPh | FSt | FSn | FTr | FLim | FMisc.

Definition fld_eqb (f g : fld) : bool :=
  match f, g with
  | FAsg, FAsg | FLvl, FLvl | FRsn, FRsn | FPh, FPh | FSt, FSt
  | FSn, FSn | FTr, FTr | FLim, FLim | FMisc, FMisc => true
  | _, _ => false
  end.

Lemma fld_eqb_eq f g : fld_eqb f g = true <-> f = g.
Proof. destruct f, g; cbn; split; congruence. Qed.

Lemma fld_eqb_refl f : fld_eqb f f = true.
Proof. now apply fld_eqb_eq. Qed.

Definition all_flds := [FAsg; FLvl; FRsn; FPh; FSt; FSn; FTr; FLim; FMisc].

Lemma in_all_flds f : In f all_flds.
Proof. destruct f; cbn; tauto. Qed.

Definition floc (s : state) (f : fld) : vec nat :=
  match f with
  | FAsg => assigns s | FLvl => level s | FRsn => reason s | FPh => phase s
  | FSt => stamp s | FSn => seen s | FTr => trail s | FLim => trail_lim s
  | FMisc => misc s
  end.

(** * Abstract states *)

Record astate := AS {
  hcls : list (vec nat);      (** clause handles *)
  db : list (list nat);       (** clause contents *)
  hwl : list (vec nat);       (** watch-list handles, per literal *)
  wl : list (list nat);       (** watch-list contents *)
  fv : fld -> list nat        (** the contents of each field *)
}.

Definition fset (st : astate) (f : fld) (xs : list nat) : astate :=
  AS (hcls st) (db st) (hwl st) (wl st) (fun g => if fld_eqb g f then xs else fv st g).
Definition dset (st : astate) (d : list (list nat)) : astate :=
  AS (hcls st) d (hwl st) (wl st) (fv st).
Definition wset (st : astate) (w : list (list nat)) : astate :=
  AS (hcls st) (db st) (hwl st) w (fv st).
Definition cpush (st : astate) (c : vec nat) (cl : list nat) : astate :=
  AS (hcls st ++ [c]) (db st ++ [cl]) (hwl st) (wl st) (fv st).
Definition wpush (st : astate) (w : vec nat) (ws : list nat) : astate :=
  AS (hcls st) (db st) (hwl st ++ [w]) (wl st ++ [ws]) (fv st).

Lemma fv_fset_eq st f xs : fv (fset st f xs) f = xs.
Proof. cbn. now rewrite fld_eqb_refl. Qed.

(** [v] holds the list [xs] of [nat]s. *)
Definition pts (h : heap) (v : vec nat) (xs : list nat) : Prop :=
  h (vloc v) = Some (existT cellof nat xs).

Lemma pts_upd_neq h v xs l c : vloc v <> l -> pts h v xs -> pts (upd h l c) v xs.
Proof. unfold pts. intros. now rewrite upd_neq. Qed.

Lemma pts_upd_eq h v xs : pts (upd h (vloc v) (existT cellof nat xs)) v xs.
Proof. apply upd_eq. Qed.

Lemma pts_inj h v xs ys : pts h v xs -> pts h v ys -> xs = ys.
Proof. apply cell_inj. Qed.

(** * Lists *)

Definition disj (a b : list loc) : Prop := forall x, In x a -> In x b -> False.

Lemma nodup_app_iff (l1 l2 : list loc) :
  NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ disj l1 l2.
Proof.
  split.
  - intros H. split; [eapply NoDup_app_remove_r; eauto|].
    split; [eapply NoDup_app_remove_l; eauto|].
    induction l1 as [|a l1 IH]; intros x Hx1 Hx2; [destruct Hx1|].
    inversion H as [|? ? Ha Hn]; subst.
    destruct Hx1 as [<- | Hx1].
    + apply Ha, in_or_app. auto.
    + eapply IH; eauto.
  - intros (H1 & H2 & H3). apply NoDup_app; auto; intros a Ha Hb; eapply H3; eauto.
Qed.

Lemma nodup_map_inj {A} (f : A -> loc) l x y :
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; [intros _ []|].
  cbn. intros Hn Hx Hy E. inversion Hn as [|? ? Ha Hn']; subst.
  destruct Hx as [<- | Hx], Hy as [<- | Hy]; auto.
  - exfalso. apply Ha. rewrite E. now apply in_map.
  - exfalso. apply Ha. rewrite <- E. now apply in_map.
Qed.

Lemma nth_error_lset_eq {A} (xs : list A) i x : i < length xs -> nth_error (lset xs i x) i = Some x.
Proof. revert i; induction xs; destruct i; cbn; intros; try lia; auto. apply IHxs; lia. Qed.

Lemma nth_error_lset_neq {A} (xs : list A) i j x : i <> j -> nth_error (lset xs i x) j = nth_error xs j.
Proof. revert i j; induction xs; destruct i, j; cbn; intros; auto; congruence. Qed.

Lemma nth_error_lset {A} (xs : list A) i j x :
  nth_error (lset xs i x) j = if Nat.eqb i j then (if Nat.ltb i (length xs) then Some x else None)
                              else nth_error xs j.
Proof.
  destruct (Nat.eqb_spec i j) as [<- | Hne].
  - destruct (Nat.ltb_spec i (length xs)).
    + now apply nth_error_lset_eq.
    + apply nth_error_None. rewrite lset_length. lia.
  - now apply nth_error_lset_neq.
Qed.

Lemma nth_lset {A} (xs : list A) i j x d :
  nth j (lset xs i x) d = if Nat.eqb i j then (if Nat.ltb i (length xs) then x else d) else nth j xs d.
Proof.
  destruct (Nat.ltb_spec j (length xs)).
  - assert (Hj : j < length (lset xs i x)) by (now rewrite lset_length).
    pose proof (nth_error_lset xs i j x) as E.
    rewrite (nth_error_nth' _ d Hj), (nth_error_nth' _ d H) in E.
    destruct (Nat.eqb i j), (Nat.ltb i (length xs)); congruence.
  - rewrite !nth_overflow; try (rewrite ?lset_length; lia).
    destruct (Nat.eqb_spec i j), (Nat.ltb_spec i (length xs)); auto; lia.
Qed.

Lemma lset_app_r {A} (xs ys : list A) i x :
  length xs <= i -> lset (xs ++ ys) i x = xs ++ lset ys (i - length xs) x.
Proof.
  revert i; induction xs as [|a xs IH]; intros i Hi; cbn.
  - now rewrite Nat.sub_0_r.
  - destruct i; [cbn in Hi; lia|]. cbn. f_equal. apply IH. cbn in Hi. lia.
Qed.

Lemma Forall2_nth {A B} (R : A -> B -> Prop) xs ys k x :
  Forall2 R xs ys -> nth_error xs k = Some x -> exists y, nth_error ys k = Some y /\ R x y.
Proof.
  intros H. revert k. induction H; intros [|k] E; cbn in *; try discriminate.
  - injection E as ->. eauto.
  - eauto.
Qed.

(** * The representation relation *)

Section Repr.
Variables (s : state) (inp : vec nat) (xs0 : list nat).

Definition locs (st : astate) : list loc :=
  [vloc inp; vloc (clauses s); vloc (watches s)]
  ++ map (fun f => vloc (floc s f)) all_flds
  ++ map vloc (hcls st) ++ map vloc (hwl st).

Record repr (h : heap) (st : astate) : Prop := {
  r_cls : h (vloc (clauses s)) = Some (existT cellof (vec nat) (hcls st));
  r_wls : h (vloc (watches s)) = Some (existT cellof (vec nat) (hwl st));
  r_db : Forall2 (pts h) (hcls st) (db st);
  r_wl : Forall2 (pts h) (hwl st) (wl st);
  r_fv : forall f, pts h (floc s f) (fv st f);
  r_inp : pts h inp xs0;
  r_nd : NoDup (locs st)
}.

(** A write to the state leaves every scratch cell alone. *)
Definition keeps (st : astate) (h h' : heap) : Prop :=
  forall v xs, ~ In (vloc v) (locs st) -> pts h v xs -> pts h' v xs.

Lemma keeps_refl st h : keeps st h h.
Proof. intros ? ? _ H. exact H. Qed.

Lemma keeps_upd st h l c : In l (locs st) -> keeps st h (upd h l c).
Proof. intros Hl v xs Hv H. apply pts_upd_neq; [congruence | exact H]. Qed.

Lemma F2_upd_out h hs ls l c :
  ~ In l (map vloc hs) -> Forall2 (pts h) hs ls -> Forall2 (pts (upd h l c)) hs ls.
Proof.
  intros Hl H. induction H; constructor; auto.
  - apply pts_upd_neq; auto. intros E. apply Hl. left. auto.
  - apply IHForall2. intros Hi. apply Hl. now right.
Qed.

Lemma F2_upd_at h hs ls k v xs :
  NoDup (map vloc hs) -> nth_error hs k = Some v -> Forall2 (pts h) hs ls ->
  Forall2 (pts (upd h (vloc v) (existT cellof nat xs))) hs (lset ls k xs).
Proof.
  intros Hn Hk H. revert k Hk Hn. induction H as [|v' l ys ls Hp H IH]; intros k Hk Hn;
    [destruct k; discriminate|].
  inversion Hn as [|? ? Hv' Hn']; subst.
  destruct k as [|k]; cbn in Hk |- *.
  - injection Hk as ->. constructor; [apply pts_upd_eq|]. now apply F2_upd_out.
  - constructor; [|now apply IH].
    apply pts_upd_neq; [|exact Hp]. intros E. apply Hv'. rewrite E.
    apply in_map. eapply nth_error_In; eauto.
Qed.

Lemma F2_alloc h hs ls l : Forall2 (pts h) hs ls -> In l (map vloc hs) -> h l <> None.
Proof.
  intros H Hl. induction H; [destruct Hl|]. destruct Hl as [<- | Hl]; auto.
  unfold pts in H. congruence.
Qed.

(** The separation facts [r_nd] contains, one per kind of write. *)
Lemma locs_split st :
  NoDup (locs st) ->
  NoDup [vloc inp; vloc (clauses s); vloc (watches s)] /\
  NoDup (map (fun f => vloc (floc s f)) all_flds) /\
  NoDup (map vloc (hcls st)) /\ NoDup (map vloc (hwl st)) /\
  disj [vloc inp; vloc (clauses s); vloc (watches s)] (map (fun f => vloc (floc s f)) all_flds) /\
  disj [vloc inp; vloc (clauses s); vloc (watches s)] (map vloc (hcls st)) /\
  disj [vloc inp; vloc (clauses s); vloc (watches s)] (map vloc (hwl st)) /\
  disj (map (fun f => vloc (floc s f)) all_flds) (map vloc (hcls st)) /\
  disj (map (fun f => vloc (floc s f)) all_flds) (map vloc (hwl st)) /\
  disj (map vloc (hcls st)) (map vloc (hwl st)).
Proof.
  unfold locs. intros H.
  apply nodup_app_iff in H as (H0 & H & D0).
  apply nodup_app_iff in H as (H1 & H & D1).
  apply nodup_app_iff in H as (H2 & H3 & D2).
  repeat split; auto.
  all: intros x Ha Hb; first [ solve [apply (D2 x); auto; rewrite ?in_app_iff; tauto]
                            | solve [apply (D1 x); auto; rewrite ?in_app_iff; tauto]
                            | solve [apply (D0 x); auto; rewrite ?in_app_iff; tauto] ].
Qed.

Lemma floc_in f : In (vloc (floc s f)) (map (fun f => vloc (floc s f)) all_flds).
Proof. apply (in_map (fun f => vloc (floc s f))), in_all_flds. Qed.

Lemma locs_in_f st f : In (vloc (floc s f)) (locs st).
Proof. unfold locs. apply in_or_app. right. apply in_or_app. left. apply floc_in. Qed.

Lemma locs_in_c st k c : nth_error (hcls st) k = Some c -> In (vloc c) (locs st).
Proof.
  intros Hk. unfold locs. do 2 (apply in_or_app; right). apply in_or_app. left.
  apply in_map. eapply nth_error_In; eauto.
Qed.

Lemma locs_in_w st k c : nth_error (hwl st) k = Some c -> In (vloc c) (locs st).
Proof.
  intros Hk. unfold locs. do 3 (apply in_or_app; right).
  apply in_map. eapply nth_error_In; eauto.
Qed.

Lemma locs_in_cls st : In (vloc (clauses s)) (locs st).
Proof. unfold locs. cbn. tauto. Qed.

Lemma locs_in_wls st : In (vloc (watches s)) (locs st).
Proof. unfold locs. cbn. tauto. Qed.

Lemma repr_alloc h st l : repr h st -> In l (locs st) -> h l <> None.
Proof.
  intros R Hl. unfold locs in Hl.
  repeat match goal with H : In _ (_ ++ _) |- _ => apply in_app_or in H as [Hl|Hl] end.
  - destruct Hl as [<- | [<- | [<- | []]]].
    + pose proof (r_inp _ _ R) as E. unfold pts in E. congruence.
    + rewrite (r_cls _ _ R). discriminate.
    + rewrite (r_wls _ _ R). discriminate.
  - apply in_map_iff in Hl as (f & <- & _). pose proof (r_fv _ _ R f) as E. unfold pts in E. congruence.
  - eapply F2_alloc; [apply (r_db _ _ R) | exact Hl].
  - eapply F2_alloc; [apply (r_wl _ _ R) | exact Hl].
Qed.

Lemma repr_out h st l c : repr h st -> ~ In l (locs st) -> repr (upd h l c) st.
Proof.
  intros R Hl.
  assert (Hne : forall l', In l' (locs st) -> l' <> l) by (intros l' H E; subst; auto).
  destruct R as [Rc Rw Rd Rwl Rf Ri Rn]. constructor; auto.
  - rewrite upd_neq; auto. apply Hne, locs_in_cls.
  - rewrite upd_neq; auto. apply Hne, locs_in_wls.
  - apply F2_upd_out; auto. intros Hi. apply Hl. unfold locs.
    do 2 (apply in_or_app; right). apply in_or_app. auto.
  - apply F2_upd_out; auto. intros Hi. apply Hl. unfold locs. do 3 (apply in_or_app; right). auto.
  - intros f. apply pts_upd_neq; auto. apply Hne, locs_in_f.
  - apply pts_upd_neq; auto. apply Hne. unfold locs. cbn. tauto.
Qed.

Lemma repr_fset h st f xs :
  repr h st -> repr (upd h (vloc (floc s f)) (existT cellof nat xs)) (fset st f xs).
Proof.
  intros R. pose proof (locs_split _ (r_nd _ _ R)) as (N0 & N1 & N2 & N3 & D01 & D02 & D03 & D12 & D13 & D23).
  pose proof (floc_in f) as Hf.
  destruct R as [Rc Rw Rd Rwl Rf Ri Rn]. constructor; cbn.
  - rewrite upd_neq; auto. intros E. apply (D01 (vloc (clauses s))); cbn; auto. rewrite E. auto.
  - rewrite upd_neq; auto. intros E. apply (D01 (vloc (watches s))); cbn; auto. rewrite E. auto.
  - apply F2_upd_out; auto. intros Hi. apply (D12 _ Hf Hi).
  - apply F2_upd_out; auto. intros Hi. apply (D13 _ Hf Hi).
  - intros g. destruct (fld_eqb g f) eqn:E.
    + apply fld_eqb_eq in E as ->. apply pts_upd_eq.
    + apply pts_upd_neq; auto. intros E'.
      assert (g = f) by (eapply nodup_map_inj; eauto using in_all_flds).
      subst. now rewrite fld_eqb_refl in E.
  - apply pts_upd_neq; auto. intros E. apply (D01 (vloc inp)); cbn; auto. rewrite E. auto.
  - exact Rn.
Qed.

Lemma repr_dset h st k v xs :
  repr h st -> nth_error (hcls st) k = Some v ->
  repr (upd h (vloc v) (existT cellof nat xs)) (dset st (lset (db st) k xs)).
Proof.
  intros R Hk. pose proof (locs_split _ (r_nd _ _ R)) as (N0 & N1 & N2 & N3 & D01 & D02 & D03 & D12 & D13 & D23).
  assert (Hv : In (vloc v) (map vloc (hcls st))) by (apply in_map; eapply nth_error_In; eauto).
  destruct R as [Rc Rw Rd Rwl Rf Ri Rn]. constructor; cbn.
  - rewrite upd_neq; auto. intros E. apply (D02 (vloc (clauses s))); cbn; auto. rewrite E. auto.
  - rewrite upd_neq; auto. intros E. apply (D02 (vloc (watches s))); cbn; auto. rewrite E. auto.
  - apply F2_upd_at; auto.
  - apply F2_upd_out; auto. intros Hi. apply (D23 _ Hv Hi).
  - intros g. apply pts_upd_neq; auto. intros E. apply (D12 (vloc (floc s g))); [apply floc_in | rewrite E; auto].
  - apply pts_upd_neq; auto. intros E. apply (D02 (vloc inp)); cbn; auto. rewrite E. auto.
  - exact Rn.
Qed.

Lemma repr_wset h st k v xs :
  repr h st -> nth_error (hwl st) k = Some v ->
  repr (upd h (vloc v) (existT cellof nat xs)) (wset st (lset (wl st) k xs)).
Proof.
  intros R Hk. pose proof (locs_split _ (r_nd _ _ R)) as (N0 & N1 & N2 & N3 & D01 & D02 & D03 & D12 & D13 & D23).
  assert (Hv : In (vloc v) (map vloc (hwl st))) by (apply in_map; eapply nth_error_In; eauto).
  destruct R as [Rc Rw Rd Rwl Rf Ri Rn]. constructor; cbn.
  - rewrite upd_neq; auto. intros E. apply (D03 (vloc (clauses s))); cbn; auto. rewrite E. auto.
  - rewrite upd_neq; auto. intros E. apply (D03 (vloc (watches s))); cbn; auto. rewrite E. auto.
  - apply F2_upd_out; auto. intros Hi. apply (D23 _ Hi Hv).
  - apply F2_upd_at; auto.
  - intros g. apply pts_upd_neq; auto. intros E. apply (D13 (vloc (floc s g))); [apply floc_in | rewrite E; auto].
  - apply pts_upd_neq; auto. intros E. apply (D03 (vloc inp)); cbn; auto. rewrite E. auto.
  - exact Rn.
Qed.

Lemma nodup_snoc (l : list loc) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros H Hx. apply NoDup_app; auto; [constructor; auto; constructor|].
  intros a Ha [<- | []]. auto.
Qed.

Lemma locs_cpush st c cl : Permutation.Permutation (locs (cpush st c cl)) (locs st ++ [vloc c]).
Proof.
  unfold locs. cbn [hcls hwl cpush]. rewrite map_app. rewrite <- !app_assoc.
  do 2 apply Permutation.Permutation_app_head. apply Permutation.Permutation_app_head.
  apply Permutation.Permutation_app_comm.
Qed.

Lemma locs_wpush st c ws : Permutation.Permutation (locs (wpush st c ws)) (locs st ++ [vloc c]).
Proof. unfold locs. cbn [hcls hwl wpush]. rewrite map_app. now rewrite <- !app_assoc. Qed.

Lemma repr_cpush h st c cl :
  repr h st -> ~ In (vloc c) (locs st) -> pts h c cl ->
  repr (upd h (vloc (clauses s)) (existT cellof (vec nat) (hcls st ++ [c]))) (cpush st c cl).
Proof.
  intros R Hc Hp. pose proof (locs_split _ (r_nd _ _ R)) as (N0 & N1 & N2 & N3 & D01 & D02 & D03 & D12 & D13 & D23).
  assert (Hcl : vloc c <> vloc (clauses s)) by (intros E; apply Hc; rewrite E; apply locs_in_cls).
  assert (Hne : forall l', In l' (locs st) -> l' <> vloc (clauses s) -> l' <> vloc (clauses s)) by auto.
  assert (Ho : forall l, In l (map (fun f => vloc (floc s f)) all_flds ++ map vloc (hcls st) ++ map vloc (hwl st))
                 -> l <> vloc (clauses s)).
  { intros l Hl E. subst. repeat (apply in_app_or in Hl as [Hl|Hl]).
    - apply (D01 (vloc (clauses s))); cbn; auto.
    - apply (D02 (vloc (clauses s))); cbn; auto.
    - apply (D03 (vloc (clauses s))); cbn; auto. }
  destruct R as [Rc Rw Rd Rwl Rf Ri Rn]. constructor; cbn.
  - apply upd_eq.
  - rewrite upd_neq; [exact Rw|]. intros E. inversion N0 as [|? ? _ N0']; subst.
    inversion N0' as [|? ? Hn _]; subst. apply Hn. rewrite E. cbn. auto.
  - apply Forall2_app; [| constructor; [| constructor]].
    + apply F2_upd_out; auto. intros Hi. apply (Ho (vloc (clauses s))); auto.
      apply in_or_app. right. apply in_or_app. auto.
    + apply pts_upd_neq; auto.
  - apply F2_upd_out; auto. intros Hi. apply (Ho (vloc (clauses s))); auto.
    do 2 (apply in_or_app; right). auto.
  - intros g. apply pts_upd_neq; auto. apply Ho. apply in_or_app. left. apply floc_in.
  - apply pts_upd_neq; auto. intros E. inversion N0 as [|? ? Hn _]; subst. apply Hn. rewrite E. cbn. auto.
  - eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_sym, (locs_cpush st c cl) | now apply nodup_snoc].
Qed.

Lemma repr_wpush h st c ws :
  repr h st -> ~ In (vloc c) (locs st) -> pts h c ws ->
  repr (upd h (vloc (watches s)) (existT cellof (vec nat) (hwl st ++ [c]))) (wpush st c ws).
Proof.
  intros R Hc Hp. pose proof (locs_split _ (r_nd _ _ R)) as (N0 & N1 & N2 & N3 & D01 & D02 & D03 & D12 & D13 & D23).
  assert (Hcl : vloc c <> vloc (watches s)) by (intros E; apply Hc; rewrite E; apply locs_in_wls).
  assert (Ho : forall l, In l (map (fun f => vloc (floc s f)) all_flds ++ map vloc (hcls st) ++ map vloc (hwl st))
                 -> l <> vloc (watches s)).
  { intros l Hl E. subst. repeat (apply in_app_or in Hl as [Hl|Hl]).
    - apply (D01 (vloc (watches s))); cbn; auto.
    - apply (D02 (vloc (watches s))); cbn; auto.
    - apply (D03 (vloc (watches s))); cbn; auto. }
  destruct R as [Rc Rw Rd Rwl Rf Ri Rn]. constructor; cbn.
  - rewrite upd_neq; [exact Rc|]. intros E. inversion N0 as [|? ? _ N0']; subst.
    inversion N0' as [|? ? Hn _]; subst. apply Hn. rewrite E. cbn. auto.
  - apply upd_eq.
  - apply F2_upd_out; auto. intros Hi. apply (Ho (vloc (watches s))); auto.
    apply in_or_app. right. apply in_or_app. auto.
  - apply Forall2_app; [| constructor; [| constructor]].
    + apply F2_upd_out; auto. intros Hi. apply (Ho (vloc (watches s))); auto.
      do 2 (apply in_or_app; right). auto.
    + apply pts_upd_neq; auto.
  - intros g. apply pts_upd_neq; auto. apply Ho. apply in_or_app. left. apply floc_in.
  - apply pts_upd_neq; auto. intros E. inversion N0 as [|? ? Hn _]; subst. apply Hn. rewrite E. cbn. auto.
  - eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_sym, (locs_wpush st c ws) | now apply nodup_snoc].
Qed.

Lemma repr_cl h st k c :
  repr h st -> nth_error (hcls st) k = Some c -> exists cl, nth_error (db st) k = Some cl /\ pts h c cl.
Proof. intros R Hk. eapply Forall2_nth; [apply (r_db _ _ R) | exact Hk]. Qed.

Lemma repr_w h st k c :
  repr h st -> nth_error (hwl st) k = Some c -> exists ws, nth_error (wl st) k = Some ws /\ pts h c ws.
Proof. intros R Hk. eapply Forall2_nth; [apply (r_wl _ _ R) | exact Hk]. Qed.

Lemma repr_len_db h st : repr h st -> length (hcls st) = length (db st).
Proof. intros R. eapply Forall2_length, r_db, R. Qed.

Lemma repr_len_wl h st : repr h st -> length (hwl st) = length (wl st).
Proof. intros R. eapply Forall2_length, r_wl, R. Qed.

(** * Events on cells *)

Lemma wp_get_pts h v xs i (Q : nat -> heap -> Prop) :
  pts h v xs -> (forall x, nth_error xs i = Some x -> Q x h) -> wp (vget (E := vecE) v i) Q h.
Proof. intros Hp HQ. apply wp_vget. intros ys x Hy Hx. rewrite (cell_inj _ _ _ _ Hy Hp) in Hx. auto. Qed.

Lemma wp_len_pts h v xs (Q : nat -> heap -> Prop) :
  pts h v xs -> Q (length xs) h -> wp (vlen (E := vecE) v) Q h.
Proof. intros Hp HQ. apply wp_vlen. intros ys Hy. now rewrite (cell_inj _ _ _ _ Hy Hp). Qed.

Lemma wp_set_pts h v xs i x (Q : unit -> heap -> Prop) :
  pts h v xs -> (i < length xs -> Q tt (upd h (vloc v) (existT cellof nat (lset xs i x)))) ->
  wp (vset (E := vecE) v i x) Q h.
Proof. intros Hp HQ. apply wp_vset. intros ys Hy. rewrite (cell_inj _ _ _ _ Hy Hp). auto. Qed.

Lemma wp_push_pts h v xs x (Q : unit -> heap -> Prop) :
  pts h v xs -> Q tt (upd h (vloc v) (existT cellof nat (xs ++ [x]))) ->
  wp (vpush (E := vecE) v x) Q h.
Proof. intros Hp HQ. apply wp_vpush. intros ys Hy. now rewrite (cell_inj _ _ _ _ Hy Hp). Qed.

Lemma wp_shrink_pts h v xs n (Q : unit -> heap -> Prop) :
  pts h v xs -> (n <= length xs -> Q tt (upd h (vloc v) (existT cellof nat (firstn n xs)))) ->
  wp (vshrink (E := vecE) v n) Q h.
Proof. intros Hp HQ. apply wp_vshrink. intros ys Hy. rewrite (cell_inj _ _ _ _ Hy Hp). auto. Qed.

(** * Events on the state *)

Section Ev.
Variables (h : heap) (st : astate).
Hypothesis R : repr h st.

Lemma get_f f i Q :
  (forall x, nth_error (fv st f) i = Some x -> Q x h) -> wp (vget (floc s f) i) Q h.
Proof. apply wp_get_pts, (r_fv _ _ R). Qed.

Lemma len_f f Q : Q (length (fv st f)) h -> wp (vlen (floc s f)) Q h.
Proof. apply wp_len_pts, (r_fv _ _ R). Qed.

Lemma set_f f i x Q :
  (forall h', i < length (fv st f) -> repr h' (fset st f (lset (fv st f) i x)) -> keeps st h h' -> Q tt h') ->
  wp (vset (floc s f) i x) Q h.
Proof.
  intros HQ. eapply wp_set_pts; [apply (r_fv _ _ R)|]. intros Hi. apply HQ; auto.
  - now apply repr_fset.
  - apply keeps_upd, locs_in_f.
Qed.

Lemma push_f f x Q :
  (forall h', repr h' (fset st f (fv st f ++ [x])) -> keeps st h h' -> Q tt h') ->
  wp (vpush (floc s f) x) Q h.
Proof.
  intros HQ. eapply wp_push_pts; [apply (r_fv _ _ R)|]. apply HQ.
  - now apply repr_fset.
  - apply keeps_upd, locs_in_f.
Qed.

Lemma shrink_f f n Q :
  (forall h', n <= length (fv st f) -> repr h' (fset st f (firstn n (fv st f))) -> keeps st h h' -> Q tt h') ->
  wp (vshrink (floc s f) n) Q h.
Proof.
  intros HQ. eapply wp_shrink_pts; [apply (r_fv _ _ R)|]. intros Hn. apply HQ; auto.
  - now apply repr_fset.
  - apply keeps_upd, locs_in_f.
Qed.

Lemma get_hc i (Q : vec nat -> heap -> Prop) :
  (forall c, nth_error (hcls st) i = Some c -> Q c h) -> wp (vget (clauses s) i) Q h.
Proof. intros HQ. apply wp_vget. intros ys x Hy Hx. rewrite (cell_inj _ _ _ _ Hy (r_cls _ _ R)) in Hx. auto. Qed.

Lemma len_hc Q : Q (length (db st)) h -> wp (vlen (clauses s)) Q h.
Proof.
  intros HQ. apply wp_vlen. intros ys Hy. rewrite (cell_inj _ _ _ _ Hy (r_cls _ _ R)).
  now rewrite (repr_len_db _ _ R).
Qed.

Lemma get_hw i (Q : vec nat -> heap -> Prop) :
  (forall c, nth_error (hwl st) i = Some c -> Q c h) -> wp (vget (watches s) i) Q h.
Proof. intros HQ. apply wp_vget. intros ys x Hy Hx. rewrite (cell_inj _ _ _ _ Hy (r_wls _ _ R)) in Hx. auto. Qed.

Lemma get_cl k c cl i Q :
  nth_error (hcls st) k = Some c -> nth_error (db st) k = Some cl ->
  (forall x, nth_error cl i = Some x -> Q x h) -> wp (vget c i) Q h.
Proof.
  intros Hk Hd. destruct (repr_cl _ _ _ _ R Hk) as (cl' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply wp_get_pts.
Qed.

Lemma len_cl k c cl Q :
  nth_error (hcls st) k = Some c -> nth_error (db st) k = Some cl -> Q (length cl) h -> wp (vlen c) Q h.
Proof.
  intros Hk Hd. destruct (repr_cl _ _ _ _ R Hk) as (cl' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply wp_len_pts.
Qed.

Lemma set_cl k c cl i x Q :
  nth_error (hcls st) k = Some c -> nth_error (db st) k = Some cl ->
  (forall h', i < length cl -> repr h' (dset st (lset (db st) k (lset cl i x))) -> keeps st h h' -> Q tt h') ->
  wp (vset c i x) Q h.
Proof.
  intros Hk Hd HQ. destruct (repr_cl _ _ _ _ R Hk) as (cl' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply wp_set_pts; [exact Hp|]. intros Hi. apply HQ; auto.
  - now apply repr_dset.
  - eapply keeps_upd, locs_in_c; eauto.
Qed.

Lemma get_w k c ws i Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws ->
  (forall x, nth_error ws i = Some x -> Q x h) -> wp (vget c i) Q h.
Proof.
  intros Hk Hd. destruct (repr_w _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply wp_get_pts.
Qed.

Lemma len_w k c ws Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws -> Q (length ws) h -> wp (vlen c) Q h.
Proof.
  intros Hk Hd. destruct (repr_w _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-. now apply wp_len_pts.
Qed.

Lemma set_w k c ws i x Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws ->
  (forall h', i < length ws -> repr h' (wset st (lset (wl st) k (lset ws i x))) -> keeps st h h' -> Q tt h') ->
  wp (vset c i x) Q h.
Proof.
  intros Hk Hd HQ. destruct (repr_w _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply wp_set_pts; [exact Hp|]. intros Hi. apply HQ; auto.
  - now apply repr_wset.
  - eapply keeps_upd, locs_in_w; eauto.
Qed.

Lemma push_w k c ws x Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws ->
  (forall h', repr h' (wset st (lset (wl st) k (ws ++ [x]))) -> keeps st h h' -> Q tt h') ->
  wp (vpush c x) Q h.
Proof.
  intros Hk Hd HQ. destruct (repr_w _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply wp_push_pts; [exact Hp|]. apply HQ.
  - now apply repr_wset.
  - eapply keeps_upd, locs_in_w; eauto.
Qed.

Lemma shrink_w k c ws n Q :
  nth_error (hwl st) k = Some c -> nth_error (wl st) k = Some ws ->
  (forall h', n <= length ws -> repr h' (wset st (lset (wl st) k (firstn n ws))) -> keeps st h h' -> Q tt h') ->
  wp (vshrink c n) Q h.
Proof.
  intros Hk Hd HQ. destruct (repr_w _ _ _ _ R Hk) as (ws' & Hd' & Hp).
  rewrite Hd in Hd'. injection Hd' as <-.
  eapply wp_shrink_pts; [exact Hp|]. intros Hn. apply HQ; auto.
  - now apply repr_wset.
  - eapply keeps_upd, locs_in_w; eauto.
Qed.

(** A fresh vector is a scratch cell. *)
Lemma make_scr n (x : nat) Q :
  (forall v h', ~ In (vloc v) (locs st) -> pts h' v (repeat x n) -> repr h' st -> keeps st h h' ->
     (forall v' xs, pts h v' xs -> pts h' v' xs) -> vloc v <> vloc inp -> Q v h') ->
  wp (vmake (E := vecE) n x) Q h.
Proof.
  intros HQ. apply wp_vmake. intros v Hv.
  assert (Hn : ~ In (vloc v) (locs st)) by (intros Hi; exact (repr_alloc _ _ _ R Hi Hv)).
  apply HQ; auto.
  - apply pts_upd_eq.
  - now apply repr_out.
  - intros v' xs _ Hp. apply pts_upd_neq; [|exact Hp]. unfold pts in Hp. congruence.
  - intros v' xs Hp. apply pts_upd_neq; [|exact Hp]. unfold pts in Hp. congruence.
  - intros E. apply Hn. rewrite E. unfold locs. cbn. auto.
Qed.

Lemma set_scr v xs i x Q :
  ~ In (vloc v) (locs st) -> pts h v xs ->
  (forall h', i < length xs -> repr h' st -> pts h' v (lset xs i x) ->
     (forall v' ys, vloc v' <> vloc v -> pts h v' ys -> pts h' v' ys) -> Q tt h') ->
  wp (vset v i x) Q h.
Proof.
  intros Hn Hp HQ. eapply wp_set_pts; [exact Hp|]. intros Hi. apply HQ; auto.
  - now apply repr_out.
  - apply pts_upd_eq.
  - intros. now apply pts_upd_neq.
Qed.

Lemma push_scr v xs x Q :
  ~ In (vloc v) (locs st) -> pts h v xs ->
  (forall h', repr h' st -> pts h' v (xs ++ [x]) ->
     (forall v' ys, vloc v' <> vloc v -> pts h v' ys -> pts h' v' ys) -> Q tt h') ->
  wp (vpush v x) Q h.
Proof.
  intros Hn Hp HQ. eapply wp_push_pts; [exact Hp|]. apply HQ; auto.
  - now apply repr_out.
  - apply pts_upd_eq.
  - intros. now apply pts_upd_neq.
Qed.

Lemma push_cls c cl Q :
  ~ In (vloc c) (locs st) -> pts h c cl ->
  (forall h', repr h' (cpush st c cl) -> Q tt h') -> wp (vpush (clauses s) c) Q h.
Proof.
  intros Hn Hp HQ. apply wp_vpush. intros ys Hy. rewrite (cell_inj _ _ _ _ Hy (r_cls _ _ R)).
  apply HQ. now apply repr_cpush.
Qed.

Lemma push_wls c ws Q :
  ~ In (vloc c) (locs st) -> pts h c ws ->
  (forall h', repr h' (wpush st c ws) -> Q tt h') -> wp (vpush (watches s) c) Q h.
Proof.
  intros Hn Hp HQ. apply wp_vpush. intros ys Hy. rewrite (cell_inj _ _ _ _ Hy (r_wls _ _ R)).
  apply HQ. now apply repr_wpush.
Qed.

Lemma get_inp i Q : (forall x, nth_error xs0 i = Some x -> Q x h) -> wp (vget inp i) Q h.
Proof. apply wp_get_pts, (r_inp _ _ R). Qed.

End Ev.
End Repr.
