(** SAT soundness of [Solver.solve]: when it answers "satisfiable", the
    formula it was given has a model.

    The answer is only given after [check_model] has found a true literal
    in every clause of [input], so the proof needs two things.
    [check_model_spec] says what that check means.  The frame invariant
    [Fr] says that nothing between loading and checking writes to [input]:
    the search writes only to the state's own vectors, to clause vectors it
    reads out of [clauses], and to watch lists it reads out of [watches], so
    it is enough that none of those is [input] (or either of the two
    vectors of handles, whose contents say which vectors are which).
    Nothing here constrains the search otherwise; UNSAT soundness needs the
    real invariants. *)
From Stdlib Require Import List PeanoNat Lia Bool.
From Crane Require Import Monads.ITree.
Require Import SatVec VecSem Solver.
Import ListNotations.
Import Solver.

(** * The formula the input encodes *)

(** Literal [2v] says variable [v] is true, [2v+1] that it is false. *)
Definition lit_true (val : nat -> bool) (l : nat) : Prop := val (lvar l) = Nat.even l.

Definition satisfies (val : nat -> bool) (F : list (list nat)) : Prop :=
  Forall (Exists (lit_true val)) F.

(** [encodes xs n pos F]: from position [pos], up to [n], [xs] holds the
    clauses [F], each as its length followed by its literals. *)
Inductive encodes (xs : list nat) (n : nat) : nat -> list (list nat) -> Prop :=
| enc_nil pos : n <= pos -> encodes xs n pos []
| enc_cons pos c F :
    pos < n -> nth_error xs pos = Some (length c) ->
    (forall j, j < length c -> nth_error xs (pos + 1 + j) = nth_error c j) ->
    encodes xs n (pos + 1 + length c) F ->
    encodes xs n pos (c :: F).

(** * The frame *)

(** Spelled out so that [existT] does not put [vec nat] in [Set]. *)
Local Notation cellof := (fun T : Type => list T).

(** The location [l] holds a list of [nat]s. *)
Definition natcell (h : heap) (l : loc) : Prop := exists xs, h l = Some (existT cellof nat xs).

Lemma natcell_write_nat h l a ys : natcell h a -> natcell (upd h l (existT cellof nat ys)) a.
Proof.
  intros Ha. destruct (Nat.eq_dec a l) as [-> | Hne].
  - exists ys. apply upd_eq.
  - destruct Ha as [xs Ha]. exists xs. now rewrite upd_neq.
Qed.

Lemma natcell_write_other h l a c : a <> l -> natcell h a -> natcell (upd h l c) a.
Proof. intros Hne [xs Ha]. exists xs. now rewrite upd_neq. Qed.

Lemma natcell_fresh h l a c : h l = None -> natcell h a -> natcell (upd h l c) a.
Proof. intros Hl [xs Ha]. apply natcell_write_other; [congruence | now exists xs]. Qed.

Section Frame.
Variables (inp db wl : loc) (xs0 : list nat).
Hypotheses (Hid : inp <> db) (Hiw : inp <> wl) (Hdw : db <> wl).

(** A location the search may write to. *)
Definition good (l : loc) : Prop := l <> inp /\ l <> db /\ l <> wl.

Definition handles (h : heap) (l : loc) : Prop :=
  exists ds : list (vec nat),
    h l = Some (existT cellof (vec nat) ds) /\ Forall (fun c => good (vloc c)) ds.

Definition frame (h : heap) : Prop :=
  h inp = Some (existT cellof nat xs0) /\ handles h db /\ handles h wl.

Lemma frame_write h l c : frame h -> good l -> frame (upd h l c).
Proof.
  intros (Hi & (ds & Hd & Fd) & (ws & Hw & Fw)) (N1 & N2 & N3).
  split; [|split].
  - rewrite upd_neq by congruence. exact Hi.
  - exists ds. rewrite upd_neq by congruence. auto.
  - exists ws. rewrite upd_neq by congruence. auto.
Qed.

Lemma frame_fresh h l : frame h -> h l = None -> good l.
Proof.
  intros (Hi & (ds & Hd & _) & (ws & Hw & _)) Hl.
  repeat split; intros ->; congruence.
Qed.

Lemma frame_push h l ds c :
  frame h -> (l = db \/ l = wl) -> h l = Some (existT cellof (vec nat) ds) ->
  good (vloc c) -> frame (upd h l (existT cellof (vec nat) (ds ++ [c]))).
Proof.
  intros (Hi & (ds1 & Hd & Fd) & (ws1 & Hw & Fw)) Hl Hds Hc.
  destruct Hl as [-> | ->]; split; [| split | | split].
  - rewrite upd_neq by congruence. exact Hi.
  - exists (ds ++ [c]). rewrite upd_eq. split; [reflexivity|].
    rewrite (cell_inj _ _ _ _ Hd Hds) in Fd. apply Forall_app. auto.
  - exists ws1. rewrite upd_neq by congruence. auto.
  - rewrite upd_neq by congruence. exact Hi.
  - exists ds1. rewrite upd_neq by congruence. auto.
  - exists (ds ++ [c]). rewrite upd_eq. split; [reflexivity|].
    rewrite (cell_inj _ _ _ _ Hw Hds) in Fw. apply Forall_app. auto.
Qed.

Lemma frame_get h l ds i c :
  frame h -> (l = db \/ l = wl) -> h l = Some (existT cellof (vec nat) ds) ->
  nth_error ds i = Some c -> good (vloc c).
Proof.
  intros (_ & (ds1 & Hd & Fd) & (ws1 & Hw & Fw)) Hl Hds Hi.
  apply nth_error_In in Hi.
  destruct Hl as [-> | ->].
  - rewrite (cell_inj _ _ _ _ Hd Hds), Forall_forall in Fd. auto.
  - rewrite (cell_inj _ _ _ _ Hw Hds), Forall_forall in Fw. auto.
Qed.

Lemma frame_make {A} n (x : A) (Q : vec A -> heap -> Prop) h :
  frame h ->
  (forall v h', frame h' -> good (vloc v) ->
     h' (vloc v) = Some (existT cellof A (repeat x n)) ->
     (forall a, natcell h a -> natcell h' a) -> Q v h') ->
  wp (vmake (E := vecE) n x) Q h.
Proof.
  intros Hf HQ. apply wp_vmake. intros v Hv.
  assert (good (vloc v)) by (eapply frame_fresh; eauto).
  apply HQ; auto.
  - now apply frame_write.
  - apply upd_eq.
  - intros a. now apply natcell_fresh.
Qed.

Lemma fresh_vecs_frame fuel : forall (acc : vec (vec nat)) n Q h,
  frame h -> vloc acc = wl ->
  (forall x h', frame h' -> Q x h') ->
  wp (fresh_vecs fuel acc n) Q h.
Proof.
  induction fuel as [|f IH]; intros acc n Q h Hf Hacc HQ; cbn [fresh_vecs].
  - apply wp_vabort.
  - destruct n as [|n].
    + apply wp_ret, HQ; auto.
    + apply wp_bind. apply frame_make; [assumption|].
      intros w h1 Hf1 Hw _ Hn1. apply wp_bind, wp_vpush. intros ds Hds.
      eapply IH; [eapply frame_push; eauto | assumption | exact HQ].
Qed.

End Frame.

(** * The search keeps to the frame *)

Section Search.
Variables (s : state) (inp : vec nat) (xs0 : list nat).

Local Notation G l := (good (vloc inp) (vloc (clauses s)) (vloc (watches s)) l).

Hypotheses (Hid : vloc inp <> vloc (clauses s)) (Hiw : vloc inp <> vloc (watches s))
           (Hdw : vloc (clauses s) <> vloc (watches s)).
Hypotheses (Gasg : G (vloc (assigns s))) (Glvl : G (vloc (level s)))
           (Grsn : G (vloc (reason s))) (Gph : G (vloc (phase s)))
           (Gst : G (vloc (stamp s))) (Gsn : G (vloc (seen s)))
           (Gtr : G (vloc (trail s))) (Gtl : G (vloc (trail_lim s)))
           (Gm : G (vloc (misc s))).

Definition Fr (h : heap) : Prop :=
  frame (vloc inp) (vloc (clauses s)) (vloc (watches s)) xs0 h /\
  natcell h (vloc (assigns s)).

Lemma fr_set (v : vec nat) i x Q h :
  Fr h -> G (vloc v) -> (forall h', Fr h' -> Q tt h') -> wp (vset (E := vecE) v i x) Q h.
Proof.
  intros [Hf Hn] Hg HQ. apply wp_vset. intros xs _ _. apply HQ. split.
  - now apply frame_write.
  - now apply natcell_write_nat.
Qed.

Lemma fr_push (v : vec nat) x Q h :
  Fr h -> G (vloc v) -> (forall h', Fr h' -> Q tt h') -> wp (vpush (E := vecE) v x) Q h.
Proof.
  intros [Hf Hn] Hg HQ. apply wp_vpush. intros xs _. apply HQ. split.
  - now apply frame_write.
  - now apply natcell_write_nat.
Qed.

Lemma fr_shrink (v : vec nat) n Q h :
  Fr h -> G (vloc v) -> (forall h', Fr h' -> Q tt h') -> wp (vshrink (E := vecE) v n) Q h.
Proof.
  intros [Hf Hn] Hg HQ. apply wp_vshrink. intros xs _ _. apply HQ. split.
  - now apply frame_write.
  - now apply natcell_write_nat.
Qed.

Lemma fr_get (v : vec nat) i (Q : nat -> heap -> Prop) h :
  (forall x, Q x h) -> wp (vget (E := vecE) v i) Q h.
Proof. intros HQ. apply wp_vget. auto. Qed.

(** Reading a handle out of [clauses] or [watches] gives one the search may
    write to. *)
Lemma fr_get_handle (v : vec (vec nat)) i Q h :
  Fr h -> (vloc v = vloc (clauses s) \/ vloc v = vloc (watches s)) ->
  (forall c, G (vloc c) -> Q c h) -> wp (vget (E := vecE) v i) Q h.
Proof.
  intros [Hf _] Hv HQ. apply wp_vget. intros xs x Hx Hi. apply HQ.
  eapply frame_get; eauto.
Qed.

Lemma fr_len {A} (v : vec A) (Q : nat -> heap -> Prop) h :
  (forall n, Q n h) -> wp (vlen (E := vecE) v) Q h.
Proof. intros HQ. apply wp_vlen. auto. Qed.

Lemma fr_make n (x : nat) Q h :
  Fr h -> (forall v h', Fr h' -> G (vloc v) -> Q v h') -> wp (vmake (E := vecE) n x) Q h.
Proof.
  intros [Hf Hn] HQ. apply wp_vmake. intros v Hv. apply HQ.
  - split.
    + apply frame_write; [assumption|]. eapply frame_fresh; eauto.
    + now apply natcell_fresh.
  - eapply frame_fresh; eauto.
Qed.

Lemma fr_push_handle (v : vec (vec nat)) c Q h :
  Fr h -> vloc v = vloc (clauses s) -> G (vloc c) ->
  (forall h', Fr h' -> Q tt h') -> wp (vpush (E := vecE) v c) Q h.
Proof.
  intros [Hf Hn] Hv Hc HQ. apply wp_vpush. intros xs Hx. apply HQ. split.
  - eapply frame_push; eauto.
  - rewrite Hv. apply natcell_write_other; [apply Gasg | assumption].
Qed.

(** Calls to the loops proved below; extended as each one is. *)
Ltac fr_call := fail.

Ltac fr_step :=
  match goal with
  | |- wp (ITree.bind _ _) _ _ => apply wp_bind
  | |- wp (Ret _) _ _ => apply wp_ret
  | |- wp (vabort _) _ _ => apply wp_vabort
  | |- wp (vlen _) _ _ => apply fr_len; intros
  | |- wp (vget _ _) _ _ =>
    apply fr_get_handle; [assumption | first [left; reflexivity | right; reflexivity] | intros ? ?]
  | |- wp (vget _ _) _ _ => apply fr_get; intros
  | |- wp (vset _ _ _) _ _ => apply fr_set; [assumption | assumption | intros ? ?]
  | |- wp (vpush _ _) _ _ =>
    apply fr_push_handle; [assumption | reflexivity | assumption | intros ? ?]
  | |- wp (vpush _ _) _ _ => apply fr_push; [assumption | assumption | intros ? ?]
  | |- wp (vshrink _ _) _ _ => apply fr_shrink; [assumption | assumption | intros ? ?]
  | |- wp (vmake _ _) _ _ => apply fr_make; [assumption | intros ? ? ? ?]
  | |- wp (lit_value _ _) _ _ => unfold lit_value
  | |- wp (decision_level _) _ _ => unfold decision_level
  | |- wp (enqueue _ _ _) _ _ => unfold enqueue
  | |- wp (backtrack _ _ _) _ _ => unfold backtrack
  | |- wp (attach _ _ _) _ _ => unfold attach
  | |- wp (learn _ _ _) _ _ => unfold learn
  | |- wp (let _ := _ in _) _ _ => cbv zeta
  | |- wp (match ?x with _ => _ end) _ _ => destruct x
  | H : forall x h', Fr h' -> ?Q x h' |- ?Q _ _ => apply H; assumption
  | |- wp _ _ _ => fr_call
  end.

Ltac fr_go := repeat (cbv beta; fr_step).

Lemma find_watch_fr fuel : forall c k len Q h,
  Fr h -> (forall x h', Fr h' -> Q x h') -> wp (find_watch s fuel c k len) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [find_watch]; fr_go; try solve [eapply IH; eauto]. Qed.

Lemma copy_rest_fr fuel : forall ws i j n Q h,
  Fr h -> G (vloc ws) -> (forall x h', Fr h' -> Q x h') -> wp (copy_rest fuel ws i j n) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [copy_rest]; fr_go; try solve [eapply IH; eauto]. Qed.

Ltac fr_call ::=
  first [ eapply find_watch_fr; [assumption | intros ? ? ?]
        | eapply copy_rest_fr; [assumption | assumption | intros ? ? ?] ].

Lemma prop_watch_fr fuel : forall fl ws i j n Q h,
  Fr h -> G (vloc ws) -> (forall x h', Fr h' -> Q x h') -> wp (prop_watch s fuel fl ws i j n) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [prop_watch]; fr_go; try solve [eapply IH; eauto]. Qed.

Ltac fr_call ::=
  first [ eapply find_watch_fr; [assumption | intros ? ? ?]
        | eapply copy_rest_fr; [assumption | assumption | intros ? ? ?]
        | eapply prop_watch_fr; [assumption | assumption | intros ? ? ?] ].

Lemma propagate_fr fuel : forall Q h,
  Fr h -> (forall x h', Fr h' -> Q x h') -> wp (propagate s fuel) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [propagate]; fr_go; try solve [eapply IH; eauto]. Qed.

Lemma unassign_fr fuel : forall i lim Q h,
  Fr h -> (forall x h', Fr h' -> Q x h') -> wp (unassign s fuel i lim) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [unassign]; fr_go; try solve [eapply IH; eauto]. Qed.

Lemma analyze_lits_fr fuel : forall c j len dl pathC learnt now Q h,
  Fr h -> G (vloc learnt) -> (forall x h', Fr h' -> Q x h') ->
  wp (analyze_lits s fuel c j len dl pathC learnt now) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [analyze_lits]; fr_go; try solve [eapply IH; eauto]. Qed.

Lemma next_seen_fr fuel : forall i Q h,
  Fr h -> (forall x h', Fr h' -> Q x h') -> wp (next_seen s fuel i) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [next_seen]; fr_go; try solve [eapply IH; eauto]. Qed.

Ltac fr_call ::=
  first [ eapply analyze_lits_fr; [assumption | assumption | intros ? ? ?]
        | eapply next_seen_fr; [assumption | intros ? ? ?] ].

Lemma analyze_loop_fr fuel : forall confl start index pathC dl learnt now Q h,
  Fr h -> G (vloc learnt) -> (forall x h', Fr h' -> Q x h') ->
  wp (analyze_loop s fuel confl start index pathC dl learnt now) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [analyze_loop]; fr_go; try solve [eapply IH; eauto]. Qed.

Lemma finish_learnt_fr fuel : forall learnt i len best bestlv Q h,
  Fr h -> G (vloc learnt) -> (forall x h', Fr h' -> Q x h') ->
  wp (finish_learnt s fuel learnt i len best bestlv) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [finish_learnt]; fr_go; try solve [eapply IH; eauto]. Qed.

Lemma pick_fr fuel : forall v n best beststamp Q h,
  Fr h -> (forall x h', Fr h' -> Q x h') -> wp (pick s fuel v n best beststamp) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [pick]; fr_go; try solve [eapply IH; eauto]. Qed.

Ltac fr_call ::=
  first [ eapply propagate_fr; [assumption | intros ? ? ?]
        | eapply unassign_fr; [assumption | intros ? ? ?]
        | eapply analyze_loop_fr; [assumption | assumption | intros ? ? ?]
        | eapply finish_learnt_fr; [assumption | assumption | intros ? ? ?]
        | eapply pick_fr; [assumption | intros ? ? ?] ].

(** [search] also answers only 0, 1 or 2. *)
Lemma search_fr fuel budget : forall nvars Q h,
  Fr h -> (forall x h', Fr h' -> x <= 2 -> Q x h') -> wp (search s fuel budget nvars) Q h.
Proof.
  induction budget as [|b IH]; intros nvars Q h Hf HQ; cbn [search].
  - apply wp_ret. auto.
  - fr_go; try solve [ apply HQ; [assumption | lia] | eapply IH; eauto ].
Qed.

Lemma read_lits_fr fuel : forall input c pos len Q h,
  Fr h -> G (vloc c) -> (forall x h', Fr h' -> Q x h') -> wp (read_lits fuel input c pos len) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [read_lits]; fr_go; try solve [eapply IH; eauto]. Qed.

Ltac fr_call ::= eapply read_lits_fr; [assumption | assumption | intros ? ? ?].

Lemma load_fr fuel : forall input pos n Q h,
  Fr h -> (forall x h', Fr h' -> Q x h') -> wp (load s fuel input pos n) Q h.
Proof. induction fuel as [|f IH]; intros; cbn [load]; fr_go; try solve [eapply IH; eauto]. Qed.

(** * What the model check means *)

(** The assignment as a valuation: unassigned variables are false. *)
Definition val_of (asl : list nat) (v : nat) : bool := Nat.eqb (nth v asl 0) 1.

Lemma lit_value_spec l asl (Q : nat -> heap -> Prop) h :
  h (vloc (assigns s)) = Some (existT cellof nat asl) ->
  (forall n, (n = 1 -> lit_true (val_of asl) l) -> Q n h) ->
  wp (lit_value s l) Q h.
Proof.
  intros Ha HQ. unfold lit_value. apply wp_bind, wp_vget. intros xs a Hx Hi.
  rewrite (cell_inj _ _ _ _ Hx Ha) in Hi. apply wp_ret, HQ. intros Hn.
  unfold lit_true, val_of. rewrite (nth_error_nth _ _ 0 Hi).
  pose proof (Nat.mod_upper_bound l 2) as Hm.
  pose proof (Nat.div_mod_eq l 2) as Hd.
  destruct (Nat.eqb_spec a 0); [discriminate|].
  destruct (Nat.eqb_spec (l mod 2) 0) as [E|E].
  - subst a. replace l with (2 * (l / 2)) by lia.
    rewrite Nat.even_mul. reflexivity.
  - assert (a = 2) by lia. subst a.
    replace l with (2 * (l / 2) + 1) by lia.
    rewrite Nat.even_add, Nat.even_mul. reflexivity.
Qed.

Lemma clause_sat_spec fuel : forall pos c asl Q h,
  h (vloc (assigns s)) = Some (existT cellof nat asl) ->
  h (vloc inp) = Some (existT cellof nat xs0) ->
  (forall j, j < length c -> nth_error xs0 (pos + j) = nth_error c j) ->
  (forall b, (b = true -> Exists (lit_true (val_of asl)) c) -> Q b h) ->
  wp (clause_sat s fuel inp pos (length c)) Q h.
Proof.
  induction fuel as [|f IH]; intros pos c asl Q h Ha Hi Hc HQ; cbn [clause_sat].
  - apply wp_vabort.
  - destruct c as [|l c]; cbn [length].
    + apply wp_ret, HQ. discriminate.
    + apply wp_bind, wp_vget. intros xs x Hx Hn.
      rewrite (cell_inj _ _ _ _ Hx Hi) in Hn.
      assert (x = l) as ->.
      { specialize (Hc 0). rewrite Nat.add_0_r in Hc. cbn in Hc.
        rewrite Hc in Hn by lia. congruence. }
      apply wp_bind. eapply lit_value_spec; [eassumption|]. intros v Hv.
      destruct (Nat.eqb_spec v 1).
      * apply wp_ret, HQ. intros _. constructor. auto.
      * eapply IH; [eassumption | eassumption | |].
        -- intros j Hj. rewrite <- Nat.add_assoc. apply (Hc (S j)). cbn. lia.
        -- intros b Hb. apply HQ. intros Hb'. apply Exists_cons_tl. auto.
Qed.

Lemma check_model_spec fuel : forall n pos F asl Q h,
  Fr h -> h (vloc (assigns s)) = Some (existT cellof nat asl) ->
  encodes xs0 n pos F ->
  (forall b, (b = true -> satisfies (val_of asl) F) -> Q b h) ->
  wp (check_model s fuel inp pos n) Q h.
Proof.
  induction fuel as [|f IH]; intros n pos F asl Q h Hf Ha HF HQ; cbn [check_model].
  - apply wp_vabort.
  - pose proof Hf as [(Hi & _ & _) _].
    destruct (Nat.leb_spec n pos).
    + apply wp_ret, HQ. intros _. inversion HF; subst; [constructor | lia].
    + inversion HF as [? Hle | ? c F' Hlt Hlen Hc HF']; subst; [lia|].
      apply wp_bind, wp_vget. intros xs len Hx Hn.
      rewrite (cell_inj _ _ _ _ Hx Hi), Hlen in Hn. injection Hn as <-.
      apply wp_bind. eapply clause_sat_spec; [eassumption | eassumption | exact Hc |].
      intros [|] Hb.
      * eapply IH; [exact Hf | eassumption | exact HF' |].
        intros b Hb'. apply HQ. intros ->. constructor; [apply Hb | apply Hb']; reflexivity.
      * apply wp_ret, HQ. discriminate.
Qed.

End Search.

(** * The theorem *)

Lemma alloc_neq (h : heap) l l' : h l = None -> h l' <> None -> l <> l'.
Proof. congruence. Qed.

Lemma mod8 c k : (c + 8 * k) mod 8 = c mod 8.
Proof. rewrite Nat.mul_comm. apply Nat.Div0.mod_add. Qed.

Lemma upd_some (h : heap) l c l' : h l' <> None -> upd h l c l' <> None.
Proof. unfold upd. destruct (Nat.eqb l' l); congruence. Qed.

(** If [run] finishes and answers "satisfiable" ([code] 1), the formula
    encoded in [input] when it started has a model. *)
Theorem run_sat_sound fuel budget nvars inp ninput xs0 F h0 r h1 :
  h0 (vloc inp) = Some (existT cellof nat xs0) ->
  encodes xs0 ninput 0 F ->
  runs h0 (run fuel budget nvars inp ninput) r h1 ->
  r mod 8 = 1 ->
  exists val, satisfies val F.
Proof.
  intros Hinp HF Hrun. revert r h1 Hrun.
  change (wp (run fuel budget nvars inp ninput)
            (fun r _ => r mod 8 = 1 -> exists val, satisfies val F) h0).
  unfold run.
  (* The empty vector, then the two vectors of handles. *)
  apply wp_bind, wp_vmake. intros e He. set (h0e := upd h0 _ _).
  apply wp_bind, wp_vmake. intros cs Hcs. set (h0c := upd h0e _ _).
  apply wp_bind, wp_vmake. intros ws Hws. set (h0w := upd h0c _ _).
  assert (Hie : h0e (vloc inp) <> None) by (apply upd_some; congruence).
  assert (Hic : h0c (vloc inp) <> None) by (now apply upd_some).
  assert (Hcc : h0c (vloc cs) <> None) by (unfold h0c; rewrite upd_eq; discriminate).
  assert (Hid : vloc inp <> vloc cs) by (intros E; rewrite E in Hie; congruence).
  assert (Hiw : vloc inp <> vloc ws) by (intros E; rewrite E in Hic; congruence).
  assert (Hdw : vloc cs <> vloc ws) by (intros E; rewrite E in Hcc; congruence).
  assert (Hf : frame (vloc inp) (vloc cs) (vloc ws) xs0 h0w).
  { split; [| split].
    - unfold h0w, h0c, h0e. rewrite !upd_neq; auto.
      + intros E; rewrite <- E in He; congruence.
    - exists []. split; [| constructor].
      unfold h0w. rewrite upd_neq by congruence. apply upd_eq.
    - exists []. split; [apply upd_eq | constructor]. }
  clearbody h0w. clear h0c h0e Hie Hic Hcc He Hcs Hws.
  apply wp_bind. eapply fresh_vecs_frame with (inp := vloc inp) (db := vloc cs) (wl := vloc ws); try eassumption; try reflexivity. intros _ h2 Hf2.
  (* The per-variable vectors, the trail and the counters. *)
  apply wp_bind. eapply frame_make; [eassumption|]. intros asg h3 Hf3 Gasg Ha3 _.
  assert (Hasg : natcell h3 (vloc asg)) by (eexists; exact Ha3). clear Ha3.
  do 8 (apply wp_bind; eapply frame_make; [eassumption|];
        let G := fresh "G" in let N := fresh "N" in
        intros ? ?h ?Hf G _ N; specialize (N _ Hasg); clear Hasg; rename N into Hasg).
  apply wp_bind, wp_vset. intros ms _ _. cbv zeta.
  match goal with
  | |- wp (ITree.bind (load ?s _ _ _ _) _) _ ?h =>
    assert (Hfr : Fr s inp xs0 h) by
      (split; [apply frame_write; assumption | now apply natcell_write_nat])
  end.
  apply wp_bind. eapply load_fr; cbn; try eassumption. intros ok hl Hfl.
  apply wp_bind. destruct ok.
  - apply wp_bind. eapply search_fr; cbn; try eassumption. intros r1 hs Hfs Hr1.
    destruct (Nat.eqb_spec r1 1) as [-> | Hne].
    + destruct (proj2 Hfs) as [asl Hasl].
      apply wp_bind. eapply check_model_spec; cbn; try eassumption.
      intros b Hb. apply wp_ret. apply wp_bind, wp_vget. intros _ k _ _. apply wp_ret.
      destruct b; intros Hm.
      * exists (val_of asl). auto.
      * assert (H3 : (3 + 8 * k) mod 8 = 1) by exact Hm. rewrite mod8 in H3. discriminate.
    + apply wp_ret. apply wp_bind, wp_vget. intros _ k _ _. apply wp_ret.
      intros Hm. assert (H3 : (r1 + 8 * k) mod 8 = 1) by exact Hm.
      rewrite mod8, Nat.mod_small in H3 by lia. lia.
  - apply wp_ret. apply wp_bind, wp_vget. intros _ k _ _. apply wp_ret.
    intros Hm. assert (H3 : (0 + 8 * k) mod 8 = 1) by exact Hm. rewrite mod8 in H3. discriminate.
Qed.

(** * Input validation *)

(** Every literal of [F] is below [lim]. *)
Definition lits_below (lim : nat) (F : list (list nat)) : Prop :=
  Forall (Forall (fun l => l < lim)) F.

Lemma valid_lits_spec inp xs0 lim fuel : forall len pos Q h,
  h (vloc inp) = Some (existT cellof nat xs0) ->
  (forall b, (b = true -> forall j, j < len ->
                exists l, nth_error xs0 (pos + j) = Some l /\ l < lim) -> Q b h) ->
  wp (valid_lits fuel inp lim pos len) Q h.
Proof.
  induction fuel as [|f IH]; intros len pos Q h Hi HQ; cbn [valid_lits].
  - apply wp_vabort.
  - destruct len as [|len'].
    + apply wp_ret, HQ. intros _ j Hj. lia.
    + apply wp_bind, wp_vget. intros xs l Hx Hn.
      rewrite (cell_inj _ _ _ _ Hx Hi) in Hn.
      destruct (Nat.ltb_spec l lim).
      * apply IH; [exact Hi|]. intros b Hb. apply HQ. intros Hbt j Hj.
        destruct j as [|j]; [exists l; rewrite Nat.add_0_r; auto|].
        destruct (Hb Hbt j) as (l' & Hl' & Hlt); [lia|].
        exists l'. split; [| exact Hlt]. rewrite <- Hl'. f_equal. lia.
      * apply wp_ret, HQ. discriminate.
Qed.

(** If [valid_clauses] accepts [input] from [pos] to [n], it encodes a
    formula there whose literals are all below [lim].  It leaves the heap
    alone either way. *)
Lemma valid_clauses_spec inp xs0 lim fuel : forall pos n Q h,
  h (vloc inp) = Some (existT cellof nat xs0) -> n <= length xs0 ->
  (forall b, (b = true -> exists F, encodes xs0 n pos F /\ lits_below lim F) -> Q b h) ->
  wp (valid_clauses fuel inp lim pos n) Q h.
Proof.
  induction fuel as [|f IH]; intros pos n Q h Hi Hn HQ; cbn [valid_clauses].
  - apply wp_vabort.
  - destruct (Nat.leb_spec n pos).
    + apply wp_ret, HQ. intros _. exists []. split; [now constructor | constructor].
    + apply wp_bind, wp_vget. intros xs len Hx Hlen.
      rewrite (cell_inj _ _ _ _ Hx Hi) in Hlen.
      destruct (Nat.leb_spec (pos + 1 + len) n); [| apply wp_ret, HQ; discriminate].
      apply wp_bind. eapply valid_lits_spec; [exact Hi|].
      intros [|] Hb; [| apply wp_ret, HQ; discriminate].
      specialize (Hb eq_refl).
      apply IH; [exact Hi | exact Hn |]. intros b Hb'. apply HQ. intros Hbt.
      destruct (Hb' Hbt) as (F & HF & HB).
      set (c := firstn len (skipn (pos + 1) xs0)).
      assert (Hc : length c = len) by (unfold c; rewrite length_firstn, length_skipn; lia).
      assert (Hcj : forall j, nth_error c j =
                     if Nat.ltb j len then nth_error xs0 (pos + 1 + j) else None)
        by (intros j; unfold c; now rewrite nth_error_firstn, nth_error_skipn).
      exists (c :: F). split.
      * apply enc_cons; [lia | now rewrite Hc | | now rewrite Hc].
        intros j Hj. rewrite Hc in Hj. rewrite Hcj. destruct (Nat.ltb_spec j len); [reflexivity | lia].
      * constructor; [| exact HB]. apply Forall_forall. intros l Hl.
        apply In_nth_error in Hl as (j & Hj). rewrite Hcj in Hj.
        destruct (Nat.ltb_spec j len); [| discriminate].
        destruct (Hb j) as (l' & Hl' & Hlt); [lia|].
        rewrite Hl' in Hj. injection Hj as <-. exact Hlt.
Qed.

(** [solve] checks its input, then either answers 4 in the heap it started
    in or is [run] on a well-formed encoding.  So a property of [run] on
    well-formed input, which also holds of 4, holds of [solve] on any
    input. *)
Lemma solve_wp fuel budget nvars inp ninput xs0 Q h0 :
  h0 (vloc inp) = Some (existT cellof nat xs0) ->
  Q 4 h0 ->
  (forall F, encodes xs0 ninput 0 F -> lits_below (2 * nvars) F ->
     wp (run fuel budget nvars inp ninput) Q h0) ->
  wp (solve fuel budget nvars inp ninput) Q h0.
Proof.
  intros Hi H4 Hrun. unfold solve.
  apply wp_bind, wp_vlen. intros xs Hx. rewrite (cell_inj _ _ _ _ Hx Hi).
  apply wp_bind. destruct (Nat.leb_spec ninput (length xs0)).
  - eapply valid_clauses_spec; [exact Hi | assumption |].
    intros [|] Hb; cbv beta iota.
    + destruct (Hb eq_refl) as (F & HF & HB). eauto.
    + apply wp_ret, H4.
  - apply wp_ret. cbv beta iota. apply wp_ret, H4.
Qed.

(** If [solve] finishes and answers "satisfiable" ([code] 1), the formula
    encoded in [input] when it started has a model. *)
Theorem solve_sat_sound fuel budget nvars inp ninput xs0 F h0 r h1 :
  h0 (vloc inp) = Some (existT cellof nat xs0) ->
  encodes xs0 ninput 0 F ->
  runs h0 (solve fuel budget nvars inp ninput) r h1 ->
  r mod 8 = 1 ->
  exists val, satisfies val F.
Proof.
  intros Hinp HF Hrun. revert r h1 Hrun.
  change (wp (solve fuel budget nvars inp ninput)
            (fun r _ => r mod 8 = 1 -> exists val, satisfies val F) h0).
  apply (solve_wp _ _ _ _ _ xs0); [exact Hinp | intros H; cbv in H; discriminate |].
  intros F' _ _ r h1 Hr. eapply run_sat_sound; eassumption.
Qed.
