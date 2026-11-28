(** The representation relation: which abstract state ([Abstract.astate])
    a pair of [Global] stores holds for the solver's handles [s].

    The [nat] store [mn] holds the twelve [nat] arrays of [s], the current
    arena and one storage array per watch list; the array store [ma] holds
    the arena reference and the watch-storage array [wdata].  The relation
    has two halves:
    - [conc]: the stores hold the arrays of [own s a ws] (the twelve
      arrays, the arena [a], the watch storages [ws]) with contents [cs],
      and no two of them share a cell;
    - [abs]: the contents [cs] spell the abstract state: fields exactly,
      the trail, trail limits, learnt clause, arena and watch storages up
      to a prefix whose length a counter holds.
    [repr] hides [a], [ws] and [cs].  Each kind of write gets a rule in
    [safe] form; the few steps that need the spare room past a prefix (a
    push, a clause written into the arena) use [rep] with the contents
    visible. *)
From ITree Require Import ITree ITreeFacts.
From Crane Require Import Monads.Global Monads.GlobalFacts.
From Stdlib Require Import List PeanoNat Lia.
Require Import Solver Abstract Inv Sem.
Import ListNotations.
Import Solver.
Local Set Warnings "-unused-intro-pattern".

(** * The arena encoding *)

(** The encoding of one more clause. *)
Lemma enc_cons c D : enc (c :: D) = (length c :: c) ++ enc D.
Proof. reflexivity. Qed.

(** The encoding of a concatenation. *)
Lemma enc_app D1 D2 : enc (D1 ++ D2) = enc D1 ++ enc D2.
Proof. unfold enc. now rewrite map_app, concat_app. Qed.

(** The arena length depends only on the clause lengths. *)
Lemma length_enc D : length (enc D) = list_sum (map S (map (@length nat) D)).
Proof.
  induction D as [|c D IH]; [reflexivity|].
  rewrite enc_cons, length_app, IH. reflexivity.
Qed.

(** Offsets depend only on the clause lengths. *)
Lemma off_ext D D' k : map (@length nat) D' = map (@length nat) D -> off D' k = off D k.
Proof. intros E. unfold off. rewrite !length_enc, <- !firstn_map, E. reflexivity. Qed.

(** [lset] commutes with [map]. *)
Lemma map_lset {A B} (f : A -> B) xs i x : map f (lset xs i x) = lset (map f xs) i (f x).
Proof. revert i; induction xs as [|y xs IH]; intros [|i]; simpl; rewrite ?IH; reflexivity. Qed.

(** Replacing a clause by one of the same length keeps the clause lengths. *)
Lemma map_length_lset D k cl cl' :
  nth_error D k = Some cl -> length cl' = length cl ->
  map (@length nat) (lset D k cl') = map (@length nat) D.
Proof.
  intros Hk E. rewrite map_lset, E. apply lset_same. rewrite nth_error_map, Hk. reflexivity.
Qed.

(** Appending a clause keeps the offsets of the old ones and of the end. *)
Lemma off_app D cl k : k <= length D -> off (D ++ [cl]) k = off D k.
Proof.
  intros Hk. unfold off. rewrite firstn_app. replace (k - length D) with 0 by lia.
  now rewrite app_nil_r.
Qed.

(** The appended clause sits at the old end of the arena. *)
Lemma off_snoc D cl : off (D ++ [cl]) (length D) = length (enc D).
Proof. rewrite off_app by lia. unfold off. now rewrite firstn_all. Qed.

(** [lset] on a list split at the written index. *)
Lemma lset_split {A} (D : list A) k cl cl' :
  nth_error D k = Some cl -> lset D k cl' = firstn k D ++ cl' :: skipn (S k) D.
Proof.
  revert k. induction D as [|c D IH]; intros [|k] H; cbn in H; try discriminate; [reflexivity|].
  rewrite lset_consS. cbn [firstn app]. f_equal. now apply IH.
Qed.

(** The arena around clause [k]. *)
Lemma enc_split D k cl :
  nth_error D k = Some cl -> enc D = enc (firstn k D) ++ (length cl :: cl) ++ enc (skipn (S k) D).
Proof.
  intros Hk. rewrite <- (firstn_skipn k D) at 1. rewrite (skipn_nth_error D k cl Hk).
  now rewrite enc_app, enc_cons.
Qed.

(** The length cell of clause [k]. *)
Lemma enc_at_len D k cl : nth_error D k = Some cl -> nth_error (enc D) (off D k) = Some (length cl).
Proof.
  intros Hk. rewrite (enc_split D k cl Hk). unfold off.
  rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
Qed.

(** Literal [j] of clause [k]. *)
Lemma enc_at_lit D k cl j :
  nth_error D k = Some cl -> j < length cl -> nth_error (enc D) (off D k + 1 + j) = nth_error cl j.
Proof.
  intros Hk Hj. rewrite (enc_split D k cl Hk). unfold off.
  rewrite nth_error_app2 by lia. replace (length (enc (firstn k D)) + 1 + j - length (enc (firstn k D)))
    with (S j) by lia. cbn [app nth_error]. now rewrite nth_error_app1.
Qed.

(** A clause fits in the arena. *)
Lemma off_lt D k cl : nth_error D k = Some cl -> off D k + S (length cl) <= length (enc D).
Proof.
  intros Hk. rewrite (enc_split D k cl Hk). unfold off. rewrite !length_app. cbn. lia.
Qed.

(** A write before the end of the prefix stays in it. *)
Lemma lset_app_l {A} (xs ys : list A) i x : i < length xs -> lset (xs ++ ys) i x = lset xs i x ++ ys.
Proof.
  revert i; induction xs as [|a xs IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|].
  rewrite !lset_consS. cbn [app]. f_equal. apply IH. lia.
Qed.

(** Writing literal [j] of clause [k] in the arena. *)
Lemma enc_lset D k cl j x :
  nth_error D k = Some cl -> j < length cl ->
  lset (enc D) (off D k + 1 + j) x = enc (lset D k (lset cl j x)).
Proof.
  intros Hk Hj. rewrite (enc_split D k cl Hk), (lset_split D k cl _ Hk). unfold off.
  rewrite lset_app_r by lia.
  replace (length (enc (firstn k D)) + 1 + j - length (enc (firstn k D))) with (S j) by lia.
  rewrite enc_app, enc_cons, lset_length. cbn [app]. rewrite lset_consS. now rewrite lset_app_l.
Qed.

(** A reason in the arrays: 0 for none, clause offset + 1 for clause [k]. *)
Definition tr_rsn (D : list (list nat)) (r : nat) : nat :=
  match r with 0 => 0 | S k => S (off D k) end.

(** Reasons survive a database change that keeps the clause lengths. *)
Lemma tr_rsn_ext D D' xs : map (@length nat) D' = map (@length nat) D -> map (tr_rsn D') xs = map (tr_rsn D) xs.
Proof.
  intros E. apply map_ext. intros [|k]; [reflexivity|]. cbn. f_equal. now apply off_ext.
Qed.

(** * Owned arrays *)

(** The [nat] array of each field. *)
Definition floc (s : state) (f : fld) : narr :=
  match f with
  | FAsg => assigns s | FLvl => level s | FRsn => reason s | FPh => phase s | FSt => stamp s
  | FSn => seen s | FTr => trail s | FLim => trail_lim s | FMisc => misc s | FLrn => learnt s
  end.

(** The position of field [f] among the owned arrays. *)
Definition fidx (f : fld) : nat :=
  match f with
  | FAsg => 0 | FLvl => 1 | FRsn => 2 | FPh => 3 | FSt => 4
  | FSn => 5 | FTr => 6 | FLim => 7 | FMisc => 8 | FLrn => 9
  end.

(** Every [nat] array the state owns: the fields, [wlen], [wcap] (positions
    10, 11), the arena [a] (12) and the watch storages (13 on). *)
Definition own (s : state) (a : narr) (ws : list narr) : list narr :=
  [assigns s; level s; reason s; phase s; stamp s; seen s; trail s; trail_lim s; misc s;
   learnt s; wlen s; wcap s; a] ++ ws.

(** The array of field [f] is owned. *)
Lemma own_fld s a ws f : nth_error (own s a ws) (fidx f) = Some (floc s f).
Proof. destruct f; reflexivity. Qed.

(** A field position is below 10. *)
Lemma fidx_lt f : fidx f < 10.
Proof. destruct f; cbn; lia. Qed.

(** The watch storage of literal [l] is owned. *)
Lemma own_ws s a ws l : nth_error (own s a ws) (13 + l) = nth_error ws l.
Proof. reflexivity. Qed.

(** Replacing the arena among the owned arrays. *)
Lemma own_lset_ar s a ws a' : lset (own s a ws) 12 a' = own s a' ws.
Proof. reflexivity. Qed.

(** Replacing a watch storage among the owned arrays. *)
Lemma own_lset_ws s a ws l w : lset (own s a ws) (13 + l) w = own s a (lset ws l w).
Proof. unfold own. rewrite lset_app_r by (cbn; lia). cbn [length]. now replace (13 + l - 13) with l by lia. Qed.

(** ** Disjoint arrays in one store *)

(** Partners at one index of a [Forall2]. *)
Lemma F2_nth {A B} (R : A -> B -> Prop) xs ys i x d :
  Forall2 R xs ys -> nth_error xs i = Some x -> R x (nth i ys d).
Proof.
  intros H. revert i. induction H as [|a b xs ys Hab H IH]; intros [|i] Hi; cbn in Hi; try discriminate.
  - injection Hi as <-. exact Hab.
  - apply IH, Hi.
Qed.

(** Replacing partners at one index of a [Forall2]. *)
Lemma F2_lset {A B} (R : A -> B -> Prop) xs ys i x y :
  Forall2 R xs ys -> R x y -> Forall2 R (lset xs i x) (lset ys i y).
Proof.
  intros H Hxy. revert i. induction H as [|a b xs ys Hab H IH]; intros [|i]; cbn; constructor; auto.
Qed.

(** A [Forall2] survives a change of relation on its left elements. *)
Lemma F2_impl {A B} (R R' : A -> B -> Prop) xs ys :
  (forall x y, In x xs -> R x y -> R' x y) -> Forall2 R xs ys -> Forall2 R' xs ys.
Proof.
  intros Himp H. induction H as [|a b xs ys Hab H IH]; constructor.
  - apply Himp; [left; reflexivity | exact Hab].
  - apply IH. intros x y Hx. apply Himp. right. exact Hx.
Qed.

(** A cell of an owned array is a cell of the owned list. *)
Lemma in_cells_own (own : list narr) (b : narr) y : In b own -> In y (cells b) -> In y (concat (map cells own)).
Proof. intros Hb Hy. apply in_concat. exists (cells b). split; [now apply in_map | exact Hy]. Qed.

(** Element [k] of [b] is a cell of [b]. *)
Lemma cell_in {A} (b : Global.array nat A) k : k < asize b -> In (abase b + k) (cells b).
Proof. intros Hk. apply in_cells. lia. Qed.

(** A write to one owned array keeps every owned array's contents but its own. *)
Lemma F2_awrite (m : Mn) (own : list narr) cs i (b : narr) k x :
  NoDup (concat (map cells own)) -> Forall2 (arr m) own cs -> nth_error own i = Some b ->
  k < length (nth i cs []) -> Forall2 (arr (awrite m b k x)) own (lset cs i (lset (nth i cs []) k x)).
Proof.
  intros Hnd H. revert i Hnd. induction H as [|a c own cs Hac H IH]; intros [|i] Hnd Hi Hk;
    cbn in Hi; try discriminate; cbn [map concat] in Hnd; cbn [nth lset] in *.
  - injection Hi as <-. constructor; [now apply (arr_awrite_same (V := Solver.Vn))|].
    apply (F2_impl (arr m)); [|exact H]. intros b' ys Hb' Hab'. apply (arr_awrite_other (V := Solver.Vn)); [exact Hab'|].
    intros Hin. apply (nodup_app_disj _ _ (abase a + k) Hnd).
    + apply cell_in. rewrite <- (arr_length _ _ _ Hac). exact Hk.
    + eapply in_cells_own; eauto.
  - constructor.
    + apply (arr_awrite_other (V := Solver.Vn)); [exact Hac|]. intros Hin. apply (nodup_app_disj _ _ _ Hnd Hin).
      eapply in_cells_own; [eapply nth_error_In; eauto|]. apply cell_in.
      pose proof (F2_nth _ _ _ _ _ [] H Hi) as Hb. rewrite <- (arr_length _ _ _ Hb). exact Hk.
    + apply IH; auto. eapply NoDup_app_remove_l; eauto.
Qed.

(** An element of an updated list is the new one or an old one. *)
Lemma in_lset {A} (xs : list A) i x y : In y (lset xs i x) -> y = x \/ In y xs.
Proof.
  revert i; induction xs as [|a xs IH]; intros [|i] H; [destruct H | destruct H | |].
  - rewrite lset_cons0 in H. destruct H as [<- | H]; auto. right; right; exact H.
  - rewrite lset_consS in H. destruct H as [<- | H]; [right; left; reflexivity|].
    destruct (IH i H); auto. right; right; auto.
Qed.

(** Replacing an owned array by one with cells of its own keeps them disjoint. *)
Lemma sep_lset (own : list narr) i (b : narr) :
  NoDup (concat (map cells own)) -> (forall y, In y (cells b) -> ~ In y (concat (map cells own))) ->
  NoDup (concat (map cells (lset own i b))).
Proof.
  revert i. induction own as [|c own IH]; intros [|i] Hnd Hb; cbn [lset map concat] in *; auto.
  - apply NoDup_app; [apply seq_NoDup | eapply NoDup_app_remove_l; eauto |].
    intros y Hy Hy'. apply (Hb y Hy). apply in_or_app. right. exact Hy'.
  - apply NoDup_app; [eapply NoDup_app_remove_r; eauto | apply IH |].
    + eapply NoDup_app_remove_l; eauto.
    + intros y Hy Hy'. apply (Hb y Hy). apply in_or_app. right. exact Hy'.
    + intros y Hy Hy'. apply in_concat in Hy' as (cl & Hcl & Hy'). apply in_map_iff in Hcl as (b' & <- & Hb').
      destruct (in_lset _ _ _ _ Hb') as [-> | Hin].
      * apply (Hb y Hy'). apply in_or_app. left. exact Hy.
      * apply (nodup_app_disj _ _ _ Hnd Hy). eapply in_cells_own; [exact Hin | exact Hy'].
Qed.

(** * The two halves of the relation *)

(** The store half: [mn] holds the owned arrays with contents [cs], pairwise
    disjoint; [ma] holds the arena [a] in the arena reference and the watch
    storages [ws] in [wdata], the reference outside [wdata]. *)
Record conc (s : state) (nv : nat) (mn : Mn) (ma : Ma) (a : narr) (ws : list narr)
    (cs : list (list nat)) : Prop := {
  c_ref : refp ma (arena s) a;
  c_wd : arr ma (wdata s) ws;
  c_wdn : length ws = 2 * nv;
  c_vsep : ~ In (Global.ref_index narr (arena s)) (cells (wdata s));
  c_arrs : Forall2 (arr mn) (own s a ws) cs;
  c_sep : NoDup (concat (map cells (own s a ws)))
}.

(** [ys] starts with [xs]. *)
Definition pre (xs ys : list nat) : Prop := exists pad, ys = xs ++ pad.

(** The fields an array holds exactly. *)
Definition plain (f : fld) : Prop := f = FAsg \/ f = FLvl \/ f = FPh \/ f = FSt \/ f = FSn \/ f = FMisc.

(** The contents of field [f]'s array. *)
Notation cfld cs f := (nth (fidx f) cs []).
(** The contents of [wlen]. *)
Notation cwl cs := (nth 10 cs []).
(** The contents of [wcap]. *)
Notation cwc cs := (nth 11 cs []).
(** The contents of the arena. *)
Notation car cs := (nth 12 cs []).
(** The contents of literal [l]'s watch storage. *)
Notation cws cs l := (nth (13 + l) cs []).

(** The abstract half: contents [cs] spell [st] over [nv] variables. *)
Record abs (nv : nat) (st : astate) (cs : list (list nat)) : Prop := {
  a_len : length cs = 13 + 2 * nv;
  a_fld : forall f, plain f -> cfld cs f = fv st f;
  a_miscn : length (fv st FMisc) = NMISC;
  a_rsn : cfld cs FRsn = map (tr_rsn (db st)) (rsn st);
  a_tr : pre (tr st) (cfld cs FTr);
  a_trn : length (cfld cs FTr) = nv;
  a_tlen : nth TLEN (fv st FMisc) 0 = length (tr st);
  a_lim : pre (lim st) (cfld cs FLim);
  a_limn : length (cfld cs FLim) = nv;
  a_tllen : nth TLLEN (fv st FMisc) 0 = length (lim st);
  a_lrn : pre (lrn st) (cfld cs FLrn);
  a_lrnn : length (cfld cs FLrn) = nv + 1;
  a_llen : nth LLEN (fv st FMisc) 0 = length (lrn st);
  a_ar : pre (enc (db st)) (car cs);
  a_alen : nth ALEN (fv st FMisc) 0 = length (enc (db st));
  a_acap : nth ACAP (fv st FMisc) 0 = length (car cs);
  a_wln : length (cwl cs) = 2 * nv;
  a_wcn : length (cwc cs) = 2 * nv;
  a_wll : length (wl st) = 2 * nv;
  a_wl : forall l, l < 2 * nv -> nth l (cwl cs) 0 = length (nth l (wl st) []);
  a_wc : forall l, l < 2 * nv -> nth l (cwc cs) 0 = length (cws cs l);
  a_ws : forall l, l < 2 * nv -> pre (map (off (db st)) (nth l (wl st) [])) (cws cs l)
}.

(** The stores hold [st], with the arena, watch storages and contents shown. *)
Definition rep s nv mn ma st a ws cs : Prop := conc s nv mn ma a ws cs /\ abs nv st cs.

(** The stores hold the abstract state [st]. *)
Definition repr (s : state) (nv : nat) (mn : Mn) (ma : Ma) (st : astate) : Prop :=
  exists a ws cs, rep s nv mn ma st a ws cs.

(** * The store half under each kind of step *)

(** Reading [nth] after [lset] at another index. *)
Lemma nth_lset_ne {A} (xs : list A) p q y d : p <> q -> nth q (lset xs p y) d = nth q xs d.
Proof. intros H. rewrite nth_lset. destruct (Nat.eqb_spec p q); [lia | reflexivity]. Qed.

(** Reading [nth] after [lset] at its index. *)
Lemma nth_lset_eq {A} (xs : list A) p y d : p < length xs -> nth p (lset xs p y) d = y.
Proof. intros H. rewrite nth_lset, Nat.eqb_refl. destruct (Nat.ltb_spec p (length xs)); [reflexivity | lia]. Qed.

(** Every owned array holds its contents. *)
Lemma conc_arr s nv mn ma a ws cs p b :
  conc s nv mn ma a ws cs -> nth_error (own s a ws) p = Some b -> arr mn b (nth p cs []).
Proof. intros C Hp. exact (F2_nth _ _ _ _ _ [] (c_arrs _ _ _ _ _ _ _ C) Hp). Qed.

(** A write to an owned array changes its contents only. *)
Lemma conc_awrite s nv mn ma a ws cs p b k x :
  conc s nv mn ma a ws cs -> nth_error (own s a ws) p = Some b -> k < length (nth p cs []) ->
  conc s nv (awrite mn b k x) ma a ws (lset cs p (lset (nth p cs []) k x)).
Proof.
  intros [? ? ? ? Ha Hs] Hp Hk. constructor; auto. now apply F2_awrite.
Qed.

(** A step that keeps every owned array keeps the store half. *)
Lemma conc_frame s nv mn mn' ma a ws cs :
  conc s nv mn ma a ws cs -> (forall b ys, In b (own s a ws) -> arr mn b ys -> arr mn' b ys) ->
  conc s nv mn' ma a ws cs.
Proof. intros [? ? ? ? Ha Hs] H. constructor; auto. eapply F2_impl; [exact H | exact Ha]. Qed.

(** [b]'s cells are outside every owned array. *)
Definition outside (s : state) (a : narr) (ws : list narr) (b : narr) : Prop :=
  forall y, In y (cells b) -> ~ In y (concat (map cells (own s a ws))).

(** A write to an array outside the owned ones keeps the store half. *)
Lemma conc_scratch s nv mn ma a ws cs b k x :
  conc s nv mn ma a ws cs -> outside s a ws b -> k < asize b -> conc s nv (awrite mn b k x) ma a ws cs.
Proof.
  intros C Hb Hk. apply (conc_frame _ _ _ _ _ _ _ _ C). intros b' ys Hb' H.
  apply (arr_awrite_other (V := Solver.Vn)); [exact H|]. intros Hin.
  apply (Hb _ (cell_in _ _ Hk)). eapply in_cells_own; eauto.
Qed.

(** A new array lies outside the owned ones. *)
Lemma conc_fresh s nv mn ma a ws cs n :
  conc s nv mn ma a ws cs -> outside s a ws (afresh mn n).
Proof.
  intros C y Hy Hin. apply in_concat in Hin as (cl & Hcl & Hy'). apply in_map_iff in Hcl as (b & <- & Hb).
  destruct (In_nth_error _ _ Hb) as (p & Hp).
  exact (afresh_disjoint (V := Solver.Vn) _ n _ _ _ (conc_arr _ _ _ _ _ _ _ _ _ C Hp) Hy' Hy).
Qed.

(** Making a new array keeps the store half. *)
Lemma conc_anew s nv mn ma a ws cs n x :
  conc s nv mn ma a ws cs -> conc s nv (anew mn n x) ma a ws cs.
Proof.
  intros C. apply (conc_frame _ _ _ _ _ _ _ _ C). intros b ys _ H. now apply (arr_anew_old (V := Solver.Vn)).
Qed.

(** Moving literal [l]'s watch list to the array [w] (outside the owned ones). *)
Lemma conc_wdata s nv mn ma a ws cs l w ys :
  conc s nv mn ma a ws cs -> l < 2 * nv -> arr mn w ys -> outside s a ws w ->
  conc s nv mn (awrite ma (wdata s) l w) a (lset ws l w) (lset cs (13 + l) ys).
Proof.
  intros [Hr Hw Hn Hv Ha Hs] Hl Hy Ho.
  assert (Hlw : l < asize (wdata s)) by (rewrite <- (arr_length _ _ _ Hw); lia).
  constructor.
  - apply (refp_awrite (V := Solver.Va)); [exact Hr|]. intros E. apply Hv. rewrite E. now apply cell_in.
  - apply (arr_awrite_same (V := Solver.Va)); [exact Hw | lia].
  - now rewrite lset_length.
  - exact Hv.
  - rewrite <- own_lset_ws. now apply F2_lset.
  - rewrite <- own_lset_ws. now apply sep_lset.
Qed.

(** Moving the arena to the array [a'] (outside the owned ones). *)
Lemma conc_arena s nv mn ma a ws cs a' ys :
  conc s nv mn ma a ws cs -> arr mn a' ys -> outside s a ws a' ->
  conc s nv mn (rwrite ma (arena s) a') a' ws (lset cs 12 ys).
Proof.
  intros [Hr Hw Hn Hv Ha Hs] Hy Ho. constructor.
  - apply (refp_rwrite_same (V := Solver.Va)).
  - now apply (arr_rwrite (V := Solver.Va)).
  - exact Hn.
  - exact Hv.
  - rewrite <- (own_lset_ar s a ws a'). now apply F2_lset.
  - rewrite <- (own_lset_ar s a ws a'). now apply sep_lset.
Qed.

(** * The abstract half under each kind of step *)

(** The fields stored with a length counter. *)
Definition seqf (f : fld) : Prop := f = FTr \/ f = FLim \/ f = FLrn.

(** The [misc] slot holding the length of a counted field. *)
Definition slot (f : fld) : nat := match f with FTr => TLEN | FLim => TLLEN | _ => LLEN end.

(** The capacity of a counted field's array. *)
Definition capf (nv : nat) (f : fld) : nat := match f with FLrn => nv + 1 | _ => nv end.

(** The [misc] slots that [abs] reads. *)
Definition kept (k : nat) : Prop := k <> TLEN /\ k <> TLLEN /\ k <> LLEN /\ k <> ALEN /\ k <> ACAP.

(** A counted field's contents and counter, from [abs]. *)
Lemma abs_seq nv st cs f :
  abs nv st cs -> seqf f ->
  pre (fv st f) (cfld cs f) /\ length (cfld cs f) = capf nv f /\ nth (slot f) (fv st FMisc) 0 = length (fv st f).
Proof. intros A [-> | [-> | ->]]; cbn [capf slot]; repeat split; apply A. Qed.

(** Rewrite [nth] after [lset] wherever the indices decide it. *)
Ltac nls :=
  repeat first [rewrite nth_lset_eq by (rewrite ?lset_length; lia) | rewrite nth_lset_ne by lia].

(** Compute field reads of updated abstract states. *)
Ltac fcases := cbn [fv fset dset wset cpush db wl fld_eqb] in *.

(** Destructure [abs] with named hypotheses. *)
Ltac dabs A :=
  destruct A as [Hlen Hfld Hmiscn Hrsn Htr Htrn Htlen Hlim Hlimn Htllen Hlrn Hlrnn Hllen Har Halen Hacap
                 Hwln Hwcn Hwll Hwl Hwc Hws].

(** Cases of a [plain] field. *)
Ltac pcases H := destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]].

(** Cases of a counted field. *)
Ltac scases H := destruct H as [-> | [-> | ->]].

(** The plain fields' contents, from [a_fld]. *)
Ltac pfacts H :=
  pose proof (H FAsg ltac:(unfold plain; tauto)); pose proof (H FLvl ltac:(unfold plain; tauto));
  pose proof (H FPh ltac:(unfold plain; tauto)); pose proof (H FSt ltac:(unfold plain; tauto));
  pose proof (H FSn ltac:(unfold plain; tauto)); pose proof (H FMisc ltac:(unfold plain; tauto)).

(** Finish an [abs] obligation by computing reads. *)
Ltac absr :=
  intros; unfold kept, TLEN, TLLEN, LLEN, ALEN, ACAP, NMISC in *; cbn [fidx] in *; fcases; nls; fcases;
  rewrite ?lset_length; try congruence; auto.

(** A plain field write; in [misc], away from the slots [abs] reads. *)
Lemma abs_plain nv st cs f k x :
  abs nv st cs -> plain f -> (f = FMisc -> kept k) ->
  abs nv (fset st f (lset (fv st f) k x)) (lset cs (fidx f) (lset (cfld cs f) k x)).
Proof.
  intros A Hf Hk. dabs A. pfacts Hfld.
  pcases Hf; [| | | | | destruct (Hk eq_refl) as (? & ? & ? & ? & ?)]; constructor;
    try (intros g Hg; pcases Hg); absr.
Qed.

(** A prefix survives a write inside it. *)
Lemma pre_lset_in xs ys k x : pre xs ys -> k < length xs -> pre (lset xs k x) (lset ys k x).
Proof. intros [pad ->] Hk. exists pad. now apply lset_app_l. Qed.

(** A prefix survives a write past it. *)
Lemma pre_lset_out xs ys k x : pre xs ys -> length xs <= k -> pre xs (lset ys k x).
Proof. intros [pad ->] Hk. exists (lset pad (k - length xs) x). now apply lset_app_r. Qed.

(** A list starts with each of its prefixes. *)
Lemma pre_firstn n ys : pre (firstn n ys) ys.
Proof. exists (skipn n ys). symmetry. apply firstn_skipn. Qed.

(** A prefix is no longer than the list. *)
Lemma pre_length xs ys : pre xs ys -> length xs <= length ys.
Proof. intros [pad ->]. rewrite length_app. lia. Qed.

(** A read inside a prefix. *)
Lemma pre_nth_error xs ys i x : pre xs ys -> nth_error xs i = Some x -> nth_error ys i = Some x.
Proof. intros [pad ->] H. rewrite nth_error_app1; [exact H | apply nth_error_Some; congruence]. Qed.

(** Writing back an entry changes nothing. *)
Lemma lset_nth_same {A} (xs : list A) p d : p < length xs -> lset xs p (nth p xs d) = xs.
Proof. intros H. apply lset_same. now apply nth_error_nth'. Qed.

(** Offsets of a list of clauses survive a change keeping the clause lengths. *)
Lemma map_off_ext D D' xs : map (@length nat) D' = map (@length nat) D -> map (off D') xs = map (off D) xs.
Proof. intros E. apply map_ext. intros k. now apply off_ext. Qed.

(** A reason write. *)
Lemma abs_rsn nv st cs k r :
  abs nv st cs ->
  abs nv (fset st FRsn (lset (rsn st) k r)) (lset cs 2 (lset (cfld cs FRsn) k (tr_rsn (db st) r))).
Proof.
  intros A. dabs A. pfacts Hfld. constructor; try (intros g Hg; pcases Hg); absr.
  rewrite Hrsn. symmetry. apply map_lset.
Qed.

(** A write inside a counted field's prefix. *)
Lemma abs_seq_set nv st cs f k x :
  abs nv st cs -> seqf f -> k < length (fv st f) ->
  abs nv (fset st f (lset (fv st f) k x)) (lset cs (fidx f) (lset (cfld cs f) k x)).
Proof.
  intros A Hf Hk. dabs A. pfacts Hfld.
  scases Hf; constructor; try (intros g Hg; pcases Hg); absr; now apply pre_lset_in.
Qed.

(** A write past a counted field's prefix. *)
Lemma abs_pad nv st cs f k x :
  abs nv st cs -> seqf f -> length (fv st f) <= k -> abs nv st (lset cs (fidx f) (lset (cfld cs f) k x)).
Proof.
  intros A Hf Hk. dabs A. pfacts Hfld.
  scases Hf; constructor; try (intros g Hg; pcases Hg); absr; now apply pre_lset_out.
Qed.

(** Setting a counted field's length to [n]: the field becomes the first
    [n] elements of its array. *)
Lemma abs_len nv st cs f n :
  abs nv st cs -> seqf f -> n <= capf nv f ->
  abs nv (fset (fset st FMisc (lset (fv st FMisc) (slot f) n)) f (firstn n (cfld cs f)))
    (lset cs 8 (lset (cfld cs FMisc) (slot f) n)).
Proof.
  intros A Hf Hn. dabs A. pfacts Hfld.
  scases Hf; cbn [slot capf] in *; constructor; try (intros g Hg; pcases Hg); absr;
    try apply pre_firstn; rewrite length_firstn; lia.
Qed.

(** Writing literal [j] of clause [k] in the arena. *)
Lemma abs_dset nv st cs k cl j x :
  abs nv st cs -> nth_error (db st) k = Some cl -> j < length cl ->
  abs nv (dset st (lset (db st) k (lset cl j x))) (lset cs 12 (lset (car cs) (off (db st) k + 1 + j) x)).
Proof.
  intros A Hk Hj. pose proof (map_length_lset _ _ _ (lset cl j x) Hk (lset_length _ _ _)) as E.
  pose proof (off_lt _ _ _ Hk) as Hlt. dabs A. pfacts Hfld.
  constructor; try (intros g Hg; pcases Hg); absr.
  all: try (now rewrite (tr_rsn_ext _ _ _ E)).
  all: try (rewrite <- (enc_lset _ _ _ _ x Hk Hj); apply pre_lset_in; [exact Har | lia]).
  all: try (rewrite Halen, !length_enc, E; reflexivity).
  all: rewrite (map_off_ext _ _ _ E); auto.
Qed.

(** A write past the clauses in the arena. *)
Lemma abs_arpad nv st cs k x :
  abs nv st cs -> length (enc (db st)) <= k -> abs nv st (lset cs 12 (lset (car cs) k x)).
Proof.
  intros A Hk. dabs A. pfacts Hfld. constructor; try (intros g Hg; pcases Hg); absr.
  now apply pre_lset_out.
Qed.

(** Setting the arena length past a clause [cl] written after the old
    clauses appends it; reasons and watch entries name old clauses. *)
Lemma abs_cpush nv st cs cl pad :
  abs nv st cs -> Forall (fun r => r <= length (db st)) (rsn st) ->
  Forall (Forall (fun ci => ci < length (db st))) (wl st) ->
  car cs = enc (db st) ++ (length cl :: cl) ++ pad ->
  abs nv (fset (cpush st cl) FMisc (lset (fv st FMisc) ALEN (length (enc (db st)) + S (length cl))))
    (lset cs 8 (lset (cfld cs FMisc) ALEN (length (enc (db st)) + S (length cl)))).
Proof.
  intros A Hr Hw Hc. dabs A. pfacts Hfld.
  assert (Er : map (tr_rsn (db st ++ [cl])) (rsn st) = map (tr_rsn (db st)) (rsn st)).
  { apply map_ext_in. intros [|r] Hin; [reflexivity|]. cbn. f_equal. apply off_app.
    rewrite Forall_forall in Hr. specialize (Hr _ Hin). lia. }
  assert (Ew : forall l, map (off (db st ++ [cl])) (nth l (wl st) []) = map (off (db st)) (nth l (wl st) [])).
  { intros l. apply map_ext_in. intros ci Hin. apply off_app.
    destruct (Nat.ltb_spec l (length (wl st))) as [Hl | Hl]; [|rewrite nth_overflow in Hin by lia; destruct Hin].
    rewrite Forall_forall in Hw. specialize (Hw _ (nth_In _ [] Hl)). rewrite Forall_forall in Hw.
    specialize (Hw _ Hin). lia. }
  constructor; try (intros g Hg; pcases Hg); absr.
  all: try (rewrite Er; exact Hrsn).
  all: try (rewrite Ew; auto).
  all: rewrite enc_app; change (enc [cl]) with ((length cl :: cl) ++ []); rewrite app_nil_r.
  - rewrite Hc. exists pad. now rewrite <- app_assoc.
  - rewrite length_app. cbn [length]. lia.
Qed.

(** Setting the arena capacity after moving the arena to contents [ys]. *)
Lemma abs_newar nv st cs ys :
  abs nv st cs -> pre (enc (db st)) ys ->
  abs nv (fset st FMisc (lset (fv st FMisc) ACAP (length ys)))
    (lset (lset cs 12 ys) 8 (lset (cfld cs FMisc) ACAP (length ys))).
Proof. intros A Hy. dabs A. pfacts Hfld. constructor; try (intros g Hg; pcases Hg); absr. Qed.

(** Replacing literal [l]'s watch list by [L'], stored in [S'] (length and
    capacity updated with it). *)
Lemma abs_watch nv st cs l L' S' :
  abs nv st cs -> l < 2 * nv -> pre (map (off (db st)) L') S' ->
  abs nv (wset st (lset (wl st) l L'))
    (lset (lset (lset cs (13 + l) S') 10 (lset (cwl cs) l (length L'))) 11 (lset (cwc cs) l (length S'))).
Proof.
  intros A Hl HS. dabs A. pfacts Hfld.
  constructor; try (intros g Hg; pcases Hg); absr;
    destruct (Nat.eq_dec l l0) as [<- | Hne]; nls; auto.
Qed.

(** Writing back what an entry holds changes nothing. *)
Lemma lset_eq_nth {A} (xs : list A) p y d : p < length xs -> nth p xs d = y -> lset xs p y = xs.
Proof. intros H <-. now apply lset_nth_same. Qed.

(** Writing entry [i] of literal [l]'s watch list in its storage. *)
Lemma abs_ws_set nv st cs l i ci :
  abs nv st cs -> l < 2 * nv -> i < length (nth l (wl st) []) ->
  abs nv (wset st (lset (wl st) l (lset (nth l (wl st) []) i ci)))
    (lset cs (13 + l) (lset (cws cs l) i (off (db st) ci))).
Proof.
  intros A Hl Hi. pose proof (a_wl _ _ _ A l Hl) as E1. pose proof (a_wc _ _ _ A l Hl) as E2.
  pose proof (a_len _ _ _ A) as E0. pose proof (a_wln _ _ _ A) as E3. pose proof (a_wcn _ _ _ A) as E4.
  set (S' := lset (cws cs l) i (off (db st) ci)).
  pose proof (abs_watch _ _ _ l (lset (nth l (wl st) []) i ci) S' A Hl) as H.
  rewrite (lset_eq_nth (cwl cs) l (length (lset (nth l (wl st) []) i ci)) 0) in H
    by (rewrite ?lset_length; lia).
  rewrite (lset_eq_nth (cwc cs) l (length S') 0) in H by (unfold S'; rewrite ?lset_length; lia).
  rewrite (lset_eq_nth (lset cs (13 + l) S') 10 (cwl cs) []) in H by (rewrite ?lset_length; try rewrite nth_lset_ne by lia; first [reflexivity | lia]).
  rewrite (lset_eq_nth (lset cs (13 + l) S') 11 (cwc cs) []) in H by (rewrite ?lset_length; try rewrite nth_lset_ne by lia; first [reflexivity | lia]).
  apply H. unfold S'. rewrite map_lset. apply pre_lset_in; [exact (a_ws _ _ _ A l Hl) | now rewrite length_map].
Qed.

(** Cutting literal [l]'s watch list to [n] entries. *)
Lemma abs_wlen_set nv st cs l n :
  abs nv st cs -> l < 2 * nv -> n <= length (nth l (wl st) []) ->
  abs nv (wset st (lset (wl st) l (firstn n (nth l (wl st) [])))) (lset cs 10 (lset (cwl cs) l n)).
Proof.
  intros A Hl Hn. pose proof (a_wc _ _ _ A l Hl) as E2.
  pose proof (a_len _ _ _ A) as E0. pose proof (a_wcn _ _ _ A) as E4.
  pose proof (abs_watch _ _ _ l (firstn n (nth l (wl st) [])) (cws cs l) A Hl) as H.
  rewrite length_firstn in H. replace (Nat.min n (length (nth l (wl st) []))) with n in H by lia.
  rewrite (lset_eq_nth (cwc cs) l (length (cws cs l)) 0) in H by lia.
  rewrite (lset_eq_nth cs (13 + l) (cws cs l) []) in H by (first [reflexivity | lia]).
  rewrite (lset_eq_nth (lset cs 10 (lset (cwl cs) l n)) 11 (cwc cs) []) in H
    by (rewrite ?lset_length; try rewrite nth_lset_ne by lia; first [reflexivity | lia]).
  apply H. destruct (a_ws _ _ _ A l Hl) as [pad Hp]. rewrite Hp, <- firstn_map.
  exists (skipn n (map (off (db st)) (nth l (wl st) [])) ++ pad). rewrite app_assoc, firstn_skipn. reflexivity.
Qed.

(** Moving literal [l]'s watch list to new storage holding [ys], with the
    capacity updated. *)
Lemma abs_wmove nv st cs l ys :
  abs nv st cs -> l < 2 * nv -> pre (map (off (db st)) (nth l (wl st) [])) ys ->
  abs nv st (lset (lset cs (13 + l) ys) 11 (lset (cwc cs) l (length ys))).
Proof.
  intros A Hl Hy. pose proof (a_wl _ _ _ A l Hl) as E1.
  pose proof (a_len _ _ _ A) as E0. pose proof (a_wln _ _ _ A) as E3. pose proof (a_wll _ _ _ A) as E5.
  pose proof (abs_watch _ _ _ l (nth l (wl st) []) ys A Hl Hy) as H.
  rewrite (lset_eq_nth (wl st) l (nth l (wl st) []) []), wset_id in H by (first [reflexivity | lia]).
  rewrite (lset_eq_nth (cwl cs) l (length (nth l (wl st) [])) 0) in H by lia.
  rewrite (lset_eq_nth (lset cs (13 + l) ys) 10 (cwl cs) []) in H
    by (rewrite ?lset_length; try rewrite nth_lset_ne by lia; first [reflexivity | lia]).
  exact H.
Qed.

(** A write past the end of literal [l]'s watch list in its storage. *)
Lemma abs_wpad nv st cs l k x :
  abs nv st cs -> l < 2 * nv -> length (nth l (wl st) []) <= k ->
  abs nv st (lset cs (13 + l) (lset (cws cs l) k x)).
Proof.
  intros A Hl Hk. pose proof (a_wc _ _ _ A l Hl) as E2.
  pose proof (a_len _ _ _ A) as E0. pose proof (a_wcn _ _ _ A) as E4.
  pose proof (abs_wmove _ _ _ l (lset (cws cs l) k x) A Hl) as H.
  rewrite lset_length, (lset_eq_nth (cwc cs) l (length (cws cs l)) 0) in H by lia.
  rewrite (lset_eq_nth (lset cs (13 + l) (lset (cws cs l) k x)) 11 (cwc cs) []) in H
    by (rewrite ?lset_length; try rewrite nth_lset_ne by lia; first [reflexivity | lia]).
  apply H. apply pre_lset_out; [exact (a_ws _ _ _ A l Hl) | now rewrite length_map].
Qed.

(** Counting one more entry of literal [l]'s watch list, already stored
    past its end: clause [ci]'s offset. *)
Lemma abs_wpush nv st cs l ci :
  abs nv st cs -> l < 2 * nv ->
  nth_error (cws cs l) (length (nth l (wl st) [])) = Some (off (db st) ci) ->
  abs nv (wset st (lset (wl st) l (nth l (wl st) [] ++ [ci])))
    (lset cs 10 (lset (cwl cs) l (length (nth l (wl st) []) + 1))).
Proof.
  intros A Hl Hn. pose proof (a_wc _ _ _ A l Hl) as E2.
  pose proof (a_len _ _ _ A) as E0. pose proof (a_wcn _ _ _ A) as E4.
  pose proof (abs_watch _ _ _ l (nth l (wl st) [] ++ [ci]) (cws cs l) A Hl) as H.
  rewrite length_app in H. cbn [length] in H.
  rewrite (lset_eq_nth (cwc cs) l (length (cws cs l)) 0) in H by lia.
  rewrite (lset_eq_nth cs (13 + l) (cws cs l) []) in H by (first [reflexivity | lia]).
  rewrite (lset_eq_nth (lset cs 10 (lset (cwl cs) l (length (nth l (wl st) []) + 1))) 11 (cwc cs) []) in H
    by (rewrite ?lset_length; try rewrite nth_lset_ne by lia; first [reflexivity | lia]).
  apply H. destruct (a_ws _ _ _ A l Hl) as [pad Hp]. rewrite Hp in Hn |- *.
  rewrite nth_error_app2 in Hn by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag in Hn.
  destruct pad as [|y pad]; [discriminate|]. injection Hn as ->.
  exists pad. rewrite map_app, <- app_assoc. reflexivity.
Qed.

(** Two abstract states that agree on every component. *)
Definition sim (st st' : astate) : Prop :=
  db st' = db st /\ wl st' = wl st /\ forall f, fv st' f = fv st f.

(** [abs] reads only the components. *)
Lemma abs_sim nv st st' cs : abs nv st cs -> sim st st' -> abs nv st' cs.
Proof.
  intros A (Ed & Ew & Ef). dabs A. constructor; rewrite ?Ed, ?Ew, ?Ef; auto.
  intros f Hf. rewrite Ef. auto.
Qed.

(** [repr] reads only the components. *)
Lemma repr_sim s nv mn ma st st' : repr s nv mn ma st -> sim st st' -> repr s nv mn ma st'.
Proof. intros (a & ws & cs & C & A) H. exists a, ws, cs. split; [exact C | eapply abs_sim; eauto]. Qed.

(** * Rules for the solver's steps *)

(** A tree is as safe as its [bind] with [Ret]. *)
Lemma safe_unbind {R} (t : itree E R) Q h : safe (ITree.bind t (fun x => Ret x)) Q h -> safe t Q h.
Proof. apply safe_eq_itree. apply bind_ret_r. Qed.

(** A [bind] whose continuation ends in a bare event is as safe as the
    same [bind] with a final [Ret]. *)
Lemma safe_unbind2 {R T} (t : itree E T) (u : T -> itree E R) Q h :
  safe (ITree.bind t (fun x => ITree.bind (u x) (fun y => Ret y))) Q h -> safe (ITree.bind t u) Q h.
Proof. apply safe_eq_itree. setoid_rewrite bind_ret_r. reflexivity. Qed.

(** [copy src dst i n] copies elements [i .. i + n) of [src] into [dst],
    whose first [i] elements already agree with [src]; arrays whose cells
    avoid [dst] keep their contents. *)
Lemma copy_safe src dst : forall n i xs ys Q mn ma,
  arr mn src xs -> arr mn dst ys -> (forall y, In y (cells dst) -> ~ In y (cells src)) ->
  i + n <= length xs -> i + n <= length ys -> firstn i ys = firstn i xs ->
  (forall mn', (forall b zs, arr mn b zs -> (forall y, In y (cells dst) -> ~ In y (cells b)) -> arr mn' b zs) ->
     arr mn' dst (firstn (i + n) xs ++ skipn (i + n) ys) -> Q tt (mn', ma)) ->
  safe (copy src dst i n) Q (mn, ma).
Proof.
  induction n as [|n IH]; intros i xs ys Q mn ma Hs Hd Hsd Hx Hy Hpre HQ; cbn [copy].
  - apply safe_ret. apply HQ; [auto|]. rewrite Nat.add_0_r, <- Hpre, firstn_skipn. exact Hd.
  - destruct (nth_error xs i) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    eapply safe_read_n_bind; [exact Hs | exact Ex |].
    assert (Hi : i < asize dst) by (rewrite <- (arr_length _ _ _ Hd); lia).
    eapply safe_write_n_bind; [exact Hd | lia |].
    apply (IH (i + 1) xs (lset ys i x)).
    + apply (arr_awrite_other (V := Solver.Vn)); [exact Hs|]. intros Hin. exact (Hsd _ (cell_in _ _ Hi) Hin).
    + apply (arr_awrite_same (V := Solver.Vn)); [exact Hd | lia].
    + exact Hsd.
    + lia.
    + rewrite lset_length. lia.
    + rewrite Nat.add_1_r, firstn_lset_S by lia. rewrite Hpre.
      symmetry. now apply firstn_S_snoc.
    + intros mn' Hk Hd'. apply HQ.
      * intros b zs Hb Hbd. apply Hk; [|exact Hbd]. apply (arr_awrite_other (V := Solver.Vn)); [exact Hb|].
        intros Hin. exact (Hbd _ (cell_in _ _ Hi) Hin).
      * replace (i + S n) with (i + 1 + n) by lia. rewrite skipn_lset in Hd' by lia. exact Hd'.
Qed.

(** Literal [l]'s watch storage, as [wdata] holds it in [ma]. *)
Definition wd (s : state) (ma : Ma) (l : nat) (w : narr) : Prop :=
  exists W, arr ma (wdata s) W /\ nth_error W l = Some w.

(** Writing back the contents of a counted field and a cell past it. *)
Lemma firstn_lset_pre xs C x :
  pre xs C -> length xs < length C -> firstn (length xs + 1) (lset C (length xs) x) = xs ++ [x].
Proof.
  intros [pad ->] H. rewrite Nat.add_1_r, firstn_lset_S by exact H.
  rewrite firstn_app, Nat.sub_diag, firstn_all, app_nil_r. reflexivity.
Qed.

Section Rules.
(** The solver's handles and its number of variables. *)
Variables (s : state) (nv : nat).

(** Unpack [repr] into its two halves. *)
Ltac drep H := destruct H as (?a & ?ws & ?cs & ?C & ?A).

(** Field [f]'s array holds [cfld cs f]. *)
Lemma rep_fld mn ma a ws cs f : conc s nv mn ma a ws cs -> arr mn (floc s f) (cfld cs f).
Proof. intros C. exact (conc_arr _ _ _ _ _ _ _ _ _ C (own_fld s a ws f)). Qed.

(** A read of a field other than the reasons, within its contents. *)
Lemma rd_fld {U} f i x (k : nat -> itree E U) Q mn ma st :
  repr s nv mn ma st -> f <> FRsn -> nth_error (fv st f) i = Some x -> safe (k x) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) (floc s f) i) k) Q (mn, ma).
Proof.
  intros R Hf Hx Hk. drep R. eapply safe_read_n_bind; [exact (rep_fld _ _ _ _ _ f C) | | exact Hk].
  destruct f; try congruence;
    first [rewrite (a_fld _ _ _ A) by (unfold plain; tauto); exact Hx
          | eapply pre_nth_error; [first [apply (a_tr _ _ _ A) | apply (a_lim _ _ _ A) | apply (a_lrn _ _ _ A)]
                                  | exact Hx]].
Qed.

(** A read of [misc]. *)
Lemma rd_misc {U} i (k : nat -> itree E U) Q mn ma st :
  repr s nv mn ma st -> i < NMISC -> safe (k (nth i (fv st FMisc) 0)) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) (misc s) i) k) Q (mn, ma).
Proof.
  intros R Hi Hk. apply (rd_fld FMisc i (nth i (fv st FMisc) 0) k Q mn ma st R ltac:(discriminate)); [|exact Hk].
  apply nth_error_nth'. destruct R as (? & ? & ? & _ & A). rewrite (a_miscn _ _ _ A). exact Hi.
Qed.

(** A read of a reason: the clause offset + 1 of the clause it names. *)
Lemma rd_rsn {U} i r (k : nat -> itree E U) Q mn ma st :
  repr s nv mn ma st -> nth_error (rsn st) i = Some r -> safe (k (tr_rsn (db st) r)) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) (reason s) i) k) Q (mn, ma).
Proof.
  intros R Hr Hk. drep R. eapply safe_read_n_bind; [exact (rep_fld _ _ _ _ _ FRsn C) | | exact Hk].
  rewrite (a_rsn _ _ _ A), nth_error_map, Hr. reflexivity.
Qed.

(** A read of a watch list's length. *)
Lemma rd_wlen {U} l (k : nat -> itree E U) Q mn ma st :
  repr s nv mn ma st -> l < 2 * nv -> safe (k (length (nth l (wl st) []))) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) (wlen s) l) k) Q (mn, ma).
Proof.
  intros R Hl Hk. drep R. eapply safe_read_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 10 _ C eq_refl) | | exact Hk].
  rewrite <- (a_wl _ _ _ A l Hl). apply nth_error_nth'. rewrite (a_wln _ _ _ A). exact Hl.
Qed.

(** A read of a watch list's storage handle. *)
Lemma rd_wdata {U} l (k : narr -> itree E U) Q mn ma st :
  repr s nv mn ma st -> l < 2 * nv -> (forall w, wd s ma l w -> safe (k w) Q (mn, ma)) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Va) (idx := 0) (wdata s) l) k) Q (mn, ma).
Proof.
  intros R Hl Hk. drep R. pose proof (c_wd _ _ _ _ _ _ _ C) as Hw.
  destruct (nth_error ws l) as [w|] eqn:Ew; [|apply nth_error_None in Ew; rewrite (c_wdn _ _ _ _ _ _ _ C) in Ew; lia].
  eapply safe_read_a_bind; [exact Hw | exact Ew |]. apply Hk. exists ws. auto.
Qed.

(** The storage [wd] names is the one [rep] holds. *)
Lemma wd_rep mn ma st a ws cs l w :
  rep s nv mn ma st a ws cs -> wd s ma l w -> nth_error ws l = Some w /\ l < 2 * nv.
Proof.
  intros [C A] (W & HW & Hl). rewrite (arr_inj _ _ _ _ HW (c_wd _ _ _ _ _ _ _ C)) in Hl.
  split; [exact Hl|]. rewrite <- (c_wdn _ _ _ _ _ _ _ C). apply nth_error_Some. congruence.
Qed.

(** A read from a watch list's storage, within the list: a clause offset. *)
Lemma rd_ws {U} l w i ci (k : nat -> itree E U) Q mn ma st :
  repr s nv mn ma st -> wd s ma l w -> nth_error (nth l (wl st) []) i = Some ci ->
  safe (k (off (db st) ci)) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) w i) k) Q (mn, ma).
Proof.
  intros R Hw Hi Hk. drep R. destruct (wd_rep _ _ _ _ _ _ _ _ (conj C A) Hw) as [Ew Hl].
  eapply safe_read_n_bind; [exact (conc_arr _ _ _ _ _ _ _ (13 + l) _ C Ew) | | exact Hk].
  eapply pre_nth_error; [exact (a_ws _ _ _ A l Hl) | ]. rewrite nth_error_map, Hi. reflexivity.
Qed.

(** A read of the arena reference. *)
Lemma rd_ref {U} (k : narr -> itree E U) Q mn ma st :
  repr s nv mn ma st -> (forall a, refp ma (arena s) a -> safe (k a) Q (mn, ma)) ->
  safe (ITree.bind (Global.read_ref (E := E) (V := Va) (idx := 0) (arena s)) k) Q (mn, ma).
Proof.
  intros R Hk. drep R. pose proof (c_ref _ _ _ _ _ _ _ C) as Hr.
  eapply safe_read_ref_bind; [exact Hr |]. now apply Hk.
Qed.

(** The arena [refp] names is the one [rep] holds. *)
Lemma ref_rep mn ma st a ws cs a' : rep s nv mn ma st a ws cs -> refp ma (arena s) a' -> a' = a.
Proof. intros [C _] H. exact (refp_inj (V := Solver.Va) _ _ _ _ H (c_ref _ _ _ _ _ _ _ C)). Qed.

(** A read from the arena, within the clauses. *)
Lemma rd_ar {U} a i x (k : nat -> itree E U) Q mn ma st :
  repr s nv mn ma st -> refp ma (arena s) a -> nth_error (enc (db st)) i = Some x -> safe (k x) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := E) (V := Vn) (idx := 0) a i) k) Q (mn, ma).
Proof.
  intros R Ha Hx Hk. drep R. rewrite (ref_rep _ _ _ _ _ _ _ (conj C A) Ha).
  eapply safe_read_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 12 _ C eq_refl) | | exact Hk].
  eapply pre_nth_error; [exact (a_ar _ _ _ A) | exact Hx].
Qed.

(** Pack the two halves into [repr]. *)
Lemma repr_of mn ma st a ws cs : conc s nv mn ma a ws cs -> abs nv st cs -> repr s nv mn ma st.
Proof. intros C A. exists a, ws, cs. split; assumption. Qed.

(** A write to a plain field; in [misc], away from the counters. *)
Lemma wr_plain {U} f i x (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> plain f -> (f = FMisc -> kept i) -> i < length (fv st f) ->
  (forall mn', repr s nv mn' ma (fset st f (lset (fv st f) i x)) -> safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (floc s f) i x) k) Q (mn, ma).
Proof.
  intros R Hf Hm Hi Hk. drep R. pose proof (a_fld _ _ _ A f Hf) as E.
  eapply safe_write_n_bind; [exact (rep_fld _ _ _ _ _ f C) | rewrite E; exact Hi |].
  apply Hk. eapply repr_of.
  - apply conc_awrite; [exact C | apply own_fld | rewrite E; exact Hi].
  - now apply abs_plain.
Qed.

(** A write to the reasons: [x] names clause [r] of the database. *)
Lemma wr_rsn {U} i r x (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> i < length (rsn st) -> x = tr_rsn (db st) r ->
  (forall mn', repr s nv mn' ma (fset st FRsn (lset (rsn st) i r)) -> safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (reason s) i x) k) Q (mn, ma).
Proof.
  intros R Hi -> Hk. drep R. pose proof (a_rsn _ _ _ A) as E.
  assert (Hi' : i < length (cfld cs FRsn)) by (rewrite E, length_map; exact Hi).
  eapply safe_write_n_bind; [exact (rep_fld _ _ _ _ _ FRsn C) | exact Hi' |].
  apply Hk. eapply repr_of.
  - apply (conc_awrite s nv mn ma a ws cs (fidx FRsn) _ i _ C); [apply own_fld | exact Hi'].
  - now apply abs_rsn.
Qed.

(** A write inside a counted field. *)
Lemma wr_seq {U} f i x (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> seqf f -> i < length (fv st f) ->
  (forall mn', repr s nv mn' ma (fset st f (lset (fv st f) i x)) -> safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (floc s f) i x) k) Q (mn, ma).
Proof.
  intros R Hf Hi Hk. drep R. destruct (abs_seq _ _ _ _ A Hf) as (Hp & _).
  assert (Hi' : i < length (cfld cs f)) by (pose proof (pre_length _ _ Hp); lia).
  eapply safe_write_n_bind; [exact (rep_fld _ _ _ _ _ f C) | exact Hi' |].
  apply Hk. eapply repr_of.
  - apply conc_awrite; [exact C | apply own_fld | exact Hi'].
  - now apply abs_seq_set.
Qed.

(** Setting a counted field's length, on the two halves. *)
Lemma len_step mn ma st a ws cs f n :
  conc s nv mn ma a ws cs -> abs nv st cs -> seqf f -> n <= capf nv f ->
  slot f < length (cfld cs FMisc) /\
  conc s nv (awrite mn (misc s) (slot f) n) ma a ws (lset cs (fidx FMisc) (lset (cfld cs FMisc) (slot f) n)) /\
  abs nv (fset (fset st FMisc (lset (fv st FMisc) (slot f) n)) f (firstn n (cfld cs f)))
    (lset cs (fidx FMisc) (lset (cfld cs FMisc) (slot f) n)).
Proof.
  intros C A Hf Hn. pose proof (a_fld _ _ _ A FMisc ltac:(unfold plain; tauto)) as E.
  assert (Hs : slot f < length (cfld cs FMisc)).
  { rewrite E, (a_miscn _ _ _ A). destruct Hf as [-> | [-> | ->]]; cbn; unfold NMISC, TLEN, TLLEN, LLEN; lia. }
  split; [exact Hs|]. split.
  - apply conc_awrite; [exact C | apply own_fld | exact Hs].
  - exact (abs_len _ _ _ f n A Hf Hn).
Qed.

(** Setting a counted field's length to [n]: the field becomes the first
    [n] elements of an array that starts with the old field. *)
Lemma wr_len {U} f n (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> seqf f -> n <= capf nv f ->
  (forall mn' C, pre (fv st f) C -> length C = capf nv f ->
     repr s nv mn' ma (fset (fset st FMisc (lset (fv st FMisc) (slot f) n)) f (firstn n C)) ->
     safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (misc s) (slot f) n) k) Q (mn, ma).
Proof.
  intros R Hf Hn Hk. drep R. destruct (abs_seq _ _ _ _ A Hf) as (Hp & Hc & _).
  destruct (len_step _ _ _ _ _ _ f n C A Hf Hn) as (Hs & C1 & A1).
  eapply safe_write_n_bind; [exact (rep_fld _ _ _ _ _ FMisc C) | exact Hs |].
  apply (Hk _ (cfld cs f)); [exact Hp | exact Hc | exact (repr_of _ _ _ _ _ _ C1 A1)].
Qed.

(** Cutting a counted field to its first [n] elements. *)
Lemma wr_shrink {U} f n (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> seqf f -> n <= length (fv st f) ->
  (forall mn', repr s nv mn' ma (fset (fset st FMisc (lset (fv st FMisc) (slot f) n)) f (firstn n (fv st f))) ->
     safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (misc s) (slot f) n) k) Q (mn, ma).
Proof.
  intros R Hf Hn Hk. assert (Hc : n <= capf nv f).
  { destruct R as (? & ? & cs & _ & A). destruct (abs_seq _ _ _ _ A Hf) as (Hp & Hc & _).
    pose proof (pre_length _ _ Hp). lia. }
  apply (wr_len f n k Q mn ma st R Hf Hc). intros mn' C' [pad ->] _ R'.
  rewrite firstn_app, (proj2 (Nat.sub_0_le _ _) Hn), firstn_O, app_nil_r in R'. exact (Hk _ R').
Qed.

(** Pushing [x] on a counted field, followed by [k]. *)
Lemma wr_push {U} f x (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> seqf f -> length (fv st f) < capf nv f ->
  (forall mn', repr s nv mn' ma
       (fset (fset st FMisc (lset (fv st FMisc) (slot f) (length (fv st f) + 1))) f (fv st f ++ [x])) ->
     safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (floc s f) (length (fv st f)) x)
          (fun _ => ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (misc s) (slot f)
                                  (length (fv st f) + 1)) k)) Q (mn, ma).
Proof.
  intros R Hf Hl Hk. drep R. destruct (abs_seq _ _ _ _ A Hf) as (Hp & Hc & _).
  assert (Hi : length (fv st f) < length (cfld cs f)) by lia.
  eapply safe_write_n_bind; [exact (rep_fld _ _ _ _ _ f C) | exact Hi |].
  pose proof (conc_awrite _ _ _ _ _ _ _ _ _ _ x C (own_fld s a ws f) Hi) as C1.
  pose proof (abs_pad _ _ _ f (length (fv st f)) x A Hf ltac:(lia)) as A1.
  destruct (len_step _ _ _ _ _ _ f (length (fv st f) + 1) C1 A1 Hf ltac:(lia)) as (Hs & C2 & A2).
  assert (Em : cfld (lset cs (fidx f) (lset (cfld cs f) (length (fv st f)) x)) FMisc = cfld cs FMisc).
  { apply nth_lset_ne. destruct Hf as [-> | [-> | ->]]; cbn; lia. }
  rewrite Em in Hs, C2, A2.
  pose proof (rep_fld _ _ _ _ _ FMisc C1) as Hm. rewrite Em in Hm.
  eapply safe_write_n_bind; [exact Hm | exact Hs |].
  apply Hk. eapply repr_of; [exact C2|].
  rewrite nth_lset_eq, firstn_lset_pre in A2 by (rewrite ?(a_len _ _ _ A); try exact Hp; pose proof (fidx_lt f); lia).
  exact A2.
Qed.

(** Pushing [x] on a counted field, as the last step. *)
Lemma wr_push_end f x Q mn ma st :
  repr s nv mn ma st -> seqf f -> length (fv st f) < capf nv f ->
  (forall mn', repr s nv mn' ma
       (fset (fset st FMisc (lset (fv st FMisc) (slot f) (length (fv st f) + 1))) f (fv st f ++ [x])) ->
     Q tt (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (floc s f) (length (fv st f)) x)
          (fun _ => Global.write_array (E := E) (V := Vn) (idx := 0) (misc s) (slot f)
                      (length (fv st f) + 1))) Q (mn, ma).
Proof.
  intros R Hf Hl HQ. apply safe_unbind2. apply wr_push; auto. intros mn' R'. apply safe_ret. auto.
Qed.

(** Writing entry [i] of literal [l]'s watch list: [x] is the offset of
    clause [ci]. *)
Lemma wr_ws {U} l w i ci x (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> wd s ma l w -> i < length (nth l (wl st) []) -> x = off (db st) ci ->
  (forall mn', repr s nv mn' ma (wset st (lset (wl st) l (lset (nth l (wl st) []) i ci))) ->
     safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) w i x) k) Q (mn, ma).
Proof.
  intros R Hw Hi -> Hk. drep R. destruct (wd_rep _ _ _ _ _ _ _ _ (conj C A) Hw) as [Ew Hl].
  assert (Hi' : i < length (cws cs l)).
  { pose proof (pre_length _ _ (a_ws _ _ _ A l Hl)). rewrite length_map in H. lia. }
  eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ (13 + l) _ C Ew) | exact Hi' |].
  apply Hk. eapply repr_of.
  - apply (conc_awrite s nv mn ma a ws cs (13 + l) w i _ C); [exact Ew | exact Hi'].
  - now apply abs_ws_set.
Qed.

(** Cutting literal [l]'s watch list to its first [n] entries. *)
Lemma wr_wlen {U} l n (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> l < 2 * nv -> n <= length (nth l (wl st) []) ->
  (forall mn', repr s nv mn' ma (wset st (lset (wl st) l (firstn n (nth l (wl st) [])))) ->
     safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) (wlen s) l n) k) Q (mn, ma).
Proof.
  intros R Hl Hn Hk. drep R.
  assert (Hl' : l < length (cwl cs)) by (rewrite (a_wln _ _ _ A); exact Hl).
  eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 10 _ C eq_refl) | exact Hl' |].
  apply Hk. eapply repr_of.
  - apply (conc_awrite s nv mn ma a ws cs 10 _ l _ C); [reflexivity | exact Hl'].
  - now apply abs_wlen_set.
Qed.

(** Writing literal [j] of clause [ci] in the arena [a]. *)
Lemma wr_ar {U} a ci cl j i x (k : unit -> itree E U) Q mn ma st :
  repr s nv mn ma st -> refp ma (arena s) a -> nth_error (db st) ci = Some cl -> j < length cl ->
  i = off (db st) ci + 1 + j ->
  (forall mn', repr s nv mn' ma (dset st (lset (db st) ci (lset cl j x))) -> safe (k tt) Q (mn', ma)) ->
  safe (ITree.bind (Global.write_array (E := E) (V := Vn) (idx := 0) a i x) k) Q (mn, ma).
Proof.
  intros R Ha Hc Hj -> Hk. drep R. rewrite (ref_rep _ _ _ _ _ _ _ (conj C A) Ha).
  assert (Hi : off (db st) ci + 1 + j < length (car cs)).
  { pose proof (pre_length _ _ (a_ar _ _ _ A)). pose proof (off_lt _ _ _ Hc). lia. }
  eapply safe_write_n_bind; [exact (conc_arr _ _ _ _ _ _ _ 12 _ C eq_refl) | exact Hi |].
  apply Hk. eapply repr_of.
  - apply (conc_awrite s nv mn ma _ ws cs 12 _ _ _ C); [reflexivity | exact Hi].
  - now apply abs_dset.
Qed.

(** The counters [abs] ties to lengths. *)
Lemma repr_counts mn ma st :
  repr s nv mn ma st ->
  nth TLEN (fv st FMisc) 0 = length (tr st) /\ nth TLLEN (fv st FMisc) 0 = length (lim st) /\
  nth LLEN (fv st FMisc) 0 = length (lrn st) /\ nth ALEN (fv st FMisc) 0 = length (enc (db st)) /\
  length (fv st FMisc) = NMISC /\ length (wl st) = 2 * nv.
Proof. intros (? & ? & ? & _ & A). repeat split; apply A. Qed.

End Rules.
