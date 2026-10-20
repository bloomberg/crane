(** What a DIMACS CNF file is, and the proof that [Solver.parse] reads
    exactly that.

    The accepted language, over the file's bytes (as [nat]s):
    - The file is cut into lines at every newline (byte 10).
    - A line starting with ['c'] (99) is a comment and is dropped.  The
      ['c'] must be the line's first byte: an indented comment is not one.
    - A line starting with ['%'] (37) ends the formula; it and everything
      after it are ignored (the SATLIB trailer [%] / [0]).
    - The remaining lines are cut into tokens: maximal runs of bytes that
      are not whitespace, where whitespace is space, [\t], [\n], [\v],
      [\f] and [\r] (bytes 32 and 9 to 13).
    - The first four tokens must be [p], [cnf], [nv] and [nc], where [nv]
      and [nc] are numbers: non-empty strings of decimal digits, leading
      zeros allowed.  [nv] is at most [MAXVAR] = 2^32.
    - The other tokens are the clauses, each a sequence of literals followed
      by the token [0] (any all-zero digit string).  A literal is [x] or
      [-x] for a number [x] with [1 <= x <= nv].  Nothing else is a token
      here: [-0], [+1], [0x2], a second header or any other junk makes the
      file invalid, and so does a last clause without its [0].
    - The number of clauses must be exactly [nc].

    The formula is in the solver's encoding: DIMACS literal [x] is
    [2 * (x - 1)] and [-x] is [2 * (x - 1) + 1], so [SolverSat.satisfies]
    applies to it directly (DIMACS variable [x] is the solver's [x - 1]).

    The definitions below say this declaratively, by plain structural
    recursion; [Solver.parse] is the tail-recursive program that is
    extracted, and [parse_sound], [parse_complete] and [dimacs_det] say it
    accepts exactly these files and returns exactly their formula. *)
From Stdlib Require Import List PeanoNat Lia Bool.
Require Import SatVec VecSem Solver SolverSat.
Import ListNotations.
Import Solver.

(** * The accepted format *)

(** [bs] cut at every byte [sep] accepts; [k] separators give [k + 1]
    pieces. *)
Fixpoint split_on (sep : nat -> bool) (bs : list nat) : list (list nat) :=
  match bs with
  | [] => [[]]
  | b :: bs' =>
    if sep b then [] :: split_on sep bs'
    else match split_on sep bs' with
         | w :: ws => (b :: w) :: ws
         | [] => [[b]]
         end
  end.

(** Cut at newlines (byte 10). *)
Definition lines (bs : list nat) : list (list nat) := split_on (Nat.eqb 10) bs.

Definition starts_with (b : nat) (l : list nat) : bool :=
  match l with b' :: _ => Nat.eqb b' b | [] => false end.

(** The lines before the first one starting with ['%'] (37), without the
    comment lines, which start with ['c'] (99). *)
Fixpoint content (ls : list (list nat)) : list (list nat) :=
  match ls with
  | [] => []
  | l :: ls' =>
    if starts_with 37 l then []
    else if starts_with 99 l then content ls'
    else l :: content ls'
  end.

Definition is_nil (w : list nat) : bool := match w with [] => true | _ :: _ => false end.

(** The non-empty runs of non-whitespace ([Solver.is_space]) in a line. *)
Definition words (l : list nat) : list (list nat) :=
  filter (fun w => negb (is_nil w)) (split_on is_space l).

Definition tokens (bs : list nat) : list (list nat) := concat (map words (content (lines bs))).

(** The value of a string of decimal digits (['0'] is byte 48). *)
Definition dval (w : list nat) : nat := fold_left (fun a d => 10 * a + (d - 48)) w 0.

Definition number (w : list nat) (n : nat) : Prop :=
  w <> [] /\ Forall (fun d => is_digit d = true) w /\ dval w = n.

(** [w] is DIMACS literal [x] or [-x] (['-'] is byte 45), [1 <= x <= nv],
    and [l] its encoding. *)
Definition literal (nv : nat) (w : list nat) (l : nat) : Prop :=
  exists x, 1 <= x <= nv /\
    ((number w x /\ l = 2 * (x - 1)) \/
     (exists w', w = 45 :: w' /\ number w' x /\ l = 2 * (x - 1) + 1)).

(** The tokens [ts] are the clauses [F], each its literals and then [0]. *)
Inductive clauses (nv : nat) : list (list nat) -> list (list nat) -> Prop :=
| cl_nil : clauses nv [] []
| cl_cons ws z ts c F :
    Forall2 (literal nv) ws c -> number z 0 -> clauses nv ts F ->
    clauses nv (ws ++ z :: ts) (c :: F).

(** The bytes [bs] are a DIMACS CNF file for the formula [F]: the header
    [p cnf nv nc] ([p] is byte 112, [cnf] bytes 99 110 102), then the
    clauses, exactly [nc] of them. *)
Definition dimacs (bs : list nat) (F : list (list nat)) : Prop :=
  exists nvw ncw ts nv,
    tokens bs = [112] :: [99; 110; 102] :: nvw :: ncw :: ts /\
    number nvw nv /\ nv <= MAXVAR /\ number ncw (length F) /\ clauses nv ts F.

(** * Tokens *)

Lemma split_on_cons sep bs : exists w ws, split_on sep bs = w :: ws.
Proof.
  induction bs as [|b bs (w & ws & E)]; cbn [split_on]; [eauto|].
  destruct (sep b); [eauto|]. rewrite E. eauto.
Qed.

Lemma split_tr_spec sep bs : forall cur acc w ws,
  split_on sep bs = w :: ws -> split_tr sep bs cur acc = rev acc ++ (rev cur ++ w) :: ws.
Proof.
  induction bs as [|b bs IH]; intros cur acc w ws E; cbn [split_on split_tr] in *.
  - injection E as <- <-. rewrite !rev_append_rev. reflexivity.
  - destruct (split_on_cons sep bs) as (w' & ws' & E').
    destruct (sep b).
    + injection E as <- <-. rewrite (IH _ _ _ _ E'), E'. cbn [rev].
      rewrite rev_append_rev, <- app_assoc. reflexivity.
    + rewrite E' in E. injection E as <- <-. rewrite (IH _ _ _ _ E'). cbn [rev].
      rewrite <- app_assoc. reflexivity.
Qed.

Lemma split_tr_nil sep bs : split_tr sep bs [] [] = split_on sep bs.
Proof.
  destruct (split_on_cons sep bs) as (w & ws & E).
  rewrite (split_tr_spec _ _ _ _ _ _ E), E. reflexivity.
Qed.

Lemma content_tr_spec ls : forall acc, content_tr ls acc = rev acc ++ content ls.
Proof.
  induction ls as [|l ls IH]; intros acc; cbn [content_tr content].
  - rewrite rev_append_rev. reflexivity.
  - destruct l as [|b l']; cbn [starts_with].
    + rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
    + destruct (Nat.eqb b 37); [rewrite rev_append_rev; reflexivity|].
      destruct (Nat.eqb b 99); [apply IH|].
      rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma nonempty_tr_spec ws : forall acc,
  nonempty_tr ws acc = rev (filter (fun w => negb (is_nil w)) ws) ++ acc.
Proof.
  induction ws as [|w ws IH]; intros acc; [reflexivity|].
  destruct w as [|b w]; cbn [nonempty_tr filter is_nil negb]; rewrite IH; [reflexivity|].
  cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma words_tr_spec ls : forall acc, words_tr ls acc = rev (concat (map words ls)) ++ acc.
Proof.
  induction ls as [|l ls IH]; intros acc; [reflexivity|].
  cbn [words_tr map concat]. rewrite IH, nonempty_tr_spec, split_tr_nil.
  unfold words. rewrite rev_app_distr, <- app_assoc. reflexivity.
Qed.

Theorem tokens_tr_eq bs : tokens_tr bs = tokens bs.
Proof.
  unfold tokens_tr, tokens, lines.
  rewrite split_tr_nil, content_tr_spec. cbn [rev app].
  rewrite words_tr_spec, rev_append_rev, !app_nil_r, rev_involutive. reflexivity.
Qed.

(** * Numbers and literals *)

Lemma fold_ge w : forall acc, acc <= fold_left (fun a d => 10 * a + (d - 48)) w acc.
Proof. induction w as [|d w IH]; intros acc; cbn [fold_left]; [lia|]. specialize (IH (10 * acc + (d - 48))). lia. Qed.

(** [sdigits] is the exact value, cut off above [cap]: once the
    accumulator passes [cap] it can only grow, so stopping it changes no
    answer. *)
Lemma sdigits_eq cap w : forall acc,
  sdigits cap acc w =
  if forallb is_digit w then
    (if fold_left (fun a d => 10 * a + (d - 48)) w acc <=? cap
     then Some (fold_left (fun a d => 10 * a + (d - 48)) w acc) else None)
  else None.
Proof.
  induction w as [|d w IH]; intros acc; cbn [sdigits forallb fold_left]; [reflexivity|].
  destruct (is_digit d); cbn [andb]; [|reflexivity].
  rewrite IH. destruct (Nat.ltb_spec cap acc); [|reflexivity].
  destruct (forallb is_digit w); [|reflexivity].
  pose proof (fold_ge w acc). pose proof (fold_ge w (10 * acc + (d - 48))).
  rewrite (proj2 (Nat.leb_gt _ cap)) by lia.
  rewrite (proj2 (Nat.leb_gt _ cap)) by lia. reflexivity.
Qed.

Theorem snum_spec cap w v : snum cap w = Some v <-> number w v /\ v <= cap.
Proof.
  unfold snum, number, dval. destruct w as [|d w'].
  - split; [discriminate | intros ((H & _) & _); now contradiction H].
  - rewrite sdigits_eq. destruct (forallb is_digit (d :: w')) eqn:E.
    + match goal with |- context [Nat.leb ?a cap] => destruct (Nat.leb_spec a cap) end.
      * split.
        -- intros Hs. injection Hs as <-. split; [|assumption]. split; [discriminate|]. split; [|reflexivity].
           apply Forall_forall. intros y Hy. rewrite forallb_forall in E. auto.
        -- intros ((_ & _ & Hv) & _). now rewrite Hv.
      * split; [discriminate|]. intros ((_ & _ & Hv) & Hc). lia.
    + split; [discriminate|]. intros ((_ & Hf & _) & _).
      rewrite <- not_true_iff_false in E. exfalso. apply E, forallb_forall. intros y Hy.
      rewrite Forall_forall in Hf. auto.
Qed.

Lemma number_det w x y : number w x -> number w y -> x = y.
Proof. intros (_ & _ & H1) (_ & _ & H2). congruence. Qed.

Theorem is_zero_spec w : is_zero w = true <-> number w 0.
Proof.
  unfold is_zero. destruct (snum 0 w) eqn:E.
  - split; [intros _ | reflexivity]. apply snum_spec in E as (Hn & Hle).
    replace n with 0 in Hn by lia. exact Hn.
  - split; [discriminate|]. intros Hn.
    assert (snum 0 w = Some 0) by (apply snum_spec; auto). congruence.
Qed.

Lemma not_number_45 w x : number (45 :: w) x -> False.
Proof. intros (_ & Hf & _). apply Forall_inv in Hf. discriminate Hf. Qed.

Theorem slit_spec nv w l : slit nv w = Some l <-> literal nv w l.
Proof.
  unfold slit, literal. destruct w as [|b w'].
  - cbn. split; [discriminate|].
    intros (x & _ & [((Hn & _ & _) & _) | (w' & Hw & _)]); [now contradiction Hn | discriminate].
  - cbv beta iota zeta. destruct (Nat.eqb_spec b 45) as [-> | Hb]; cbn [fst snd].
    + destruct (snum nv w') as [[|v]|] eqn:E.
      * split; [discriminate|].
        intros (x & Hx & [(Hn & _) | (w0 & Hw & Hn & _)]); [exfalso; eapply not_number_45; eauto|].
        injection Hw as <-. apply snum_spec in E as (E & _). pose proof (number_det _ _ _ E Hn). lia.
      * apply snum_spec in E as (Hn & Hle). split.
        -- intros H. injection H as <-. exists (S v). split; [lia|]. right. exists w'.
           split; [reflexivity|]. split; [exact Hn | lia].
        -- intros (x & Hx & [(Hn' & _) | (w0 & Hw & Hn' & Hl)]); [exfalso; eapply not_number_45; eauto|].
           injection Hw as <-. pose proof (number_det _ _ _ Hn Hn'). subst. f_equal. lia.
      * split; [discriminate|].
        intros (x & Hx & [(Hn & _) | (w0 & Hw & Hn & _)]); [exfalso; eapply not_number_45; eauto|].
        injection Hw as <-. assert (snum nv w' = Some x) by (apply snum_spec; split; [exact Hn | lia]).
        congruence.
    + destruct (snum nv (b :: w')) as [[|v]|] eqn:E.
      * split; [discriminate|].
        intros (x & Hx & [(Hn & _) | (w0 & Hw & _)]); [| injection Hw; congruence].
        apply snum_spec in E as (E & _). pose proof (number_det _ _ _ E Hn). lia.
      * apply snum_spec in E as (Hn & Hle). split.
        -- intros H. injection H as <-. exists (S v). split; [lia|]. left. split; [exact Hn | lia].
        -- intros (x & Hx & [(Hn' & Hl) | (w0 & Hw & _)]); [| injection Hw; congruence].
           pose proof (number_det _ _ _ Hn Hn'). subst. f_equal. lia.
      * split; [discriminate|].
        intros (x & Hx & [(Hn & _) | (w0 & Hw & _)]); [| injection Hw; congruence].
        assert (snum nv (b :: w') = Some x) by (apply snum_spec; split; [exact Hn | lia]).
        congruence.
Qed.

Lemma literal_det nv w l l' : literal nv w l -> literal nv w l' -> l = l'.
Proof.
  intros (x & _ & [(Hn & ->) | (w0 & -> & Hn & ->)]) (y & _ & [(Hm & ->) | (w1 & Hw & Hm & ->)]).
  - now rewrite (number_det _ _ _ Hn Hm).
  - rewrite Hw in Hn. exfalso. eapply not_number_45; eauto.
  - exfalso. eapply not_number_45; eauto.
  - injection Hw as <-. now rewrite (number_det _ _ _ Hn Hm).
Qed.

Lemma literal_nz nv w l : literal nv w l -> number w 0 -> False.
Proof.
  intros (x & Hx & [(Hn & _) | (w0 & -> & _ & _)]) Hz.
  - pose proof (number_det _ _ _ Hn Hz). lia.
  - eapply not_number_45; eauto.
Qed.

(** * Determinism *)

Lemma F2_det nv ws c : Forall2 (literal nv) ws c -> forall c', Forall2 (literal nv) ws c' -> c = c'.
Proof.
  induction 1 as [|w l ws c Hl _ IH]; intros c' H'; inversion H'; subst; [reflexivity|].
  f_equal; [eapply literal_det; eauto | auto].
Qed.

Lemma F2_nz nv ws c : Forall2 (literal nv) ws c -> Forall (fun w => ~ number w 0) ws.
Proof. induction 1; constructor; auto. intros Hz. eapply literal_nz; eauto. Qed.

(** The first zero token ends the clause. *)
Lemma app_zero_unique ws : forall ws' z z' ts ts',
  ws ++ z :: ts = ws' ++ z' :: ts' ->
  Forall (fun w => ~ number w 0) ws -> Forall (fun w => ~ number w 0) ws' ->
  number z 0 -> number z' 0 -> ws = ws' /\ z = z' /\ ts = ts'.
Proof.
  induction ws as [|w ws IH]; intros [|w' ws'] z z' ts ts' E H1 H2 Hz Hz'; cbn in E.
  - injection E as -> ->. auto.
  - injection E as -> _. exfalso. exact (Forall_inv H2 Hz).
  - injection E as <- _. exfalso. exact (Forall_inv H1 Hz').
  - injection E as -> E.
    destruct (IH ws' z z' ts ts' E (Forall_inv_tail H1) (Forall_inv_tail H2) Hz Hz') as (-> & -> & ->).
    auto.
Qed.

Lemma clauses_inv nv ts F :
  clauses nv ts F ->
  (ts = [] /\ F = []) \/
  exists ws z ts' c F', ts = ws ++ z :: ts' /\ F = c :: F' /\
    Forall2 (literal nv) ws c /\ number z 0 /\ clauses nv ts' F'.
Proof. destruct 1; [left; auto | right; eauto 10]. Qed.

Lemma clauses_det nv ts F : clauses nv ts F -> forall F', clauses nv ts F' -> F = F'.
Proof.
  induction 1 as [|ws z ts c F Hws Hz _ IH]; intros F' H';
    apply clauses_inv in H' as [(E & ->) | (ws' & z' & ts' & c' & F'' & E & -> & H1 & H2 & H3)].
  - reflexivity.
  - destruct ws'; discriminate.
  - destruct ws; discriminate.
  - destruct (app_zero_unique _ _ _ _ _ _ E (F2_nz _ _ _ Hws) (F2_nz _ _ _ H1) Hz H2) as (<- & <- & <-).
    f_equal; [eapply F2_det; eauto | auto].
Qed.

(** A file is the encoding of at most one formula. *)
Theorem dimacs_det bs F F' : dimacs bs F -> dimacs bs F' -> F = F'.
Proof.
  intros (nvw & ncw & ts & nv & Et & Hnv & _ & _ & Hcl) (nvw' & ncw' & ts' & nv' & Et' & Hnv' & _ & _ & Hcl').
  rewrite Et in Et'. injection Et' as <- <- <-.
  pose proof (number_det _ _ _ Hnv Hnv') as <-. eapply clauses_det; eauto.
Qed.

(** * The clause parser *)

(** [ts] finishes the clause whose literals so far are [pre], then is
    clauses; [F] is the clauses, that one first.  With [pre] empty the
    clause may also not have begun, at the end of the input. *)
Definition after (nv : nat) (pre : list nat) (ts : list (list nat)) (F : list (list nat)) : Prop :=
  (pre = [] /\ ts = [] /\ F = []) \/
  exists ws z ts' c F', ts = ws ++ z :: ts' /\ Forall2 (literal nv) ws c /\
    number z 0 /\ clauses nv ts' F' /\ F = (pre ++ c) :: F'.

Lemma clauses_after nv ts F : clauses nv ts F <-> after nv [] ts F.
Proof.
  split.
  - intros H. apply clauses_inv in H as [(-> & ->) | (ws & z & ts' & c & F' & -> & -> & H1 & H2 & H3)].
    + left. auto.
    + right. exists ws, z, ts', c, F'. auto.
  - intros [(_ & -> & ->) | (ws & z & ts' & c & F' & -> & H1 & H2 & H3 & ->)]; constructor; auto.
Qed.

Lemma pclauses_sound nv ts : forall cur acc cnt maxv G k m,
  pclauses nv ts cur acc cnt maxv = Some (G, k, m) ->
  exists F, after nv (rev cur) ts F /\ G = rev acc ++ F /\ k = cnt + length F.
Proof.
  induction ts as [|t ts IH]; intros cur acc cnt maxv G k m H; cbn [pclauses] in H.
  - destruct cur; [|discriminate]. injection H as <- <- <-. exists [].
    split; [left; auto|]. rewrite rev_append_rev. cbn [length]. split; [reflexivity | lia].
  - destruct (is_zero t) eqn:Ez.
    + apply IH in H as (F1 & HA & -> & ->). apply is_zero_spec in Ez.
      exists (rev cur :: F1). split; [|split].
      * right. exists [], t, ts, [], F1. split; [reflexivity|]. split; [constructor|].
        split; [exact Ez|]. split; [apply clauses_after; exact HA | now rewrite app_nil_r].
      * rewrite rev_append_rev, app_nil_r. cbn [rev]. rewrite <- app_assoc. reflexivity.
      * cbn [length]. lia.
    + destruct (slit nv t) as [l|] eqn:El; [|discriminate].
      apply IH in H as (F1 & HA & -> & ->). exists F1. split; [|split; reflexivity].
      apply slit_spec in El.
      destruct HA as [(E & _ & _) | (ws & z & ts' & c & F' & -> & H1 & H2 & H3 & ->)].
      * cbn [rev] in E. apply app_eq_nil in E as [_ E]. discriminate.
      * right. exists (t :: ws), z, ts', (l :: c), F'.
        split; [reflexivity|]. split; [constructor; auto|]. split; [exact H2|]. split; [exact H3|].
        cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma pclauses_complete nv ts : forall cur acc cnt maxv F,
  after nv (rev cur) ts F -> pclauses nv ts cur acc cnt maxv <> None.
Proof.
  induction ts as [|t ts IH]; intros cur acc cnt maxv F HA; cbn [pclauses].
  - destruct HA as [(E & _ & _) | (ws & z & ts' & c & F' & E & _)].
    + destruct cur as [|x cur]; [discriminate|].
      exfalso. cbn [rev] in E. apply app_eq_nil in E as [_ E]. discriminate.
    + destruct ws; discriminate.
  - destruct HA as [(_ & E & _) | (ws & z & ts' & c & F' & E & H1 & H2 & H3 & ->)]; [discriminate|].
    destruct ws as [|w ws]; cbn [app] in E; injection E as -> ->.
    + assert (Hz : is_zero z = true) by (apply is_zero_spec; exact H2). rewrite Hz.
      apply (IH [] _ _ _ F'). apply clauses_after. exact H3.
    + inversion H1 as [|? l ? c1 Hl Hc1]; subst.
      assert (Hz : is_zero w = false).
      { destruct (is_zero w) eqn:Ez; [|reflexivity].
        apply is_zero_spec in Ez. exfalso. eapply literal_nz; eauto. }
      rewrite Hz. assert (Hs : slit nv w = Some l) by (apply slit_spec; exact Hl). rewrite Hs.
      eapply (IH (l :: cur)). right. exists ws, z, ts', c1, F'.
      split; [reflexivity|]. split; [exact Hc1|]. split; [exact H2|]. split; [exact H3|]. reflexivity.
Qed.

Lemma Forall_rev' {A} (P : A -> Prop) l : Forall P l -> Forall P (rev l).
Proof. rewrite !Forall_forall. intros H x Hx. apply H. now apply in_rev. Qed.

(** [maxv] ends up at least as large as every variable, and no larger than
    [nv]. *)
Lemma pclauses_lits nv ts : forall cur acc cnt maxv G k m,
  pclauses nv ts cur acc cnt maxv = Some (G, k, m) ->
  lits_below (2 * maxv) acc -> Forall (fun l => l < 2 * maxv) cur -> maxv <= nv ->
  lits_below (2 * m) G /\ m <= nv.
Proof.
  unfold lits_below.
  induction ts as [|t ts IH]; intros cur acc cnt maxv G k m H Ha Hc Hm; cbn [pclauses] in H.
  - destruct cur; [|discriminate]. injection H as <- <- <-.
    rewrite rev_append_rev, app_nil_r. split; [now apply Forall_rev' | exact Hm].
  - destruct (is_zero t).
    + eapply IH; [exact H | | constructor | exact Hm].
      constructor; [| exact Ha]. rewrite rev_append_rev, app_nil_r. now apply Forall_rev'.
    + destruct (slit nv t) as [l|] eqn:El; [|discriminate].
      apply slit_spec in El as (x & Hx & Hl).
      assert (Hq : l / 2 + 1 = x).
      { pose proof (Nat.div_mod_eq l 2). pose proof (Nat.mod_upper_bound l 2 ltac:(lia)).
        destruct Hl as [(_ & ->) | (w' & _ & _ & ->)]; lia. }
      assert (Hlt : l < 2 * x) by (destruct Hl as [(_ & ->) | (w' & _ & _ & ->)]; lia).
      rewrite Hq in H.
      pose proof (Nat.le_max_l maxv x). pose proof (Nat.le_max_r maxv x).
      eapply IH; [exact H | | | ].
      * eapply Forall_impl; [| exact Ha]. intros c Hc'.
        eapply Forall_impl; [| exact Hc']. intros y Hy. cbv beta in Hy. lia.
      * constructor; [lia|]. eapply Forall_impl; [| exact Hc]. intros y Hy. cbv beta in Hy. lia.
      * apply Nat.max_lub; lia.
Qed.

(** * The parser *)

Theorem parse_sound bs nvars F :
  parse bs = Some (nvars, F) -> dimacs bs F /\ lits_below (2 * nvars) F /\ nvars <= MAXVAR.
Proof.
  intros H. unfold parse in H. rewrite tokens_tr_eq in H.
  destruct (tokens bs) as [|tp [|tc [|tnv [|tnc ts]]]] eqn:Et; cbv beta iota zeta in H;
    try discriminate H.
  destruct tp as [|p [|? ?]]; cbv beta iota in H; try discriminate H.
  destruct tc as [|c [|n [|f [|? ?]]]]; cbv beta iota in H; try discriminate H.
  destruct (Nat.eqb_spec p 112), (Nat.eqb_spec c 99), (Nat.eqb_spec n 110), (Nat.eqb_spec f 102);
    cbn [andb] in H; try discriminate H. subst.
  destruct (snum MAXVAR tnv) as [nv|] eqn:Env; cbv beta iota in H; [|discriminate H].
  destruct (pclauses nv ts [] [] 0 0) as [[[G cnt] m]|] eqn:Ep; cbv beta iota in H; [|discriminate H].
  destruct (snum cnt tnc) as [k|] eqn:Ek; cbv beta iota in H; [|discriminate H].
  destruct (Nat.eqb_spec k cnt) as [->|]; [|discriminate H]. injection H as -> ->.
  apply snum_spec in Env as (Hnv & Hle). apply snum_spec in Ek as (Hnc & _).
  destruct (pclauses_sound _ _ _ _ _ _ _ _ _ Ep) as (F' & HA & EG & Ecnt).
  cbn [rev app] in EG, Ecnt. subst.
  destruct (pclauses_lits _ _ _ _ _ _ _ _ _ Ep) as (HL & Hm); [constructor | constructor | lia |].
  split; [| split; [exact HL | lia]].
  exists tnv, tnc, ts, nv. split; [exact Et|]. split; [exact Hnv|]. split; [exact Hle|].
  split; [exact Hnc | apply clauses_after; exact HA].
Qed.

Theorem parse_complete bs F : dimacs bs F -> exists nvars, parse bs = Some (nvars, F).
Proof.
  intros (nvw & ncw & ts & nv & Et & Hnv & Hle & Hnc & Hcl).
  assert (Env : snum MAXVAR nvw = Some nv) by (apply snum_spec; auto).
  destruct (pclauses nv ts [] [] 0 0) as [[[G cnt] m]|] eqn:Ep.
  2: { exfalso. exact (pclauses_complete nv ts [] [] 0 0 F (proj1 (clauses_after _ _ _) Hcl) Ep). }
  destruct (pclauses_sound _ _ _ _ _ _ _ _ _ Ep) as (F' & HA & EG & Ecnt).
  cbn [rev app Nat.add] in EG, Ecnt. subst G cnt.
  apply clauses_after in HA. pose proof (clauses_det _ _ _ Hcl _ HA). subst F'.
  assert (Enc : snum (length F) ncw = Some (length F)) by (apply snum_spec; auto).
  exists m. unfold parse. rewrite tokens_tr_eq, Et. cbv beta iota zeta.
  rewrite !Nat.eqb_refl. cbn [andb].
  rewrite Env. cbv beta iota. rewrite Ep. cbv beta iota. rewrite Enc, Nat.eqb_refl. reflexivity.
Qed.

Corollary parse_none bs : parse bs = None -> ~ exists F, dimacs bs F.
Proof. intros H (F & HF). destruct (parse_complete _ _ HF) as (n & E). congruence. Qed.

(** * Sanity checks *)

(** ["p cnf 1 1\nc x\n1 0\n"] *)
Example tokens_ex :
  tokens [112; 32; 99; 110; 102; 32; 49; 32; 49; 10; 99; 32; 120; 10; 49; 32; 48; 10]
  = [[112]; [99; 110; 102]; [49]; [49]; [49]; [48]].
Proof. reflexivity. Qed.

(** ["1 -2 0"] over 3 variables: one clause, DIMACS 1 and -2. *)
Example pclauses_ex : pclauses 3 [[49]; [45; 50]; [48]] [] [] 0 0 = Some ([[0; 3]], 1, 2).
Proof. reflexivity. Qed.
