(** Layer 2 of the proof: the invariants of the abstract solver state, and
    the pure facts about literals, levels and watch lists they need.

    UNSAT soundness is proved by contradiction: fix a valuation [val] that
    satisfies the input formula, and show that the solver never answers 0.
    "Entailed by the formula" then becomes "true under [val]", and every
    invariant is a plain statement about the current state:

    - [Core]: every database clause is true under [val] (I4); the trail
      lists exactly the assigned variables, each once and true (I2); levels
      are the decision segments of trail positions (I2); every propagated
      literal's reason has it at position 0 and every other literal false
      and earlier on the trail (I3); every reason-less literal is a decision
      or comes before the first decision; every level-0 literal is true
      under [val] (I5); the queue head lies between the last decision and
      the end of the trail.
    - [Wch]: a clause occurs in a watch list no more often than it has that
      literal at position 0 or 1.  This is the membership half of I6, and
      UNSAT soundness needs it: [prop_watch] never reads the value of
      [c[1]], it relies on [c[1]] being the literal just made false.
    - [Seen0]: the analysis marks are clear between conflicts. *)
From Stdlib Require Import List PeanoNat Lia Bool Permutation.
Require Import SatVec VecSem Solver SolverSat SolverRepr.
Import ListNotations.
Import Solver.

Notation asg st := (fv st FAsg).
Notation lvl st := (fv st FLvl).
Notation rsn st := (fv st FRsn).
Notation sn st := (fv st FSn).
Notation tr st := (fv st FTr).
Notation lim st := (fv st FLim).
Notation qhead st := (nth QHEAD (fv st FMisc) 0).

(** * Literals *)

(** What [lit_value] answers when the variable holds [a]. *)
Definition lval_of (a l : nat) : nat :=
  if Nat.eqb a 0 then 0 else if Nat.eqb (Nat.modulo l 2) 0 then a else 3 - a.

Definition lval (A : list nat) (l : nat) : nat := lval_of (nth (lvar l) A 0) l.

Lemma div2_eq q r : r < 2 -> (2 * q + r) / 2 = q.
Proof. intros. symmetry. apply (Nat.div_unique _ _ _ r); lia. Qed.

Lemma mod2_eq q r : r < 2 -> (2 * q + r) mod 2 = r.
Proof. intros. symmetry. apply (Nat.mod_unique _ _ q); lia. Qed.

Lemma lit_cases l : (l = 2 * lvar l /\ l mod 2 = 0) \/ (l = 2 * lvar l + 1 /\ l mod 2 = 1).
Proof.
  unfold lvar. pose proof (Nat.div_mod_eq l 2). pose proof (Nat.mod_upper_bound l 2).
  assert (l mod 2 = 0 \/ l mod 2 = 1) as [E | E] by lia; [left | right]; split; lia.
Qed.

Lemma lvar_2v v : lvar (2 * v) = v.
Proof. unfold lvar. pose proof (div2_eq v 0) as H. rewrite Nat.add_0_r in H. apply H. lia. Qed.

Lemma lvar_2v1 v : lvar (2 * v + 1) = v.
Proof. unfold lvar. apply div2_eq. lia. Qed.

Lemma mod_2v v : (2 * v) mod 2 = 0.
Proof. pose proof (mod2_eq v 0) as H. rewrite Nat.add_0_r in H. apply H. lia. Qed.

Lemma mod_2v1 v : (2 * v + 1) mod 2 = 1.
Proof. apply mod2_eq. lia. Qed.

Lemma lneg_cases l :
  (l mod 2 = 0 /\ lneg l = l + 1) \/ (l mod 2 = 1 /\ lneg l = l - 1).
Proof. unfold lneg. destruct (lit_cases l) as [[_ E] | [_ E]]; rewrite E; cbn; auto. Qed.

Lemma lvar_lneg l : lvar (lneg l) = lvar l.
Proof.
  destruct (lit_cases l) as [[E M] | [E M]]; unfold lneg; rewrite M; cbn.
  - rewrite E at 1. apply lvar_2v1.
  - rewrite E at 1. replace (2 * lvar l + 1 - 1) with (2 * lvar l) by lia. apply lvar_2v.
Qed.

Lemma lneg_mod l : lneg l mod 2 = 1 - l mod 2.
Proof.
  destruct (lit_cases l) as [[E M] | [E M]]; unfold lneg; rewrite M; cbn.
  - rewrite E at 1. apply mod_2v1.
  - rewrite E at 1. replace (2 * lvar l + 1 - 1) with (2 * lvar l) by lia. apply mod_2v.
Qed.

Lemma lneg_lneg l : lneg (lneg l) = l.
Proof.
  destruct (lit_cases l) as [[E M] | [E M]]; set (v := lvar l) in *; clearbody v; subst l; unfold lneg.
  - rewrite mod_2v. cbn [Nat.eqb]. rewrite mod_2v1. cbn [Nat.eqb]. lia.
  - rewrite mod_2v1. cbn [Nat.eqb]. replace (2 * v + 1 - 1) with (2 * v) by lia.
    rewrite mod_2v. cbn [Nat.eqb]. lia.
Qed.

Lemma lneg_neq l : lneg l <> l.
Proof. intros E. pose proof (lneg_mod l) as M. rewrite E in M. pose proof (Nat.mod_upper_bound l 2). lia. Qed.

Lemma lit_eq a b : lvar a = lvar b -> a mod 2 = b mod 2 -> a = b.
Proof.
  intros E M. destruct (lit_cases a) as [[Ea Ma] | [Ea Ma]], (lit_cases b) as [[Eb Mb] | [Eb Mb]]; lia.
Qed.

Lemma lval_le2 A l : nth (lvar l) A 0 <= 2 -> lval A l <= 2.
Proof.
  unfold lval, lval_of. intros.
  destruct (Nat.eqb_spec (nth (lvar l) A 0) 0); [lia|]. destruct (Nat.eqb (l mod 2) 0); lia.
Qed.

Ltac eqbs := repeat match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y) end.

(** Case on the parity of [l] and substitute [l := 2v] or [2v+1]. *)
Ltac par l :=
  let v := fresh "v" in let E := fresh "E" in let M := fresh "M" in
  destruct (lit_cases l) as [[E M] | [E M]]; set (v := lvar l) in *; clearbody v; subst l;
  rewrite ?lvar_2v, ?lvar_2v1, ?mod_2v, ?mod_2v1 in *.

Lemma lval_zero A l : nth (lvar l) A 0 <= 2 -> lval A l = 0 <-> nth (lvar l) A 0 = 0.
Proof. unfold lval, lval_of. revert l. intros l. par l; cbn [Nat.eqb]; eqbs; lia. Qed.

Lemma lneg_2v v : lneg (2 * v) = 2 * v + 1.
Proof. unfold lneg. now rewrite mod_2v. Qed.

Lemma lneg_2v1 v : lneg (2 * v + 1) = 2 * v.
Proof. unfold lneg. rewrite mod_2v1. cbn [Nat.eqb]. lia. Qed.

Ltac parn l := par l; rewrite ?lneg_2v, ?lneg_2v1, ?lvar_2v, ?lvar_2v1, ?mod_2v, ?mod_2v1 in *.

Lemma lval_lneg A l : nth (lvar l) A 0 <= 2 ->
  lval A (lneg l) = if Nat.eqb (nth (lvar l) A 0) 0 then 0 else 3 - lval A l.
Proof. unfold lval, lval_of. parn l; cbn [Nat.eqb]; eqbs; lia. Qed.

Lemma lval_neg_true A l : nth (lvar l) A 0 <= 2 -> lval A l = 2 <-> lval A (lneg l) = 1.
Proof. unfold lval, lval_of. parn l; cbn [Nat.eqb]; eqbs; lia. Qed.

Lemma lval_true_inj A a b : lval A a = 1 -> lval A b = 1 -> lvar a = lvar b -> a = b.
Proof.
  unfold lval, lval_of. intros Ha Hb E. rewrite <- E in Hb. revert Ha Hb E.
  par a; par b; cbn [Nat.eqb]; eqbs; intros; lia.
Qed.

Lemma even_mod l : Nat.even l = Nat.eqb (l mod 2) 0.
Proof.
  par l; cbn [Nat.eqb].
  - now rewrite Nat.even_mul.
  - now rewrite Nat.even_add, Nat.even_mul.
Qed.

Lemma even_2v v : Nat.even (2 * v) = true.
Proof. now rewrite even_mod, mod_2v. Qed.

Lemma even_2v1 v : Nat.even (2 * v + 1) = false.
Proof. now rewrite even_mod, mod_2v1. Qed.

Lemma lit_true_lneg val l : lit_true val (lneg l) <-> ~ lit_true val l.
Proof.
  unfold lit_true. parn l; rewrite ?even_2v, ?even_2v1; destruct (val v); intuition congruence.
Qed.

(** The value a literal gets from [enqueue]. *)
Definition lit_code (l : nat) : nat := if Nat.eqb (l mod 2) 0 then 1 else 2.

Lemma lit_code_le l : lit_code l <= 2.
Proof. unfold lit_code. destruct (Nat.eqb (l mod 2) 0); lia. Qed.

Lemma lit_code_nz l : lit_code l <> 0.
Proof. unfold lit_code. destruct (Nat.eqb (l mod 2) 0); lia. Qed.

Lemma lval_of_code l : lval_of (lit_code l) l = 1.
Proof. unfold lval_of, lit_code. par l; reflexivity. Qed.

Lemma lval_of_code_neg l : lval_of (lit_code l) (lneg l) = 2.
Proof. unfold lval_of, lit_code. parn l; reflexivity. Qed.

Lemma lval_lset A v x l :
  lval (lset A v x) l = if Nat.eqb v (lvar l) then (if Nat.ltb v (length A) then lval_of x l else 0)
                        else lval A l.
Proof.
  unfold lval. rewrite nth_lset.
  destruct (Nat.eqb v (lvar l)); [destruct (Nat.ltb v (length A))|]; reflexivity.
Qed.

Lemma lval_lset_neq A v x l : v <> lvar l -> lval (lset A v x) l = lval A l.
Proof. intros. rewrite lval_lset. now destruct (Nat.eqb_spec v (lvar l)). Qed.

(** A literal false under the assignment is true under a model [val] only if
    [val] disagrees with the assignment on its variable. *)
Definition disagree (val : nat -> bool) (A : list nat) (v : nat) : Prop :=
  nth v A 0 <> 0 /\ val v <> Nat.eqb (nth v A 0) 1.

Lemma false_true_disagree val A q :
  nth (lvar q) A 0 <= 2 -> lval A q = 2 -> lit_true val q -> disagree val A (lvar q).
Proof.
  unfold lval, lval_of, lit_true, disagree. par q; rewrite ?even_2v, ?even_2v1; cbn [Nat.eqb];
    destruct (val v); eqbs; intuition (try lia; try congruence).
Qed.

Lemma false_disagree_true val A q :
  nth (lvar q) A 0 <= 2 -> lval A q = 2 -> disagree val A (lvar q) -> lit_true val q.
Proof.
  unfold lval, lval_of, lit_true, disagree. par q; rewrite ?even_2v, ?even_2v1; cbn [Nat.eqb];
    destruct (val v); eqbs; intuition (try lia; try congruence).
Qed.

Lemma true_disagree_false val A p :
  lval A p = 1 -> disagree val A (lvar p) -> lit_true val (lneg p).
Proof.
  intros Hp Hd. apply lit_true_lneg. revert Hp Hd.
  unfold lval, lval_of, lit_true, disagree. par p; rewrite ?even_2v, ?even_2v1; cbn [Nat.eqb];
    destruct (val v); eqbs; intuition (try lia; try congruence).
Qed.

(** * Levels *)

Definition count_le (lim : list nat) (k : nat) : nat := length (filter (fun x => Nat.leb x k) lim).

Definition sorted (l : list nat) : Prop :=
  forall i j, i < j < length l -> nth i l 0 <= nth j l 0.

Lemma count_le_max lim k : count_le lim k <= length lim.
Proof. apply filter_length_le. Qed.

Lemma count_le_all lim k : Forall (fun x => x <= k) lim -> count_le lim k = length lim.
Proof.
  unfold count_le. induction 1; cbn; auto. destruct (Nat.leb_spec x k); cbn; [lia | lia].
Qed.

Lemma count_le_snoc lim x k : count_le (lim ++ [x]) k = count_le lim k + (if Nat.leb x k then 1 else 0).
Proof. unfold count_le. rewrite filter_app, length_app. cbn. now destruct (Nat.leb x k). Qed.

Lemma sorted_snoc l x : sorted l -> Forall (fun y => y <= x) l -> sorted (l ++ [x]).
Proof.
  intros Hs F i j Hij. rewrite length_app in Hij. cbn in Hij.
  rewrite app_nth1 by lia.
  destruct (Nat.eq_dec j (length l)) as [-> | Hj].
  - rewrite app_nth2, Nat.sub_diag by lia. cbn.
    rewrite Forall_forall in F. apply F, nth_In. lia.
  - rewrite app_nth1 by lia. apply Hs. lia.
Qed.

Lemma sorted_firstn l n : sorted l -> sorted (firstn n l).
Proof.
  intros Hs i j Hij. rewrite length_firstn in Hij.
  rewrite !nth_firstn. destruct (Nat.ltb_spec i n), (Nat.ltb_spec j n); try lia.
  apply Hs. lia.
Qed.

Lemma sorted_le_nth l n x : sorted l -> n < length l -> In x (firstn n l) -> x <= nth n l 0.
Proof.
  intros Hs Hn Hx. apply In_nth with (d := 0) in Hx as (i & Hi & <-).
  rewrite length_firstn in Hi. rewrite nth_firstn.
  destruct (Nat.ltb_spec i n); [|lia]. apply Hs. lia.
Qed.

Lemma sorted_cons a l : sorted (a :: l) -> sorted l /\ Forall (fun x => a <= x) l.
Proof.
  intros Hs. split.
  - intros i j Hij. apply (Hs (S i) (S j)). cbn. lia.
  - apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx as (j & Hj & <-).
    apply (Hs 0 (S j)). cbn. lia.
Qed.

Lemma count_le_none l k : Forall (fun x => k < x) l -> count_le l k = 0.
Proof. unfold count_le. induction 1; cbn; auto. destruct (Nat.leb_spec x k); [lia | auto]. Qed.

(** Positions below [lim[n]] are exactly those at level [<= n]. *)
Lemma count_le_lt_iff lim n k : sorted lim -> n < length lim ->
  count_le lim k <= n <-> k < nth n lim 0.
Proof.
  revert n. induction lim as [|a l IH]; intros n Hs Hn; [cbn in Hn; lia|].
  apply sorted_cons in Hs as [Hs F]. unfold count_le in *. cbn [filter].
  destruct (Nat.leb_spec a k).
  - cbn [length]. destruct n as [|n]; cbn [nth]; [lia|].
    rewrite <- (IH n Hs) by (cbn in Hn; lia). lia.
  - assert (Hz : length (filter (fun x => Nat.leb x k) l) = 0).
    { apply count_le_none. eapply Forall_impl; [|exact F]. cbn. intros. lia. }
    rewrite Hz. destruct n as [|n]; cbn [nth]; split; intros; try lia.
    rewrite Forall_forall in F. assert (a <= nth n l 0) by (apply F, nth_In; cbn in Hn; lia). lia.
Qed.

Lemma count_le_eq_all lim k : count_le lim k = length lim -> Forall (fun x => x <= k) lim.
Proof.
  unfold count_le. induction lim as [|a l IH]; cbn; intros E; constructor.
  - destruct (Nat.leb_spec a k); [lia|]. pose proof (filter_length_le (fun x => Nat.leb x k) l). cbn in E. lia.
  - apply IH. destruct (Nat.leb a k); cbn in E; [lia|].
    pose proof (filter_length_le (fun x => Nat.leb x k) l). lia.
Qed.

(** A position is at the current level iff it is at or after the last decision. *)
Lemma count_le_cur lim k : sorted lim -> lim <> [] ->
  count_le lim k = length lim <-> nth (length lim - 1) lim 0 <= k.
Proof.
  intros Hs Hne. assert (Hl : length lim - 1 < length lim) by (destruct lim; [congruence | cbn; lia]).
  pose proof (count_le_lt_iff lim (length lim - 1) k Hs Hl). pose proof (count_le_max lim k). lia.
Qed.

Lemma count_le_firstn lim n k : sorted lim -> n < length lim -> k < nth n lim 0 ->
  count_le (firstn n lim) k = count_le lim k.
Proof.
  intros Hs Hn Hk. unfold count_le.
  rewrite <- (firstn_skipn n lim) at 2. rewrite filter_app, length_app.
  enough (length (filter (fun x => Nat.leb x k) (skipn n lim)) = 0) by lia.
  apply count_le_none. apply Forall_forall. intros x Hx.
  apply In_nth with (d := 0) in Hx as (j & Hj & <-). rewrite length_skipn in Hj.
  rewrite nth_skipn. destruct (Nat.eq_dec j 0) as [-> | Hj0].
  - now rewrite Nat.add_0_r.
  - enough (nth n lim 0 <= nth (n + j) lim 0) by lia. apply Hs. lia.
Qed.

(** * Lists *)

Lemma nth_error_snoc {A} (xs : list A) x k y :
  nth_error (xs ++ [x]) k = Some y ->
  (k < length xs /\ nth_error xs k = Some y) \/ (k = length xs /\ y = x).
Proof.
  intros H. destruct (Nat.ltb_spec k (length xs)).
  - left. rewrite nth_error_app1 in H by lia. auto.
  - right. rewrite nth_error_app2 in H by lia.
    destruct (k - length xs) as [|j] eqn:E; cbn in H.
    + split; [lia | congruence].
    + destruct j; discriminate.
Qed.

Lemma nth_error_snoc_lt {A} (xs : list A) x k : k < length xs -> nth_error (xs ++ [x]) k = nth_error xs k.
Proof. apply nth_error_app1. Qed.

Lemma nth_error_snoc_eq {A} (xs : list A) x : nth_error (xs ++ [x]) (length xs) = Some x.
Proof. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma in_map_nth_error {A B} (f : A -> B) xs y :
  In y (map f xs) -> exists k x, nth_error xs k = Some x /\ f x = y.
Proof.
  intros Hy. apply in_map_iff in Hy as (x & <- & Hx).
  apply In_nth_error in Hx as (k & Hk). eauto.
Qed.

Lemma nth_error_in_map {A B} (f : A -> B) xs k x : nth_error xs k = Some x -> In (f x) (map f xs).
Proof. intros. apply in_map. eapply nth_error_In; eauto. Qed.

(** In a list without duplicates, an element has one position. *)
Lemma nodup_nth_error {A} (xs : list A) i j x :
  NoDup xs -> nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof. intros Hn Hi Hj. eapply NoDup_nth_error; eauto. apply nth_error_Some. congruence. congruence. Qed.

Definition at_pos (T : list nat) (k v : nat) : Prop := exists l, nth_error T k = Some l /\ lvar l = v.

Lemma at_pos_unique T k k' v : NoDup (map lvar T) -> at_pos T k v -> at_pos T k' v -> k = k'.
Proof.
  intros Hn (l & Hl & El) (l' & Hl' & El').
  apply (nodup_nth_error (map lvar T) k k' v Hn); rewrite nth_error_map.
  - rewrite Hl; cbn [option_map]; now rewrite El.
  - rewrite Hl'; cbn [option_map]; now rewrite El'.
Qed.

Lemma at_pos_lt T k v : at_pos T k v -> k < length T.
Proof. intros (l & Hl & _). apply nth_error_Some. congruence. Qed.

Lemma at_pos_snoc T x k v : at_pos T k v -> at_pos (T ++ [x]) k v.
Proof. intros (l & Hl & E). exists l. split; [|exact E]. rewrite nth_error_snoc_lt; auto. apply nth_error_Some. congruence. Qed.

Lemma at_pos_firstn T m k v : k < m -> at_pos T k v -> at_pos (firstn m T) k v.
Proof. intros Hk (l & Hl & E). exists l. split; [|exact E]. rewrite nth_error_firstn. now destruct (Nat.ltb_spec k m); [|lia]. Qed.

Lemma at_pos_in T k v : at_pos T k v -> In v (map lvar T).
Proof. intros (l & Hl & <-). eapply nth_error_in_map; eauto. Qed.

(** A variable placed before [m] is not among the variables after [m]. *)
Lemma at_pos_not_skipn T k m v : NoDup (map lvar T) -> at_pos T k v -> k < m -> ~ In v (map lvar (skipn m T)).
Proof.
  intros Hn Hk Hkm Hi. apply in_map_nth_error in Hi as (j & l & Hj & El).
  rewrite nth_error_skipn in Hj.
  assert (at_pos T (m + j) v) as Hk' by (exists l; auto).
  pose proof (at_pos_unique _ _ _ _ Hn Hk Hk'). lia.
Qed.

Lemma nodup_firstn {A} (xs : list A) n : NoDup xs -> NoDup (firstn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. eapply NoDup_app_remove_r; eauto. Qed.

Lemma in_firstn_skipn {A} (xs : list A) n x : In x xs -> In x (firstn n xs) \/ In x (skipn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. now apply in_app_or. Qed.

Global Arguments lvar : simpl never.
Global Arguments lneg : simpl never.
Global Arguments lval : simpl never.
Global Arguments lset : simpl never.

Lemma lset_cons0 {A} (a : A) xs x : lset (a :: xs) 0 x = x :: xs.
Proof. reflexivity. Qed.

Lemma lset_consS {A} (a : A) xs i x : lset (a :: xs) (S i) x = a :: lset xs i x.
Proof. reflexivity. Qed.

Lemma lset_nil {A} i (x : A) : lset [] i x = [].
Proof. now destruct i. Qed.

(** * The invariants *)

(** Literal [l], at trail position [k], has reason clause [r]: [l] is its
    first literal, and every other literal is false and earlier. *)
Definition reason_ok (st : astate) (k l r : nat) : Prop :=
  exists c, nth_error (db st) r = Some c /\ nth_error c 0 = Some l /\
    Forall (fun q => lval (asg st) q = 2 /\ exists k', k' < k /\ at_pos (tr st) k' (lvar q)) (tl c).

Record Core (val : nat -> bool) (st : astate) : Prop := {
  i_db : Forall (Exists (lit_true val)) (db st);
  i_asg : forall v, nth v (asg st) 0 <= 2;
  i_nd : NoDup (map lvar (tr st));
  i_tr : forall v, nth v (asg st) 0 <> 0 <-> In v (map lvar (tr st));
  i_true : Forall (fun l => lval (asg st) l = 1) (tr st);
  i_lvl : forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (lvl st) 0 = count_le (lim st) k;
  i_sorted : sorted (lim st);
  i_limq : Forall (fun x => x <= qhead st) (lim st);
  i_qtr : qhead st <= length (tr st);
  i_rsn : forall k l r, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 = S r -> reason_ok st k l r;
  i_dec : forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 = 0 ->
            Forall (fun x => k <= x) (lim st) \/ In k (lim st);
  i_l0 : forall l, In l (tr st) -> nth (lvar l) (lvl st) 0 = 0 -> lit_true val l
}.

(** How often clause [ci] should at most occur in the watch list of [l]. *)
Definition expect_cl (c : list nat) (l : nat) : nat :=
  if Nat.leb 2 (length c)
  then (if Nat.eqb (nth 0 c 0) l then 1 else 0) + (if Nat.eqb (nth 1 c 0) l then 1 else 0)
  else 0.

Definition expect (D : list (list nat)) (ci l : nat) : nat :=
  match nth_error D ci with Some c => expect_cl c l | None => 0 end.

Definition cnt (W : list (list nat)) (l ci : nat) : nat := count_occ Nat.eq_dec (nth l W []) ci.

Definition Wch (D : list (list nat)) (W : list (list nat)) : Prop :=
  forall ci l, l < length W -> cnt W l ci <= expect D ci l.

Definition Seen0 (st : astate) : Prop := forall v, nth v (sn st) 0 = 0.

Definition Inv (val : nat -> bool) (st : astate) : Prop :=
  Core val st /\ Wch (db st) (wl st) /\ Seen0 st.

(** * Consequences *)

Section Facts.
Variables (val : nat -> bool) (st : astate).
Hypothesis C : Core val st.

Lemma asg_lval_le2 l : lval (asg st) l <= 2.
Proof. apply lval_le2, (i_asg _ _ C). Qed.

Lemma true_on_trail l : In l (tr st) -> lval (asg st) l = 1.
Proof. intros H. pose proof (i_true _ _ C) as F. rewrite Forall_forall in F. auto. Qed.

(** A true literal is the trail's literal for its variable. *)
Lemma true_trail l : lval (asg st) l = 1 -> exists k, nth_error (tr st) k = Some l.
Proof.
  intros Hl. assert (nth (lvar l) (asg st) 0 <> 0) as Ha.
  { intros E. apply (lval_zero (asg st) l (i_asg _ _ C _)) in E. lia. }
  apply (i_tr _ _ C) in Ha. apply in_map_nth_error in Ha as (k & l' & Hk & E).
  exists k. rewrite Hk. f_equal. apply (lval_true_inj (asg st)); auto.
  apply true_on_trail. eapply nth_error_In; eauto.
Qed.

Lemma false_trail q : lval (asg st) q = 2 -> exists k, nth_error (tr st) k = Some (lneg q).
Proof. intros Hq. apply true_trail. now apply lval_neg_true; [apply (i_asg _ _ C)|]. Qed.

Lemma false_at_pos q : lval (asg st) q = 2 -> exists k, at_pos (tr st) k (lvar q).
Proof.
  intros Hq. destruct (false_trail q Hq) as (k & Hk). exists k, (lneg q). split; [exact Hk|]. apply lvar_lneg.
Qed.

Lemma assigned_at_pos q : lval (asg st) q <> 0 -> exists k, at_pos (tr st) k (lvar q).
Proof.
  intros Hq. assert (nth (lvar q) (asg st) 0 <> 0) as Ha.
  { intros E. apply Hq. now apply (lval_zero (asg st) q (i_asg _ _ C _)). }
  apply (i_tr _ _ C) in Ha. apply in_map_nth_error in Ha as (k & l' & Hk & E). exists k, l'. auto.
Qed.

Lemma at_pos_assigned k v : at_pos (tr st) k v -> nth v (asg st) 0 <> 0.
Proof. intros H. apply (i_tr _ _ C). eapply at_pos_in; eauto. Qed.

Lemma level_le k l : nth_error (tr st) k = Some l -> nth (lvar l) (lvl st) 0 <= length (lim st).
Proof. intros H. rewrite (i_lvl _ _ C k l H). apply count_le_max. Qed.

(** A literal false at level 0 is false under [val]. *)
Lemma false_l0 q : lval (asg st) q = 2 -> nth (lvar q) (lvl st) 0 = 0 -> ~ lit_true val q.
Proof.
  intros Hq H0. destruct (false_trail q Hq) as (k & Hk).
  apply lit_true_lneg. apply (i_l0 _ _ C).
  - eapply nth_error_In; eauto.
  - now rewrite lvar_lneg.
Qed.

(** With no decision on the trail, a clause cannot be false: it is true under [val]. *)
Lemma no_false_clause_l0 c : length (lim st) = 0 -> In c (db st) -> Forall (fun q => lval (asg st) q = 2) c -> False.
Proof.
  intros H0 Hc Hf. pose proof (i_db _ _ C) as D. rewrite Forall_forall in D.
  apply D, Exists_exists in Hc as (q & Hq & Ht).
  rewrite Forall_forall in Hf. specialize (Hf q Hq).
  destruct (false_trail q Hf) as (k & Hk).
  apply (false_l0 q Hf); [|exact Ht].
  pose proof (level_le k _ Hk) as Hl. rewrite lvar_lneg in Hl. lia.
Qed.

End Facts.

(** * Preservation *)

Lemma nodup_snoc' {A} (l : list A) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros H Hx. apply NoDup_app; auto; [constructor; auto; constructor|].
  intros a Ha [<- | []]. auto.
Qed.

Lemma core_ext val st st' :
  db st' = db st -> asg st' = asg st -> lvl st' = lvl st -> rsn st' = rsn st ->
  tr st' = tr st -> lim st' = lim st -> qhead st' = qhead st -> Core val st -> Core val st'.
Proof.
  intros Ed Ea El Er Et Em Eq [? ? ? ? ? ? ? ? ? Hr ? ?].
  constructor; unfold reason_ok in *; rewrite ?Ed, ?Ea, ?El, ?Er, ?Et, ?Em, ?Eq; auto.
Qed.

Lemma core_fset_other val st f xs :
  f = FPh \/ f = FSt \/ f = FSn -> Core val st -> Core val (fset st f xs).
Proof. intros Hf. apply core_ext; cbn; destruct Hf as [-> | [-> | ->]]; reflexivity. Qed.

Lemma core_wset val st w : Core val st -> Core val (wset st w).
Proof. apply core_ext; reflexivity. Qed.

Lemma lit_var_cases q l : lvar q = lvar l -> q = l \/ q = lneg l.
Proof.
  intros E. pose proof (Nat.mod_upper_bound q 2). pose proof (Nat.mod_upper_bound l 2).
  destruct (Nat.eq_dec (q mod 2) (l mod 2)).
  - left. now apply lit_eq.
  - right. apply lit_eq; [now rewrite lvar_lneg | rewrite lneg_mod; lia].
Qed.

(** [enqueue l r] on the abstract state. *)
Definition enq (st : astate) (l r : nat) : astate :=
  fset (fset (fset (fset st FAsg (lset (asg st) (lvar l) (lit_code l)))
                         FLvl (lset (lvl st) (lvar l) (length (lim st))))
                   FRsn (lset (rsn st) (lvar l) r))
       FTr (tr st ++ [l]).

Lemma lval_enq A l q : lvar l < length A ->
  lval (lset A (lvar l) (lit_code l)) q =
  if Nat.eqb q l then 1 else if Nat.eqb q (lneg l) then 2 else lval A q.
Proof.
  intros Hv. rewrite lval_lset. destruct (Nat.eqb_spec (lvar l) (lvar q)) as [E|E].
  - destruct (Nat.ltb_spec (lvar l) (length A)); [|lia].
    destruct (lit_var_cases q l (eq_sym E)) as [-> | ->].
    + rewrite Nat.eqb_refl. apply lval_of_code.
    + rewrite Nat.eqb_refl. destruct (Nat.eqb_spec (lneg l) l) as [N|_]; [now apply lneg_neq in N|].
      apply lval_of_code_neg.
  - destruct (Nat.eqb_spec q l) as [-> | _]; [congruence|].
    destruct (Nat.eqb_spec q (lneg l)) as [-> | _]; [rewrite lvar_lneg in E; congruence|]. reflexivity.
Qed.

Lemma lval_enq_other A l q : lvar l < length A -> lvar q <> lvar l ->
  lval (lset A (lvar l) (lit_code l)) q = lval A q.
Proof. intros _ Hne. apply lval_lset_neq. auto. Qed.

Lemma core_enq val st l r :
  Core val st -> lval (asg st) l = 0 ->
  lvar l < length (asg st) -> lvar l < length (lvl st) -> lvar l < length (rsn st) ->
  (r = 0 -> Forall (fun x => length (tr st) <= x) (lim st) \/ In (length (tr st)) (lim st)) ->
  (forall ci, r = S ci -> exists c, nth_error (db st) ci = Some c /\ nth_error c 0 = Some l /\
                            Forall (fun q => lval (asg st) q = 2) (tl c)) ->
  (length (lim st) = 0 -> lit_true val l) ->
  Core val (enq st l r).
Proof.
  intros C Hl0 Ha Hlv Hr Hdec Hrsn Hl0v. unfold enq.
  set (v := lvar l) in *.
  assert (Hv0 : nth v (asg st) 0 = 0) by (apply (lval_zero _ _ (i_asg _ _ C _)), Hl0).
  assert (Hold : forall k l', nth_error (tr st) k = Some l' -> lvar l' <> v).
  { intros k l' Hk E. apply (at_pos_assigned val st C k v); [|exact Hv0]. exists l'. auto. }
  assert (Hasg : forall q, lval (asg st) q <> 0 -> lvar q <> v).
  { intros q Hq E. destruct (assigned_at_pos val st C q Hq) as (k & l' & Hk & E').
    apply (Hold k l' Hk). congruence. }
  assert (Hkeep : forall q, lvar q <> v -> lval (lset (asg st) v (lit_code l)) q = lval (asg st) q).
  { intros q Hq. apply lval_lset_neq. auto. }
  assert (Hqt : qhead st <= length (tr st)) by apply (i_qtr _ _ C).
  assert (Hlimtr : Forall (fun x => x <= length (tr st)) (lim st)).
  { eapply Forall_impl; [|apply (i_limq _ _ C)]. cbn. lia. }
  assert (Hnot : ~ In v (map lvar (tr st))).
  { intros Hi. apply (i_tr _ _ C) in Hi. contradiction. }
  assert (Hin : forall l', In l' (tr st) -> lvar l' <> v).
  { intros l' Hi. apply In_nth_error in Hi as (k & Hk). eauto. }
  constructor; cbn [fv fset fld_eqb db hcls hwl wl].
  - apply (i_db _ _ C).
  - intros w. rewrite nth_lset. destruct (Nat.eqb v w); [destruct (Nat.ltb v (length (asg st)))|];
      [apply lit_code_le | lia | apply (i_asg _ _ C)].
  - rewrite map_app. apply nodup_snoc'; [apply (i_nd _ _ C) | exact Hnot].
  - intros w. rewrite nth_lset, map_app, in_app_iff. cbn [map In].
    destruct (Nat.eqb_spec v w) as [<- | Hne].
    + destruct (Nat.ltb_spec v (length (asg st))); [|lia].
      pose proof (lit_code_nz l). tauto.
    + rewrite (i_tr _ _ C w). intuition.
  - apply Forall_app. split.
    + apply Forall_forall. intros l' Hi. rewrite Hkeep by (now apply Hin).
      now apply (true_on_trail val st C).
    + constructor; [|constructor]. rewrite lval_lset. rewrite Nat.eqb_refl.
      destruct (Nat.ltb_spec v (length (asg st))); [apply lval_of_code | lia].
  - intros k l' Hk. apply nth_error_snoc in Hk as [[Hk Hk'] | [-> ->]].
    + rewrite nth_lset. destruct (Nat.eqb_spec v (lvar l')) as [E | _]; [exfalso; eapply Hold; eauto|].
      apply (i_lvl _ _ C k l' Hk').
    + rewrite nth_lset, Nat.eqb_refl. destruct (Nat.ltb_spec v (length (lvl st))); [|lia].
      symmetry. now apply count_le_all.
  - apply (i_sorted _ _ C).
  - apply (i_limq _ _ C).
  - rewrite length_app. lia.
  - intros k l' r' Hk. apply nth_error_snoc in Hk as [[Hk Hk'] | [-> ->]].
    + rewrite nth_lset. destruct (Nat.eqb_spec v (lvar l')) as [E | _]; [exfalso; eapply Hold; eauto|].
      intros Hr'. destruct (i_rsn _ _ C k l' r' Hk' Hr') as (c & Hc & H0 & Hf).
      exists c. split; [exact Hc|]. split; [exact H0|].
      eapply Forall_impl; [|exact Hf]. intros q [Hq (k' & Hk'k & Hp)].
      split.
      * rewrite Hkeep; [exact Hq|]. apply Hasg. lia.
      * exists k'. split; [exact Hk'k | now apply at_pos_snoc].
    + rewrite nth_lset, Nat.eqb_refl. destruct (Nat.ltb_spec v (length (rsn st))); [|lia].
      intros ->. destruct (Hrsn r' eq_refl) as (c & Hc & H0 & Hf).
      exists c. split; [exact Hc|]. split; [exact H0|].
      eapply Forall_impl; [|exact Hf]. intros q Hq. cbv beta in Hq. split.
      * rewrite Hkeep; [exact Hq|]. apply Hasg. lia.
      * destruct (false_at_pos val st C q Hq) as (k' & Hp). exists k'.
        split; [eapply at_pos_lt; exact Hp | now apply at_pos_snoc].
  - intros k l' Hk. apply nth_error_snoc in Hk as [[Hk Hk'] | [-> ->]].
    + rewrite nth_lset. destruct (Nat.eqb_spec v (lvar l')) as [E | _]; [exfalso; eapply Hold; eauto|].
      apply (i_dec _ _ C k l' Hk').
    + rewrite nth_lset, Nat.eqb_refl. destruct (Nat.ltb_spec v (length (rsn st))); [|lia]. exact Hdec.
  - intros l' Hi. apply in_app_or in Hi as [Hi | [<- | []]].
    + rewrite nth_lset. destruct (Nat.eqb_spec v (lvar l')) as [E | _]; [exfalso; eapply Hin; eauto|].
      apply (i_l0 _ _ C l' Hi).
    + rewrite nth_lset, Nat.eqb_refl. destruct (Nat.ltb_spec v (length (lvl st))); [|lia]. exact Hl0v.
Qed.

Lemma in_firstn {A} (xs : list A) n x : In x (firstn n xs) -> In x xs.
Proof. intros H. rewrite <- (firstn_skipn n xs). apply in_or_app. auto. Qed.

Lemma nth_error_firstn_inv {A} (xs : list A) m k x :
  nth_error (firstn m xs) k = Some x -> k < m /\ nth_error xs k = Some x.
Proof.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec k m); [auto | discriminate].
Qed.

Lemma in_firstn_pos {A} (xs : list A) m x : In x (firstn m xs) -> exists k, k < m /\ nth_error xs k = Some x.
Proof. intros H. apply In_nth_error in H as (k & Hk). apply nth_error_firstn_inv in Hk. eauto. Qed.

Lemma nodup_app_disj {A} (l1 l2 : list A) x : NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; intros H H1 H2; [destruct H1|].
  inversion H as [|? ? Ha Hn]; subst. destruct H1 as [<- | H1].
  - apply Ha, in_or_app. auto.
  - eauto.
Qed.

Lemma lval_ext A A' q : nth (lvar q) A' 0 = nth (lvar q) A 0 -> lval A' q = lval A q.
Proof. unfold lval. now intros ->. Qed.

(** [backtrack lv] on the abstract state: everything from trail position
    [lim[lv]] on is unassigned, and the queue restarts there. *)
Definition bt_rel (st st' : astate) (lv : nat) : Prop :=
  let m := nth lv (lim st) 0 in
  db st' = db st /\
  (forall w, In w (map lvar (skipn m (tr st))) -> nth w (asg st') 0 = 0) /\
  (forall w, ~ In w (map lvar (skipn m (tr st))) -> nth w (asg st') 0 = nth w (asg st) 0) /\
  lvl st' = lvl st /\
  (forall w, ~ In w (map lvar (skipn m (tr st))) -> nth w (rsn st') 0 = nth w (rsn st) 0) /\
  tr st' = firstn m (tr st) /\ lim st' = firstn lv (lim st) /\ qhead st' = m.

Lemma core_bt val st st' lv : Core val st -> lv < length (lim st) -> bt_rel st st' lv -> Core val st'.
Proof.
  intros C Hlv (Edb & Az & Ak & Elv & Rk & Etr & Elim & Eq).
  set (m := nth lv (lim st) 0) in *.
  assert (Hm : m <= length (tr st)).
  { pose proof (i_limq _ _ C) as F. rewrite Forall_forall in F.
    pose proof (F m (nth_In _ _ Hlv)). pose proof (i_qtr _ _ C). lia. }
  assert (Hsplit : map lvar (tr st) = map lvar (firstn m (tr st)) ++ map lvar (skipn m (tr st)))
    by (now rewrite <- map_app, firstn_skipn).
  assert (Hnd : NoDup (map lvar (tr st))) by apply (i_nd _ _ C).
  assert (Hkeep : forall k w, at_pos (tr st) k w -> k < m -> ~ In w (map lvar (skipn m (tr st))))
    by (intros; eapply at_pos_not_skipn; eauto).
  assert (Hkeepl : forall k l, nth_error (tr st) k = Some l -> k < m -> ~ In (lvar l) (map lvar (skipn m (tr st))))
    by (intros k l Hk Hkm; apply (Hkeep k); [exists l; auto | exact Hkm]).
  assert (Hval : forall k l, nth_error (tr st) k = Some l -> k < m -> lval (asg st') l = lval (asg st) l)
    by (intros k l Hk Hkm; apply lval_ext, Ak; eauto).
  constructor; rewrite ?Edb, ?Elv, ?Etr, ?Elim, ?Eq.
  - apply (i_db _ _ C).
  - intros w. destruct (in_dec Nat.eq_dec w (map lvar (skipn m (tr st)))) as [Hi | Hi].
    + rewrite Az by exact Hi. lia.
    + rewrite Ak by exact Hi. apply (i_asg _ _ C).
  - rewrite <- firstn_map. apply nodup_firstn, Hnd.
  - intros w. destruct (in_dec Nat.eq_dec w (map lvar (skipn m (tr st)))) as [Hi | Hi].
    + rewrite Az by exact Hi. split; [congruence|]. intros Hf.
      pose proof Hnd as Hn'. rewrite Hsplit in Hn'. destruct (nodup_app_disj _ _ w Hn' Hf Hi).
    + rewrite Ak by exact Hi. rewrite (i_tr _ _ C w), Hsplit, in_app_iff. tauto.
  - apply Forall_forall. intros l Hl. apply in_firstn_pos in Hl as (k & Hkm & Hk).
    rewrite (Hval k l Hk Hkm). apply (true_on_trail val st C). eapply nth_error_In; eauto.
  - intros k l Hk. apply nth_error_firstn_inv in Hk as [Hkm Hk].
    rewrite (i_lvl _ _ C k l Hk). symmetry. apply count_le_firstn; auto. apply (i_sorted _ _ C).
  - apply sorted_firstn, (i_sorted _ _ C).
  - apply Forall_forall. intros x Hx. apply sorted_le_nth with (n := lv); auto. apply (i_sorted _ _ C).
  - rewrite length_firstn. lia.
  - intros k l r Hk. apply nth_error_firstn_inv in Hk as [Hkm Hk].
    rewrite Rk by (eapply Hkeepl; eauto). intros Hr.
    destruct (i_rsn _ _ C k l r Hk Hr) as (c & Hc & H0 & Hf).
    exists c. rewrite Edb, Etr. split; [exact Hc|]. split; [exact H0|].
    eapply Forall_impl; [|exact Hf]. intros q [Hq (k' & Hk'k & Hp)]. split.
    + rewrite lval_ext with (A := asg st); [exact Hq|]. apply Ak. apply (Hkeep k'); [exact Hp | lia].
    + exists k'. split; [exact Hk'k|]. apply at_pos_firstn; [lia | exact Hp].
  - intros k l Hk. apply nth_error_firstn_inv in Hk as [Hkm Hk].
    rewrite Rk by (eapply Hkeepl; eauto). intros Hr.
    destruct (i_dec _ _ C k l Hk Hr) as [F | Hi].
    + left. apply Forall_forall. intros x Hx. rewrite Forall_forall in F. apply F. eapply in_firstn; eauto.
    + right. apply In_nth with (d := 0) in Hi as (i & Hi & Ei).
      destruct (Nat.ltb_spec i lv).
      * rewrite <- Ei. replace (nth i (lim st) 0) with (nth i (firstn lv (lim st)) 0)
          by (rewrite nth_firstn; destruct (Nat.ltb_spec i lv); [reflexivity | lia]).
        apply nth_In. rewrite length_firstn. lia.
      * exfalso. assert (m <= nth i (lim st) 0); [|lia].
        destruct (Nat.eq_dec i lv) as [-> | Hne]; [unfold m; lia|]. apply (i_sorted _ _ C). lia.
  - intros l Hl. apply (i_l0 _ _ C). eapply in_firstn; eauto.
Qed.

Lemma Forall_lset {A} (P : A -> Prop) xs i x : Forall P xs -> P x -> Forall P (lset xs i x).
Proof.
  intros H Hx. revert i. induction H; intros [|i]; rewrite ?lset_nil, ?lset_cons0, ?lset_consS; constructor; auto.
Qed.

Lemma Forall_nth_error {A} (P : A -> Prop) xs i x : Forall P xs -> nth_error xs i = Some x -> P x.
Proof. intros H Hi. rewrite Forall_forall in H. apply H. eapply nth_error_In; eauto. Qed.

(** A clause that is no literal's reason may be replaced by a permutation of itself. *)
Lemma not_reason val st ci cl :
  Core val st -> nth_error (db st) ci = Some cl -> (forall x, nth_error cl 0 = Some x -> lval (asg st) x <> 1) ->
  forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 <> S ci.
Proof.
  intros C Hc Hx k l Hk Hr. destruct (i_rsn _ _ C k l ci Hk Hr) as (c & Hc' & H0 & _).
  rewrite Hc in Hc'. injection Hc' as <-. apply (Hx l H0). apply (true_on_trail val st C).
  eapply nth_error_In; eauto.
Qed.

Lemma core_dset val st ci cl cl' :
  Core val st -> nth_error (db st) ci = Some cl -> Permutation cl cl' ->
  (forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 <> S ci) ->
  Core val (dset st (lset (db st) ci cl')).
Proof.
  intros C Hc Hp Hnr. destruct C as [Cdb ? ? ? ? ? ? ? ? Cr ? ?]. constructor; cbn [dset db fv]; auto.
  - apply Forall_lset; [exact Cdb|]. eapply Permutation_Exists; [exact Hp|]. eapply Forall_nth_error; eauto.
  - intros k l r Hk Hr. destruct (Cr k l r Hk Hr) as (c & Hc' & ?). exists c. cbn [dset db fv]. split; [|auto].
    rewrite nth_error_lset_neq; [exact Hc'|]. intros ->. exact (Hnr k l Hk Hr).
Qed.

Lemma core_cpush val st c cl : Core val st -> Exists (lit_true val) cl -> Core val (cpush st c cl).
Proof.
  intros C Hcl. destruct C as [Cdb ? ? ? ? ? ? ? ? Cr ? ?]. constructor; cbn [cpush db fv]; auto.
  - apply Forall_app. auto.
  - intros k l r Hk Hr. destruct (Cr k l r Hk Hr) as (c' & Hc' & ?). exists c'. cbn [cpush db fv]. split; [|auto].
    rewrite nth_error_app1; [exact Hc'|]. apply nth_error_Some. congruence.
Qed.

(** * Permutations by swapping *)

Lemma count_occ_lset xs i x y : i < length xs ->
  count_occ Nat.eq_dec (lset xs i x) y + (if Nat.eqb (nth i xs 0) y then 1 else 0) =
  count_occ Nat.eq_dec xs y + (if Nat.eqb x y then 1 else 0).
Proof.
  revert i. induction xs as [|a xs IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; rewrite ?lset_cons0, ?lset_consS; cbn [nth count_occ].
  - destruct (Nat.eq_dec x y), (Nat.eq_dec a y), (Nat.eqb_spec a y), (Nat.eqb_spec x y); lia.
  - cbn in Hi. specialize (IH i ltac:(lia)). destruct (Nat.eq_dec a y); lia.
Qed.

Lemma perm_swap xs i j : i < length xs -> j < length xs ->
  Permutation xs (lset (lset xs i (nth j xs 0)) j (nth i xs 0)).
Proof.
  intros Hi Hj. apply (Permutation_count_occ Nat.eq_dec). intros y.
  pose proof (count_occ_lset xs i (nth j xs 0) y Hi) as E1.
  pose proof (count_occ_lset (lset xs i (nth j xs 0)) j (nth i xs 0) y) as E2.
  rewrite lset_length in E2. specialize (E2 Hj).
  rewrite nth_lset in E2. destruct (Nat.eqb_spec i j) as [<- | _].
  - destruct (Nat.ltb_spec i (length xs)); [|lia]. lia.
  - lia.
Qed.

Lemma nth_swap_len {A} (xs : list A) i j a b : length (lset (lset xs i a) j b) = length xs.
Proof. now rewrite !lset_length. Qed.

(** * Watch lists *)

Lemma wch_mono D W D' W' :
  Wch D W -> length W' = length W ->
  (forall ci l, l < length W -> cnt W' l ci + expect D ci l <= cnt W l ci + expect D' ci l) ->
  Wch D' W'.
Proof.
  intros H E H'. intros ci l Hl. rewrite E in Hl. specialize (H ci l Hl). specialize (H' ci l Hl). lia.
Qed.

Lemma wch_in D W l ci : Wch D W -> l < length W -> In ci (nth l W []) ->
  exists cl, nth_error D ci = Some cl /\ 2 <= length cl /\ (nth 0 cl 0 = l \/ nth 1 cl 0 = l).
Proof.
  intros H Hl Hi. specialize (H ci l Hl). unfold cnt, expect, expect_cl in H.
  apply (count_occ_In Nat.eq_dec) in Hi.
  destruct (nth_error D ci) as [cl|]; [|lia]. exists cl. split; [reflexivity|].
  destruct (Nat.leb_spec 2 (length cl)); [|lia]. split; [assumption|].
  destruct (Nat.eqb_spec (nth 0 cl 0) l), (Nat.eqb_spec (nth 1 cl 0) l); auto; lia.
Qed.

Lemma expect_lset_other D ci cl ci' l : ci' <> ci -> expect (lset D ci cl) ci' l = expect D ci' l.
Proof. intros. unfold expect. now rewrite nth_error_lset_neq by auto. Qed.

Lemma expect_lset_same D ci cl l : ci < length D -> expect (lset D ci cl) ci l = expect_cl cl l.
Proof. intros. unfold expect. now rewrite nth_error_lset_eq. Qed.

Lemma expect_nth D ci cl l : nth_error D ci = Some cl -> expect D ci l = expect_cl cl l.
Proof. unfold expect. now intros ->. Qed.

Lemma expect_swap01 cl l : 2 <= length cl ->
  expect_cl (lset (lset cl 0 (nth 1 cl 0)) 1 (nth 0 cl 0)) l = expect_cl cl l.
Proof.
  intros H. unfold expect_cl. rewrite !lset_length, !nth_lset, !lset_length.
  repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b); try lia end.
  repeat match goal with |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b); try lia end.
  cbn [Nat.eqb].
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b) end; lia.
Qed.

Lemma expect_swap1k cl k l : 2 <= k < length cl ->
  expect_cl (lset (lset cl 1 (nth k cl 0)) k (nth 1 cl 0)) l + (if Nat.eqb (nth 1 cl 0) l then 1 else 0) =
  expect_cl cl l + (if Nat.eqb (nth k cl 0) l then 1 else 0).
Proof.
  intros H. unfold expect_cl. rewrite !lset_length, !nth_lset, !lset_length.
  repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b); try lia end.
  repeat match goal with |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b); try lia end.
  destruct (Nat.eqb_spec k 0); [lia|]. destruct (Nat.eqb_spec k 1); [lia|]. cbn [Nat.eqb].
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b) end; lia.
Qed.

Lemma cnt_lset W a xs l ci : a < length W ->
  cnt (lset W a xs) l ci = if Nat.eqb a l then count_occ Nat.eq_dec xs ci else cnt W l ci.
Proof.
  intros Ha. unfold cnt. rewrite nth_lset.
  destruct (Nat.eqb a l); [destruct (Nat.ltb_spec a (length W)); [reflexivity | lia] | reflexivity].
Qed.

Lemma skipn_nth_error {A} (xs : list A) i x : nth_error xs i = Some x -> skipn i xs = x :: skipn (S i) xs.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] H; cbn in H |- *; try discriminate.
  - congruence.
  - apply IH, H.
Qed.

Lemma firstn_lset_S {A} (xs : list A) j x : j < length xs -> firstn (S j) (lset xs j x) = firstn j xs ++ [x].
Proof.
  revert j. induction xs as [|a xs IH]; intros [|j] Hj; cbn in Hj; try lia.
  - reflexivity.
  - rewrite lset_consS. cbn [firstn app]. f_equal. apply IH. lia.
Qed.

Lemma skipn_lset {A} (xs : list A) i j x : j < i -> skipn i (lset xs j x) = skipn i xs.
Proof.
  revert i j. induction xs as [|a xs IH]; intros i j Hji; [now rewrite lset_nil|].
  destruct i as [|i]; [lia|]. destruct j as [|j]; [reflexivity|].
  rewrite lset_consS. cbn [skipn]. apply IH. lia.
Qed.

Lemma firstn_lset_lt {A} (xs : list A) n j x : n <= j -> firstn n (lset xs j x) = firstn n xs.
Proof.
  revert n j. induction xs as [|a xs IH]; intros n j Hn; [now rewrite lset_nil|].
  destruct n as [|n]; [reflexivity|]. destruct j as [|j]; [lia|].
  rewrite lset_consS. cbn [firstn]. f_equal. apply IH. lia.
Qed.

(** Keeping the entry at [i] by writing it at [j <= i] leaves [ws[0,j) ++ ws[i,n)] alone. *)
Lemma keep_step (L : list nat) i j x : j <= i -> nth_error L i = Some x ->
  firstn (S j) (lset L j x) ++ skipn (S i) (lset L j x) = firstn j L ++ skipn i L.
Proof.
  intros Hji Hx. assert (i < length L) by (apply nth_error_Some; congruence).
  rewrite firstn_lset_S by lia. rewrite skipn_lset by lia.
  rewrite (skipn_nth_error L i x Hx). now rewrite <- app_assoc.
Qed.

Lemma lset_lset {A} (xs : list A) i x y : lset (lset xs i x) i y = lset xs i y.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i]; rewrite ?lset_nil, ?lset_cons0, ?lset_consS; auto.
  now rewrite IH.
Qed.

Lemma lset_same {A} (xs : list A) i x : nth_error xs i = Some x -> lset xs i x = xs.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite lset_consS. now rewrite IH.
Qed.

Lemma nth_error_nth' {A} (xs : list A) i x d : nth_error xs i = Some x -> nth i xs d = x.
Proof. intros H. now apply nth_error_nth. Qed.

Lemma count_occ_keep L i j ci x : nth_error L i = Some x ->
  count_occ Nat.eq_dec (firstn j L ++ skipn i L) ci =
  count_occ Nat.eq_dec (firstn j L ++ skipn (S i) L) ci + (if Nat.eq_dec x ci then 1 else 0).
Proof.
  intros H. rewrite (skipn_nth_error L i x H), !count_occ_app. cbn [count_occ].
  destruct (Nat.eq_dec x ci); lia.
Qed.

(** Re-homing clause [ci] from the list of [fl] to the list of [ck]. *)
Lemma wch_rehome D W fl ck ci L i j cl1 cl2 Wck :
  Wch (lset D ci cl1) (lset W fl (firstn j L ++ skipn i L)) ->
  nth_error L i = Some ci -> fl < length W -> ck < length W -> ck <> fl ->
  nth_error W ck = Some Wck -> ci < length D ->
  (forall l, expect_cl cl2 l + (if Nat.eqb fl l then 1 else 0) = expect_cl cl1 l + (if Nat.eqb ck l then 1 else 0)) ->
  Wch (lset D ci cl2) (lset (lset W ck (Wck ++ [ci])) fl (firstn j L ++ skipn (S i) L)).
Proof.
  intros HW Hi Hfl Hck Hne HWck Hci He.
  eapply wch_mono; [exact HW | now rewrite !lset_length |].
  intros ci' l Hl. rewrite lset_length in Hl.
  rewrite !cnt_lset by (rewrite ?lset_length; lia).
  rewrite (count_occ_keep L i j ci' ci Hi).
  assert (Ek : cnt W ck ci' = count_occ Nat.eq_dec Wck ci') by (unfold cnt; now rewrite (nth_error_nth' W ck Wck [] HWck)).
  rewrite count_occ_app in *. cbn [count_occ] in *.
  destruct (Nat.eq_dec ci' ci) as [-> | Hne'].
  - rewrite !expect_lset_same by exact Hci. specialize (He l).
    destruct (Nat.eq_dec ci ci); [|congruence].
    destruct (Nat.eqb_spec fl l) as [E1 | N1]; destruct (Nat.eqb_spec ck l) as [E2 | N2]; subst; try lia;
      rewrite ?count_occ_app in *; cbn [count_occ] in *; repeat destruct (Nat.eq_dec _ _); try lia.
  - rewrite !expect_lset_other by exact Hne'.
    destruct (Nat.eq_dec ci ci'); [congruence|].
    destruct (Nat.eqb_spec fl l) as [E1 | N1]; destruct (Nat.eqb_spec ck l) as [E2 | N2]; subst; try lia;
      rewrite ?count_occ_app in *; cbn [count_occ] in *; repeat destruct (Nat.eq_dec _ _); try lia.
Qed.

Lemma wch_same_expect D W ci cl cl1 :
  Wch D W -> nth_error D ci = Some cl -> (forall l, expect_cl cl1 l = expect_cl cl l) ->
  Wch (lset D ci cl1) W.
Proof.
  intros HW Hd He. eapply wch_mono; [exact HW | reflexivity |]. intros ci' l _.
  destruct (Nat.eq_dec ci' ci) as [-> | Hne].
  - rewrite expect_lset_same by (apply nth_error_Some; congruence).
    rewrite (expect_nth D ci cl l Hd), He. lia.
  - rewrite expect_lset_other by exact Hne. lia.
Qed.

Lemma dset_id st : dset st (db st) = st.
Proof. now destruct st. Qed.

Lemma wset_id st : wset st (wl st) = st.
Proof. now destruct st. Qed.

(** * Conflicts *)

(** [q]'s variable is assigned at the current decision level. *)
Definition cur_lit (st : astate) (q : nat) : Prop :=
  exists k, at_pos (tr st) k (lvar q) /\ Forall (fun x => x <= k) (lim st).

(** [r] is a conflict clause's index + 1: every literal false, one at the current level. *)
Definition conflict (st : astate) (r : nat) : Prop :=
  exists ci cl, r = S ci /\ nth_error (db st) ci = Some cl /\
    Forall (fun q => lval (asg st) q = 2) cl /\ Exists (cur_lit st) cl.

Lemma all_false_cl A cl from :
  (forall p, from <= p < length cl -> lval A (nth p cl 0) = 2) -> Forall (fun q => lval A q = 2) (skipn from cl).
Proof.
  intros H. apply Forall_forall. intros q Hq. apply In_nth with (d := 0) in Hq as (p & Hp & <-).
  rewrite length_skipn in Hp. rewrite nth_skipn. apply H. lia.
Qed.

(** The literal a clause propagates at level 0 is true under [val]. *)
Lemma unit_true val st ci cl first :
  Core val st -> nth_error (db st) ci = Some cl -> length (lim st) = 0 ->
  nth_error cl 0 = Some first ->
  (forall p, 1 <= p < length cl -> lval (asg st) (nth p cl 0) = 2) -> lit_true val first.
Proof.
  intros C Hd H0 Hf Hrest.
  pose proof (Forall_nth_error _ _ _ _ (i_db _ _ C) Hd) as Hex.
  apply Exists_exists in Hex as (q & Hq & Ht).
  apply In_nth with (d := 0) in Hq as (p & Hp & <-).
  destruct p as [|p].
  - rewrite (nth_error_nth' cl 0 first 0 Hf) in Ht. exact Ht.
  - exfalso. assert (Hq : lval (asg st) (nth (S p) cl 0) = 2) by (apply Hrest; lia).
    apply (false_l0 val st C _ Hq); [|exact Ht].
    destruct (false_trail val st C _ Hq) as (k & Hk).
    pose proof (level_le val st C k _ Hk) as Hl. rewrite lvar_lneg in Hl. lia.
Qed.

Lemma tl_skipn1 {A} (xs : list A) : tl xs = skipn 1 xs.
Proof. now destruct xs. Qed.

(** Moving the queue head forward, or writing the other counters. *)
Lemma core_fset_misc val st m :
  Core val st -> qhead st <= nth QHEAD m 0 <= length (tr st) -> Core val (fset st FMisc m).
Proof.
  intros C Hq. destruct C. constructor; cbn [fv fset fld_eqb db]; auto.
  - eapply Forall_impl; [|eassumption]. cbn. lia.
  - lia.
Qed.

Lemma lneg_trail_false val st p : Core val st -> In p (tr st) -> lval (asg st) (lneg p) = 2.
Proof.
  intros C Hp. apply lval_neg_true; [rewrite lvar_lneg; apply (i_asg _ _ C)|].
  rewrite lneg_lneg. now apply (true_on_trail val st C).
Qed.

Lemma firstn_S_snoc {A} (xs : list A) i x : nth_error xs i = Some x -> firstn (S i) xs = firstn i xs ++ [x].
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] H; cbn in H |- *; try discriminate.
  - congruence.
  - f_equal. now apply IH.
Qed.

Lemma skipn_snoc {A} (xs : list A) m x : m <= length xs -> skipn m (xs ++ [x]) = skipn m xs ++ [x].
Proof. intros H. rewrite skipn_app. now replace (m - length xs) with 0 by lia. Qed.
