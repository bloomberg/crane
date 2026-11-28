(** The invariants of the abstract solver state ([Abstract.astate]), the
    pure facts about literals, levels and watch lists they need, and the
    model-free safety invariant [SI].  Nothing here mentions the heap:
    clauses are named by their index in [db], and a later layer relates
    indices to arena offsets.

    UNSAT soundness is proved by contradiction: fix a valuation that
    satisfies the input formula, and show that the solver never answers 0.
    "Entailed by the formula" then becomes "true under the valuation".
    [Core] takes the valuation as an [option]: [Core None st] is the purely
    structural part, which holds on every input and is what memory safety
    needs; [Core (Some v) st] adds the two parts that read [v].  Every
    preservation lemma works for any [val : option _], so one specification
    per function carries both.

    - [Core val]: every database clause holds under [val] (I4); the trail
      lists exactly the assigned variables, each once and true (I2); levels
      are the decision segments of trail positions (I2); every propagated
      literal's reason has it at position 0 and every other literal false
      and earlier on the trail (I3); every reason-less literal is a decision
      or comes before the first decision; every level-0 literal holds under
      [val] (I5); the queue head lies between the last decision and the end
      of the trail.
    - [Wch]: a clause occurs in a watch list no more often than it has that
      literal at position 0 or 1.  This is the membership half of I6, and
      UNSAT soundness needs it: [prop_watch] never reads the value of
      [c[1]], it relies on [c[1]] being the literal just made false.
    - [Seen0]: the analysis marks are clear between conflicts.
    - [AInv]: the first-UIP analysis invariant, including that the learnt
      literals have distinct variables, which bounds the learnt clause by
      the capacity [nv + 1] of its array.
    - [SI nv]: field lengths, literals below [2 * nv], watch entries naming
      clauses of length 2 or more, reasons naming clauses, decision
      positions strictly increasing and on the trail.  With [Core] it gives
      the fixed capacities of the trail and the trail limits. *)
From Stdlib Require Import List PeanoNat Lia Bool Permutation.
Require Import Solver Cnf Abstract.
Import ListNotations.
Import Solver.

(** Shorthands for the fields of an abstract state; [qhead] is slot [QHEAD]
    of [misc], the propagation queue head; [lrn] is the learnt clause. *)
Notation asg st := (fv st FAsg).
Notation lvl st := (fv st FLvl).
Notation rsn st := (fv st FRsn).
Notation sn st := (fv st FSn).
Notation tr st := (fv st FTr).
Notation lim st := (fv st FLim).
Notation lrn st := (fv st FLrn).
Notation qhead st := (nth QHEAD (fv st FMisc) 0).

(** * Literals *)

(** What [lit_value] answers when [l]'s variable holds [a]: 0 unassigned,
    1 true, 2 false. *)
Definition lval_of (a l : nat) : nat :=
  if Nat.eqb a 0 then 0 else if Nat.eqb (Nat.modulo l 2) 0 then a else 3 - a.

(** The value of literal [l] under the assignment vector [A]. *)
Definition lval (A : list nat) (l : nat) : nat := lval_of (nth (lvar l) A 0) l.

(** Halving an explicit [2 * q + r]. *)
Lemma div2_eq q r : r < 2 -> (2 * q + r) / 2 = q.
Proof. intros. symmetry. apply (Nat.div_unique _ _ _ r); lia. Qed.

(** The parity of an explicit [2 * q + r]. *)
Lemma mod2_eq q r : r < 2 -> (2 * q + r) mod 2 = r.
Proof. intros. symmetry. apply (Nat.mod_unique _ _ q); lia. Qed.

(** Every literal is [2v] (positive) or [2v+1] (negative) for its variable [v]. *)
Lemma lit_cases l : (l = 2 * lvar l /\ l mod 2 = 0) \/ (l = 2 * lvar l + 1 /\ l mod 2 = 1).
Proof.
  unfold lvar. pose proof (Nat.div_mod_eq l 2). pose proof (Nat.mod_upper_bound l 2).
  assert (l mod 2 = 0 \/ l mod 2 = 1) as [E | E] by lia; [left | right]; split; lia.
Qed.

(** The variable of a positive literal. *)
Lemma lvar_2v v : lvar (2 * v) = v.
Proof. unfold lvar. pose proof (div2_eq v 0) as H. rewrite Nat.add_0_r in H. apply H. lia. Qed.

(** The variable of a negative literal. *)
Lemma lvar_2v1 v : lvar (2 * v + 1) = v.
Proof. unfold lvar. apply div2_eq. lia. Qed.

(** A positive literal is even. *)
Lemma mod_2v v : (2 * v) mod 2 = 0.
Proof. pose proof (mod2_eq v 0) as H. rewrite Nat.add_0_r in H. apply H. lia. Qed.

(** A negative literal is odd. *)
Lemma mod_2v1 v : (2 * v + 1) mod 2 = 1.
Proof. apply mod2_eq. lia. Qed.

(** [lneg] flips the parity bit. *)
Lemma lneg_cases l :
  (l mod 2 = 0 /\ lneg l = l + 1) \/ (l mod 2 = 1 /\ lneg l = l - 1).
Proof. unfold lneg. destruct (lit_cases l) as [[_ E] | [_ E]]; rewrite E; cbn; auto. Qed.

(** A literal and its negation share a variable. *)
Lemma lvar_lneg l : lvar (lneg l) = lvar l.
Proof.
  destruct (lit_cases l) as [[E M] | [E M]]; unfold lneg; rewrite M; cbn.
  - rewrite E at 1. apply lvar_2v1.
  - rewrite E at 1. replace (2 * lvar l + 1 - 1) with (2 * lvar l) by lia. apply lvar_2v.
Qed.

(** Negation flips polarity. *)
Lemma lneg_mod l : lneg l mod 2 = 1 - l mod 2.
Proof.
  destruct (lit_cases l) as [[E M] | [E M]]; unfold lneg; rewrite M; cbn.
  - rewrite E at 1. apply mod_2v1.
  - rewrite E at 1. replace (2 * lvar l + 1 - 1) with (2 * lvar l) by lia. apply mod_2v.
Qed.

(** Negation is an involution. *)
Lemma lneg_lneg l : lneg (lneg l) = l.
Proof.
  destruct (lit_cases l) as [[E M] | [E M]]; set (v := lvar l) in *; clearbody v; subst l; unfold lneg.
  - rewrite mod_2v. cbn [Nat.eqb]. rewrite mod_2v1. cbn [Nat.eqb]. lia.
  - rewrite mod_2v1. cbn [Nat.eqb]. replace (2 * v + 1 - 1) with (2 * v) by lia.
    rewrite mod_2v. cbn [Nat.eqb]. lia.
Qed.

(** No literal is its own negation. *)
Lemma lneg_neq l : lneg l <> l.
Proof. intros E. pose proof (lneg_mod l) as M. rewrite E in M. pose proof (Nat.mod_upper_bound l 2). lia. Qed.

(** A literal is determined by its variable and polarity. *)
Lemma lit_eq a b : lvar a = lvar b -> a mod 2 = b mod 2 -> a = b.
Proof.
  intros E M. destruct (lit_cases a) as [[Ea Ma] | [Ea Ma]], (lit_cases b) as [[Eb Mb] | [Eb Mb]]; lia.
Qed.

(** A well-formed assignment entry gives a literal value of at most 2. *)
Lemma lval_le2 A l : nth (lvar l) A 0 <= 2 -> lval A l <= 2.
Proof.
  unfold lval, lval_of. intros.
  destruct (Nat.eqb_spec (nth (lvar l) A 0) 0); [lia|]. destruct (Nat.eqb (l mod 2) 0); lia.
Qed.

(** Case-split every [Nat.eqb] in the goal. *)
Ltac eqbs := repeat match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y) end.

(** Case on the parity of [l] and substitute [l := 2v] or [2v+1]. *)
Ltac par l :=
  let v := fresh "v" in let E := fresh "E" in let M := fresh "M" in
  destruct (lit_cases l) as [[E M] | [E M]]; set (v := lvar l) in *; clearbody v; subst l;
  rewrite ?lvar_2v, ?lvar_2v1, ?mod_2v, ?mod_2v1 in *.

(** A literal is unassigned iff its variable is. *)
Lemma lval_zero A l : nth (lvar l) A 0 <= 2 -> lval A l = 0 <-> nth (lvar l) A 0 = 0.
Proof. unfold lval, lval_of. revert l. intros l. par l; cbn [Nat.eqb]; eqbs; lia. Qed.

(** The negation of a positive literal. *)
Lemma lneg_2v v : lneg (2 * v) = 2 * v + 1.
Proof. unfold lneg. now rewrite mod_2v. Qed.

(** The negation of a negative literal. *)
Lemma lneg_2v1 v : lneg (2 * v + 1) = 2 * v.
Proof. unfold lneg. rewrite mod_2v1. cbn [Nat.eqb]. lia. Qed.

(** [par] that also computes [lneg]. *)
Ltac parn l := par l; rewrite ?lneg_2v, ?lneg_2v1, ?lvar_2v, ?lvar_2v1, ?mod_2v, ?mod_2v1 in *.

(** Negation swaps true and false and keeps unassigned. *)
Lemma lval_lneg A l : nth (lvar l) A 0 <= 2 ->
  lval A (lneg l) = if Nat.eqb (nth (lvar l) A 0) 0 then 0 else 3 - lval A l.
Proof. unfold lval, lval_of. parn l; cbn [Nat.eqb]; eqbs; lia. Qed.

(** [l] is false iff [lneg l] is true. *)
Lemma lval_neg_true A l : nth (lvar l) A 0 <= 2 -> lval A l = 2 <-> lval A (lneg l) = 1.
Proof. unfold lval, lval_of. parn l; cbn [Nat.eqb]; eqbs; lia. Qed.

(** At most one literal per variable is true. *)
Lemma lval_true_inj A a b : lval A a = 1 -> lval A b = 1 -> lvar a = lvar b -> a = b.
Proof.
  unfold lval, lval_of. intros Ha Hb E. rewrite <- E in Hb. revert Ha Hb E.
  par a; par b; cbn [Nat.eqb]; eqbs; intros; lia.
Qed.

(** [Nat.even], which [lit_true] uses, agrees with the solver's parity test. *)
Lemma even_mod l : Nat.even l = Nat.eqb (l mod 2) 0.
Proof.
  par l; cbn [Nat.eqb].
  - now rewrite Nat.even_mul.
  - now rewrite Nat.even_add, Nat.even_mul.
Qed.

(** Positive literals are even. *)
Lemma even_2v v : Nat.even (2 * v) = true.
Proof. now rewrite even_mod, mod_2v. Qed.

(** Negative literals are odd. *)
Lemma even_2v1 v : Nat.even (2 * v + 1) = false.
Proof. now rewrite even_mod, mod_2v1. Qed.

(** Under a total model, exactly one of [l] and [lneg l] is true. *)
Lemma lit_true_lneg val l : lit_true val (lneg l) <-> ~ lit_true val l.
Proof.
  unfold lit_true. parn l; rewrite ?even_2v, ?even_2v1; destruct (val v); intuition congruence.
Qed.

(** The code [enqueue] stores for [l]'s variable: the one that makes [l] true. *)
Definition lit_code (l : nat) : nat := if Nat.eqb (l mod 2) 0 then 1 else 2.

(** [lit_code] is a well-formed code. *)
Lemma lit_code_le l : lit_code l <= 2.
Proof. unfold lit_code. destruct (Nat.eqb (l mod 2) 0); lia. Qed.

(** [lit_code] marks the variable assigned. *)
Lemma lit_code_nz l : lit_code l <> 0.
Proof. unfold lit_code. destruct (Nat.eqb (l mod 2) 0); lia. Qed.

(** [lit_code l] makes [l] true. *)
Lemma lval_of_code l : lval_of (lit_code l) l = 1.
Proof. unfold lval_of, lit_code. par l; reflexivity. Qed.

(** [lit_code l] makes [lneg l] false. *)
Lemma lval_of_code_neg l : lval_of (lit_code l) (lneg l) = 2.
Proof. unfold lval_of, lit_code. parn l; reflexivity. Qed.

(** A literal's value after a write to some variable's assignment entry. *)
Lemma lval_lset A v x l :
  lval (lset A v x) l = if Nat.eqb v (lvar l) then (if Nat.ltb v (length A) then lval_of x l else 0)
                        else lval A l.
Proof.
  unfold lval. rewrite nth_lset.
  destruct (Nat.eqb v (lvar l)); [destruct (Nat.ltb v (length A))|]; reflexivity.
Qed.

(** A write to another variable's entry keeps [l]'s value. *)
Lemma lval_lset_neq A v x l : v <> lvar l -> lval (lset A v x) l = lval A l.
Proof. intros. rewrite lval_lset. now destruct (Nat.eqb_spec v (lvar l)). Qed.

(** [val] contradicts the solver's assignment of [v].  A false literal can be
    true under [val] only on such a variable. *)
Definition disagree (val : nat -> bool) (A : list nat) (v : nat) : Prop :=
  nth v A 0 <> 0 /\ val v <> Nat.eqb (nth v A 0) 1.

(** A literal false under the assignment but true under [val] marks a disagreement. *)
Lemma false_true_disagree val A q :
  nth (lvar q) A 0 <= 2 -> lval A q = 2 -> lit_true val q -> disagree val A (lvar q).
Proof.
  unfold lval, lval_of, lit_true, disagree. par q; rewrite ?even_2v, ?even_2v1; cbn [Nat.eqb];
    destruct (val v); eqbs; intuition (try lia; try congruence).
Qed.

(** On a disagreeing variable, every false literal is true under [val]. *)
Lemma false_disagree_true val A q :
  nth (lvar q) A 0 <= 2 -> lval A q = 2 -> disagree val A (lvar q) -> lit_true val q.
Proof.
  unfold lval, lval_of, lit_true, disagree. par q; rewrite ?even_2v, ?even_2v1; cbn [Nat.eqb];
    destruct (val v); eqbs; intuition (try lia; try congruence).
Qed.

(** On a disagreeing variable, a true literal's negation is true under [val]. *)
Lemma true_disagree_false val A p :
  lval A p = 1 -> disagree val A (lvar p) -> lit_true val (lneg p).
Proof.
  intros Hp Hd. apply lit_true_lneg. revert Hp Hd.
  unfold lval, lval_of, lit_true, disagree. par p; rewrite ?even_2v, ?even_2v1; cbn [Nat.eqb];
    destruct (val v); eqbs; intuition (try lia; try congruence).
Qed.

(** * Levels *)

(** The decision level of trail position [k]: the number of decisions at or before it. *)
Definition count_le (lim : list nat) (k : nat) : nat := length (filter (fun x => Nat.leb x k) lim).

(** [l] is nondecreasing. *)
Definition sorted (l : list nat) : Prop :=
  forall i j, i < j < length l -> nth i l 0 <= nth j l 0.

(** A level never exceeds the number of decisions. *)
Lemma count_le_max lim k : count_le lim k <= length lim.
Proof. apply filter_length_le. Qed.

(** A position after every decision is at the top level. *)
Lemma count_le_all lim k : Forall (fun x => x <= k) lim -> count_le lim k = length lim.
Proof.
  unfold count_le. induction 1; cbn; auto. destruct (Nat.leb_spec x k); cbn; [lia | lia].
Qed.

(** A new decision raises the level of positions at or after it. *)
Lemma count_le_snoc lim x k : count_le (lim ++ [x]) k = count_le lim k + (if Nat.leb x k then 1 else 0).
Proof. unfold count_le. rewrite filter_app, length_app. cbn. now destruct (Nat.leb x k). Qed.

(** Appending an upper bound keeps a list sorted. *)
Lemma sorted_snoc l x : sorted l -> Forall (fun y => y <= x) l -> sorted (l ++ [x]).
Proof.
  intros Hs F i j Hij. rewrite length_app in Hij. cbn in Hij.
  rewrite app_nth1 by lia.
  destruct (Nat.eq_dec j (length l)) as [-> | Hj].
  - rewrite app_nth2, Nat.sub_diag by lia. cbn.
    rewrite Forall_forall in F. apply F, nth_In. lia.
  - rewrite app_nth1 by lia. apply Hs. lia.
Qed.

(** Prefixes of a sorted list are sorted. *)
Lemma sorted_firstn l n : sorted l -> sorted (firstn n l).
Proof.
  intros Hs i j Hij. rewrite length_firstn in Hij.
  rewrite !nth_firstn. destruct (Nat.ltb_spec i n), (Nat.ltb_spec j n); try lia.
  apply Hs. lia.
Qed.

(** In a sorted list, everything before index [n] is at most the [n]-th entry. *)
Lemma sorted_le_nth l n x : sorted l -> n < length l -> In x (firstn n l) -> x <= nth n l 0.
Proof.
  intros Hs Hn Hx. apply In_nth with (d := 0) in Hx as (i & Hi & <-).
  rewrite length_firstn in Hi. rewrite nth_firstn.
  destruct (Nat.ltb_spec i n); [|lia]. apply Hs. lia.
Qed.

(** The tail of a sorted list is sorted and bounded below by the head. *)
Lemma sorted_cons a l : sorted (a :: l) -> sorted l /\ Forall (fun x => a <= x) l.
Proof.
  intros Hs. split.
  - intros i j Hij. apply (Hs (S i) (S j)). cbn. lia.
  - apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx as (j & Hj & <-).
    apply (Hs 0 (S j)). cbn. lia.
Qed.

(** Before the first decision, the level is 0. *)
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

(** The converse of [count_le_all]. *)
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

(** Dropping decisions after position [k] keeps [k]'s level: backtracking
    does not relevel the kept trail. *)
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

(** A read from [xs ++ [x]] reads [xs] or hits [x]. *)
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

(** A push keeps the earlier entries. *)
Lemma nth_error_snoc_lt {A} (xs : list A) x k : k < length xs -> nth_error (xs ++ [x]) k = nth_error xs k.
Proof. apply nth_error_app1. Qed.

(** The pushed entry sits at the old length. *)
Lemma nth_error_snoc_eq {A} (xs : list A) x : nth_error (xs ++ [x]) (length xs) = Some x.
Proof. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

(** A member of a mapped list comes from some position. *)
Lemma in_map_nth_error {A B} (f : A -> B) xs y :
  In y (map f xs) -> exists k x, nth_error xs k = Some x /\ f x = y.
Proof.
  intros Hy. apply in_map_iff in Hy as (x & <- & Hx).
  apply In_nth_error in Hx as (k & Hk). eauto.
Qed.

(** An entry's image is in the mapped list. *)
Lemma nth_error_in_map {A B} (f : A -> B) xs k x : nth_error xs k = Some x -> In (f x) (map f xs).
Proof. intros. apply in_map. eapply nth_error_In; eauto. Qed.

(** In a list without duplicates, an element has one position. *)
Lemma nodup_nth_error {A} (xs : list A) i j x :
  NoDup xs -> nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof. intros Hn Hi Hj. eapply NoDup_nth_error; eauto. apply nth_error_Some. congruence. congruence. Qed.

(** Variable [v] is assigned at trail position [k]. *)
Definition at_pos (T : list nat) (k v : nat) : Prop := exists l, nth_error T k = Some l /\ lvar l = v.

(** On a trail without repeated variables, each variable has one position. *)
Lemma at_pos_unique T k k' v : NoDup (map lvar T) -> at_pos T k v -> at_pos T k' v -> k = k'.
Proof.
  intros Hn (l & Hl & El) (l' & Hl' & El').
  apply (nodup_nth_error (map lvar T) k k' v Hn); rewrite nth_error_map.
  - rewrite Hl; cbn [option_map]; now rewrite El.
  - rewrite Hl'; cbn [option_map]; now rewrite El'.
Qed.

(** A trail position is in range. *)
Lemma at_pos_lt T k v : at_pos T k v -> k < length T.
Proof. intros (l & Hl & _). apply nth_error_Some. congruence. Qed.

(** Positions survive a push onto the trail. *)
Lemma at_pos_snoc T x k v : at_pos T k v -> at_pos (T ++ [x]) k v.
Proof. intros (l & Hl & E). exists l. split; [|exact E]. rewrite nth_error_snoc_lt; auto. apply nth_error_Some. congruence. Qed.

(** Positions survive truncating the trail above them. *)
Lemma at_pos_firstn T m k v : k < m -> at_pos T k v -> at_pos (firstn m T) k v.
Proof. intros Hk (l & Hl & E). exists l. split; [|exact E]. rewrite nth_error_firstn. now destruct (Nat.ltb_spec k m); [|lia]. Qed.

(** A variable with a position is a trail variable. *)
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

(** Prefixes keep [NoDup]. *)
Lemma nodup_firstn {A} (xs : list A) n : NoDup xs -> NoDup (firstn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. eapply NoDup_app_remove_r; eauto. Qed.

(** A member is in the prefix or the suffix. *)
Lemma in_firstn_skipn {A} (xs : list A) n x : In x xs -> In x (firstn n xs) \/ In x (skipn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. now apply in_app_or. Qed.

(** Keep these from unfolding under [cbn]: proofs rewrite with the lemmas
    instead (the [lset_cons*] rules for [lset]). *)
Global Arguments lvar : simpl never.
Global Arguments lneg : simpl never.
Global Arguments lval : simpl never.
Global Arguments lset : simpl never.

(** [lset] at the head. *)
Lemma lset_cons0 {A} (a : A) xs x : lset (a :: xs) 0 x = x :: xs.
Proof. reflexivity. Qed.

(** [lset] below the head. *)
Lemma lset_consS {A} (a : A) xs i x : lset (a :: xs) (S i) x = a :: lset xs i x.
Proof. reflexivity. Qed.

(** [lset] on the empty list. *)
Lemma lset_nil {A} i (x : A) : lset [] i x = [].
Proof. now destruct i. Qed.

(** * The invariants *)

(** Literal [l], at trail position [k], has reason clause [r]: [l] is its
    first literal, and every other literal is false and earlier. *)
Definition reason_ok (st : astate) (k l r : nat) : Prop :=
  exists c, nth_error (db st) r = Some c /\ nth_error c 0 = Some l /\
    Forall (fun q => lval (asg st) q = 2 /\ exists k', k' < k /\ at_pos (tr st) k' (lvar q)) (tl c).

(** Literal [l] holds under the optional valuation [val]: always, when there
    is none. *)
Definition holds (val : option (nat -> bool)) (l : nat) : Prop :=
  match val with Some v => lit_true v l | None => True end.

(** Clause [c] holds under [val]: some literal is true under the valuation,
    if there is one.  Without one this asks nothing, not even [c <> []], so
    that storing an empty input clause keeps [Core None]. *)
Definition cholds (val : option (nat -> bool)) (c : list nat) : Prop :=
  match val with Some v => Exists (lit_true v) c | None => True end.

(** [cholds] ignores the order of the literals. *)
Lemma cholds_perm val c c' : Permutation c c' -> cholds val c -> cholds val c'.
Proof. intros Hp. destruct val; cbn; [now apply Permutation_Exists | auto]. Qed.

(** The core invariant against the optional model [val]; the file header
    explains each part. *)
Record Core (val : option (nat -> bool)) (st : astate) : Prop := {
  (** I4: every clause holds under [val]. *)
  i_db : Forall (cholds val) (db st);
  (** Assignment codes are 0, 1 or 2. *)
  i_asg : forall v, nth v (asg st) 0 <= 2;
  (** No variable occurs twice on the trail. *)
  i_nd : NoDup (map lvar (tr st));
  (** The assigned variables are exactly the trail's. *)
  i_tr : forall v, nth v (asg st) 0 <> 0 <-> In v (map lvar (tr st));
  (** Every trail literal is true. *)
  i_true : Forall (fun l => lval (asg st) l = 1) (tr st);
  (** A trail literal's level is the decision count up to its position. *)
  i_lvl : forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (lvl st) 0 = count_le (lim st) k;
  (** Decision positions increase. *)
  i_sorted : sorted (lim st);
  (** Every decision is at or before the queue head. *)
  i_limq : Forall (fun x => x <= qhead st) (lim st);
  (** The queue head is within the trail. *)
  i_qtr : qhead st <= length (tr st);
  (** I3: a recorded reason justifies its literal. *)
  i_rsn : forall k l r, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 = S r -> reason_ok st k l r;
  (** A reason-less literal precedes every decision or is one. *)
  i_dec : forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 = 0 ->
            Forall (fun x => k <= x) (lim st) \/ In k (lim st);
  (** I5: level-0 literals hold under [val]. *)
  i_l0 : forall l, In l (tr st) -> nth (lvar l) (lvl st) 0 = 0 -> holds val l
}.

(** How often a clause [c] may occur in [l]'s watch list: once per watched
    position, 0 or 1, holding [l]; never for a clause shorter than 2. *)
Definition expect_cl (c : list nat) (l : nat) : nat :=
  if Nat.leb 2 (length c)
  then (if Nat.eqb (nth 0 c 0) l then 1 else 0) + (if Nat.eqb (nth 1 c 0) l then 1 else 0)
  else 0.

(** [expect_cl] for clause index [ci] of [D]; 0 out of range. *)
Definition expect (D : list (list nat)) (ci l : nat) : nat :=
  match nth_error D ci with Some c => expect_cl c l | None => 0 end.

(** How often clause index [ci] occurs in [l]'s watch list. *)
Definition cnt (W : list (list nat)) (l ci : nat) : nat := count_occ Nat.eq_dec (nth l W []) ci.

(** Watch membership: no clause occurs in a watch list more often than it
    watches that literal. *)
Definition Wch (D : list (list nat)) (W : list (list nat)) : Prop :=
  forall ci l, l < length W -> cnt W l ci <= expect D ci l.

(** Every analysis mark is clear. *)
Definition Seen0 (st : astate) : Prop := forall v, nth v (sn st) 0 = 0.

(** The full invariant between solver steps. *)
Definition Inv (val : option (nat -> bool)) (st : astate) : Prop :=
  Core val st /\ Wch (db st) (wl st) /\ Seen0 st.

(** * Consequences *)

(** Consequences of [Core] for a fixed state. *)
Section Facts.
Variables (val : option (nat -> bool)) (st : astate).
Hypothesis C : Core val st.

(** Literal values are 0, 1 or 2. *)
Lemma asg_lval_le2 l : lval (asg st) l <= 2.
Proof. apply lval_le2, (i_asg _ _ C). Qed.

(** Trail literals are true. *)
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

(** A false literal's negation is on the trail. *)
Lemma false_trail q : lval (asg st) q = 2 -> exists k, nth_error (tr st) k = Some (lneg q).
Proof. intros Hq. apply true_trail. now apply lval_neg_true; [apply (i_asg _ _ C)|]. Qed.

(** A false literal's variable has a trail position. *)
Lemma false_at_pos q : lval (asg st) q = 2 -> exists k, at_pos (tr st) k (lvar q).
Proof.
  intros Hq. destruct (false_trail q Hq) as (k & Hk). exists k, (lneg q). split; [exact Hk|]. apply lvar_lneg.
Qed.

(** An assigned literal's variable has a trail position. *)
Lemma assigned_at_pos q : lval (asg st) q <> 0 -> exists k, at_pos (tr st) k (lvar q).
Proof.
  intros Hq. assert (nth (lvar q) (asg st) 0 <> 0) as Ha.
  { intros E. apply Hq. now apply (lval_zero (asg st) q (i_asg _ _ C _)). }
  apply (i_tr _ _ C) in Ha. apply in_map_nth_error in Ha as (k & l' & Hk & E). exists k, l'. auto.
Qed.

(** A trail variable is assigned. *)
Lemma at_pos_assigned k v : at_pos (tr st) k v -> nth v (asg st) 0 <> 0.
Proof. intros H. apply (i_tr _ _ C). eapply at_pos_in; eauto. Qed.

(** Levels are bounded by the number of decisions. *)
Lemma level_le k l : nth_error (tr st) k = Some l -> nth (lvar l) (lvl st) 0 <= length (lim st).
Proof. intros H. rewrite (i_lvl _ _ C k l H). apply count_le_max. Qed.

End Facts.

(** The consequences of [Core] that read the valuation. *)
Section ModelFacts.
Variables (val : nat -> bool) (st : astate).
Hypothesis C : Core (Some val) st.

(** A literal false at level 0 is false under [val]. *)
Lemma false_l0 q : lval (asg st) q = 2 -> nth (lvar q) (lvl st) 0 = 0 -> ~ lit_true val q.
Proof.
  intros Hq H0. destruct (false_trail _ _ C q Hq) as (k & Hk).
  apply lit_true_lneg. apply (i_l0 _ _ C).
  - eapply nth_error_In; eauto.
  - now rewrite lvar_lneg.
Qed.

(** With no decision on the trail, no clause is all false: its literal true under
    [val] would be false at level 0.  So a level-0 conflict refutes the model. *)
Lemma no_false_clause_l0 c : length (lim st) = 0 -> In c (db st) -> Forall (fun q => lval (asg st) q = 2) c -> False.
Proof.
  intros H0 Hc Hf. pose proof (i_db _ _ C) as D. rewrite Forall_forall in D.
  apply D, Exists_exists in Hc as (q & Hq & Ht).
  rewrite Forall_forall in Hf. specialize (Hf q Hq).
  destruct (false_trail _ _ C q Hf) as (k & Hk).
  apply (false_l0 q Hf); [|exact Ht].
  pose proof (level_le _ _ C k _ Hk) as Hl. rewrite lvar_lneg in Hl. lia.
Qed.

End ModelFacts.

(** * Preservation *)

(** [nodup_snoc] at any element type. *)
Lemma nodup_snoc' {A} (l : list A) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros H Hx. apply NoDup_app; auto; [constructor; auto; constructor|].
  intros a Ha [<- | []]. auto.
Qed.

(** [Core] reads only the clauses, assignment, levels, reasons, trail,
    decisions and queue head. *)
Lemma core_ext val st st' :
  db st' = db st -> asg st' = asg st -> lvl st' = lvl st -> rsn st' = rsn st ->
  tr st' = tr st -> lim st' = lim st -> qhead st' = qhead st -> Core val st -> Core val st'.
Proof.
  intros Ed Ea El Er Et Em Eq [? ? ? ? ? ? ? ? ? Hr ? ?].
  constructor; unfold reason_ok in *; rewrite ?Ed, ?Ea, ?El, ?Er, ?Et, ?Em, ?Eq; auto.
Qed.

(** Writes to phase, stamp, seen marks or the learnt clause keep [Core]. *)
Lemma core_fset_other val st f xs :
  f = FPh \/ f = FSt \/ f = FSn \/ f = FLrn -> Core val st -> Core val (fset st f xs).
Proof. intros Hf. apply core_ext; cbn; destruct Hf as [-> | [-> | [-> | ->]]]; reflexivity. Qed.

(** Watch-list writes keep [Core]. *)
Lemma core_wset val st w : Core val st -> Core val (wset st w).
Proof. apply core_ext; reflexivity. Qed.

(** Two literals on one variable are equal or opposite. *)
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

(** Values after [enqueue l]: [l] true, [lneg l] false, the rest unchanged. *)
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

(** Literals on other variables keep their value. *)
Lemma lval_enq_other A l q : lvar l < length A -> lvar q <> lvar l ->
  lval (lset A (lvar l) (lit_code l)) q = lval A q.
Proof. intros _ Hne. apply lval_lset_neq. auto. Qed.

(** [enqueue l r] keeps [Core] for an unassigned [l] with a justification: for
    [r = 0] its position precedes every decision or is one; for [r = S ci] a reason
    clause has [l] first and the rest false.  At level 0, [l] must hold under [val]. *)
Lemma core_enq val st l r :
  Core val st -> lval (asg st) l = 0 ->
  lvar l < length (asg st) -> lvar l < length (lvl st) -> lvar l < length (rsn st) ->
  (r = 0 -> Forall (fun x => length (tr st) <= x) (lim st) \/ In (length (tr st)) (lim st)) ->
  (forall ci, r = S ci -> exists c, nth_error (db st) ci = Some c /\ nth_error c 0 = Some l /\
                            Forall (fun q => lval (asg st) q = 2) (tl c)) ->
  (length (lim st) = 0 -> holds val l) ->
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
  constructor; cbn [fv fset fld_eqb db wl].
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

(** A prefix member is a member. *)
Lemma in_firstn {A} (xs : list A) n x : In x (firstn n xs) -> In x xs.
Proof. intros H. rewrite <- (firstn_skipn n xs). apply in_or_app. auto. Qed.

(** A read from a prefix is an in-range read from the list. *)
Lemma nth_error_firstn_inv {A} (xs : list A) m k x :
  nth_error (firstn m xs) k = Some x -> k < m /\ nth_error xs k = Some x.
Proof.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec k m); [auto | discriminate].
Qed.

(** A prefix member has a position below the cut. *)
Lemma in_firstn_pos {A} (xs : list A) m x : In x (firstn m xs) -> exists k, k < m /\ nth_error xs k = Some x.
Proof. intros H. apply In_nth_error in H as (k & Hk). apply nth_error_firstn_inv in Hk. eauto. Qed.

(** The two halves of a [NoDup] concatenation are disjoint. *)
Lemma nodup_app_disj {A} (l1 l2 : list A) x : NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; intros H H1 H2; [destruct H1|].
  inversion H as [|? ? Ha Hn]; subst. destruct H1 as [<- | H1].
  - apply Ha, in_or_app. auto.
  - eauto.
Qed.

(** A literal's value depends only on its variable's entry. *)
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

(** Backtracking to an existing level keeps [Core]: the kept prefix keeps its
    levels, and its reasons mention only earlier, still-assigned literals. *)
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

(** [lset] with a good value keeps a [Forall]. *)
Lemma Forall_lset {A} (P : A -> Prop) xs i x : Forall P xs -> P x -> Forall P (lset xs i x).
Proof.
  intros H Hx. revert i. induction H; intros [|i]; rewrite ?lset_nil, ?lset_cons0, ?lset_consS; constructor; auto.
Qed.

(** An entry of a [Forall] list satisfies the predicate. *)
Lemma Forall_nth_error {A} (P : A -> Prop) xs i x : Forall P xs -> nth_error xs i = Some x -> P x.
Proof. intros H Hi. rewrite Forall_forall in H. apply H. eapply nth_error_In; eauto. Qed.

(** A clause whose first literal is not true is no literal's reason, so
    [core_dset] may permute it. *)
Lemma not_reason val st ci cl :
  Core val st -> nth_error (db st) ci = Some cl -> (forall x, nth_error cl 0 = Some x -> lval (asg st) x <> 1) ->
  forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 <> S ci.
Proof.
  intros C Hc Hx k l Hk Hr. destruct (i_rsn _ _ C k l ci Hk Hr) as (c & Hc' & H0 & _).
  rewrite Hc in Hc'. injection Hc' as <-. apply (Hx l H0). apply (true_on_trail val st C).
  eapply nth_error_In; eauto.
Qed.

(** Permuting a clause that is no literal's reason keeps [Core]: truth under
    [val] ignores the order. *)
Lemma core_dset val st ci cl cl' :
  Core val st -> nth_error (db st) ci = Some cl -> Permutation cl cl' ->
  (forall k l, nth_error (tr st) k = Some l -> nth (lvar l) (rsn st) 0 <> S ci) ->
  Core val (dset st (lset (db st) ci cl')).
Proof.
  intros C Hc Hp Hnr. destruct C as [Cdb ? ? ? ? ? ? ? ? Cr ? ?]. constructor; cbn [dset db fv]; auto.
  - apply Forall_lset; [exact Cdb|]. eapply cholds_perm; [exact Hp|]. eapply Forall_nth_error; eauto.
  - intros k l r Hk Hr. destruct (Cr k l r Hk Hr) as (c & Hc' & ?). exists c. cbn [dset db fv]. split; [|auto].
    rewrite nth_error_lset_neq; [exact Hc'|]. intros ->. exact (Hnr k l Hk Hr).
Qed.

(** Adding a clause that holds under [val] keeps [Core]. *)
Lemma core_cpush val st cl : Core val st -> cholds val cl -> Core val (cpush st cl).
Proof.
  intros C Hcl. destruct C as [Cdb ? ? ? ? ? ? ? ? Cr ? ?]. constructor; cbn [cpush db fv]; auto.
  - apply Forall_app. auto.
  - intros k l r Hk Hr. destruct (Cr k l r Hk Hr) as (c' & Hc' & ?). exists c'. cbn [cpush db fv]. split; [|auto].
    rewrite nth_error_app1; [exact Hc'|]. apply nth_error_Some. congruence.
Qed.

(** * Permutations by swapping *)

(** Overwriting position [i] trades one occurrence of the old entry for one of the new. *)
Lemma count_occ_lset xs i x y : i < length xs ->
  count_occ Nat.eq_dec (lset xs i x) y + (if Nat.eqb (nth i xs 0) y then 1 else 0) =
  count_occ Nat.eq_dec xs y + (if Nat.eqb x y then 1 else 0).
Proof.
  revert i. induction xs as [|a xs IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; rewrite ?lset_cons0, ?lset_consS; cbn [nth count_occ].
  - destruct (Nat.eq_dec x y), (Nat.eq_dec a y), (Nat.eqb_spec a y), (Nat.eqb_spec x y); lia.
  - cbn in Hi. specialize (IH i ltac:(lia)). destruct (Nat.eq_dec a y); lia.
Qed.

(** Swapping two positions is a permutation; the watch updates permute clauses. *)
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

(** Swapping keeps the length. *)
Lemma nth_swap_len {A} (xs : list A) i j a b : length (lset (lset xs i a) j b) = length xs.
Proof. now rewrite !lset_length. Qed.

(** * Watch lists *)

(** [Wch] carries over an update in which no count grows by more than its bound. *)
Lemma wch_mono D W D' W' :
  Wch D W -> length W' = length W ->
  (forall ci l, l < length W -> cnt W' l ci + expect D ci l <= cnt W l ci + expect D' ci l) ->
  Wch D' W'.
Proof.
  intros H E H'. intros ci l Hl. rewrite E in Hl. specialize (H ci l Hl). specialize (H' ci l Hl). lia.
Qed.

(** A clause in [l]'s watch list exists, has two literals or more, and has [l]
    at position 0 or 1: what [prop_watch] relies on. *)
Lemma wch_in D W l ci : Wch D W -> l < length W -> In ci (nth l W []) ->
  exists cl, nth_error D ci = Some cl /\ 2 <= length cl /\ (nth 0 cl 0 = l \/ nth 1 cl 0 = l).
Proof.
  intros H Hl Hi. specialize (H ci l Hl). unfold cnt, expect, expect_cl in H.
  apply (count_occ_In Nat.eq_dec) in Hi.
  destruct (nth_error D ci) as [cl|]; [|lia]. exists cl. split; [reflexivity|].
  destruct (Nat.leb_spec 2 (length cl)); [|lia]. split; [assumption|].
  destruct (Nat.eqb_spec (nth 0 cl 0) l), (Nat.eqb_spec (nth 1 cl 0) l); auto; lia.
Qed.

(** Rewriting one clause leaves the other clauses' bounds. *)
Lemma expect_lset_other D ci cl ci' l : ci' <> ci -> expect (lset D ci cl) ci' l = expect D ci' l.
Proof. intros. unfold expect. now rewrite nth_error_lset_neq by auto. Qed.

(** The rewritten clause's bound is that of its new contents. *)
Lemma expect_lset_same D ci cl l : ci < length D -> expect (lset D ci cl) ci l = expect_cl cl l.
Proof. intros. unfold expect. now rewrite nth_error_lset_eq. Qed.

(** [expect] unfolded at a known clause. *)
Lemma expect_nth D ci cl l : nth_error D ci = Some cl -> expect D ci l = expect_cl cl l.
Proof. unfold expect. now intros ->. Qed.

(** Swapping the two watched positions keeps every bound. *)
Lemma expect_swap01 cl l : 2 <= length cl ->
  expect_cl (lset (lset cl 0 (nth 1 cl 0)) 1 (nth 0 cl 0)) l = expect_cl cl l.
Proof.
  intros H. unfold expect_cl. rewrite !lset_length, !nth_lset, !lset_length.
  repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b); try lia end.
  repeat match goal with |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b); try lia end.
  cbn [Nat.eqb].
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b) end; lia.
Qed.

(** Swapping watched position 1 with position [k]: [c[1]] loses a watch
    and [c[k]] gains one. *)
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

(** Counts after replacing one watch list. *)
Lemma cnt_lset W a xs l ci : a < length W ->
  cnt (lset W a xs) l ci = if Nat.eqb a l then count_occ Nat.eq_dec xs ci else cnt W l ci.
Proof.
  intros Ha. unfold cnt. rewrite nth_lset.
  destruct (Nat.eqb a l); [destruct (Nat.ltb_spec a (length W)); [reflexivity | lia] | reflexivity].
Qed.

(** The suffix from a known position starts with its entry. *)
Lemma skipn_nth_error {A} (xs : list A) i x : nth_error xs i = Some x -> skipn i xs = x :: skipn (S i) xs.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] H; cbn in H |- *; try discriminate.
  - congruence.
  - apply IH, H.
Qed.

(** The prefix through a written position ends with the new entry. *)
Lemma firstn_lset_S {A} (xs : list A) j x : j < length xs -> firstn (S j) (lset xs j x) = firstn j xs ++ [x].
Proof.
  revert j. induction xs as [|a xs IH]; intros [|j] Hj; cbn in Hj; try lia.
  - reflexivity.
  - rewrite lset_consS. cbn [firstn app]. f_equal. apply IH. lia.
Qed.

(** A write before the cut leaves the suffix alone. *)
Lemma skipn_lset {A} (xs : list A) i j x : j < i -> skipn i (lset xs j x) = skipn i xs.
Proof.
  revert i j. induction xs as [|a xs IH]; intros i j Hji; [now rewrite lset_nil|].
  destruct i as [|i]; [lia|]. destruct j as [|j]; [reflexivity|].
  rewrite lset_consS. cbn [skipn]. apply IH. lia.
Qed.

(** A write at or after the cut leaves the prefix alone. *)
Lemma firstn_lset_lt {A} (xs : list A) n j x : n <= j -> firstn n (lset xs j x) = firstn n xs.
Proof.
  revert n j. induction xs as [|a xs IH]; intros n j Hn; [now rewrite lset_nil|].
  destruct n as [|n]; [reflexivity|]. destruct j as [|j]; [lia|].
  rewrite lset_consS. cbn [firstn]. f_equal. apply IH. lia.
Qed.

(** In-place compaction of a watch list: copying entry [i] down to slot [j <= i]
    advances both cursors and keeps the logical list [firstn j L ++ skipn i L]. *)
Lemma keep_step (L : list nat) i j x : j <= i -> nth_error L i = Some x ->
  firstn (S j) (lset L j x) ++ skipn (S i) (lset L j x) = firstn j L ++ skipn i L.
Proof.
  intros Hji Hx. assert (i < length L) by (apply nth_error_Some; congruence).
  rewrite firstn_lset_S by lia. rewrite skipn_lset by lia.
  rewrite (skipn_nth_error L i x Hx). now rewrite <- app_assoc.
Qed.

(** The second of two writes to one index wins. *)
Lemma lset_lset {A} (xs : list A) i x y : lset (lset xs i x) i y = lset xs i y.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i]; rewrite ?lset_nil, ?lset_cons0, ?lset_consS; auto.
  now rewrite IH.
Qed.

(** Writing back the current entry changes nothing. *)
Lemma lset_same {A} (xs : list A) i x : nth_error xs i = Some x -> lset xs i x = xs.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite lset_consS. now rewrite IH.
Qed.

(** [nth] agrees with a successful [nth_error]. *)
Lemma nth_of_error {A} (xs : list A) i x d : nth_error xs i = Some x -> nth i xs d = x.
Proof. intros H. now apply nth_error_nth. Qed.

(** Dropping entry [i] from the logical list removes one occurrence of it. *)
Lemma count_occ_keep L i j ci x : nth_error L i = Some x ->
  count_occ Nat.eq_dec (firstn j L ++ skipn i L) ci =
  count_occ Nat.eq_dec (firstn j L ++ skipn (S i) L) ci + (if Nat.eq_dec x ci then 1 else 0).
Proof.
  intros H. rewrite (skipn_nth_error L i x H), !count_occ_app. cbn [count_occ].
  destruct (Nat.eq_dec x ci); lia.
Qed.

(** Moving clause [ci] from [fl]'s watch list to [ck]'s, while rewriting it so
    that it watches [ck] instead of [fl], keeps [Wch]. *)
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
  assert (Ek : cnt W ck ci' = count_occ Nat.eq_dec Wck ci') by (unfold cnt; now rewrite (nth_of_error W ck Wck [] HWck)).
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

(** Rewriting a clause without changing what it watches keeps [Wch]. *)
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

(** Writing back the current clauses is the identity. *)
Lemma dset_id st : dset st (db st) = st.
Proof. now destruct st. Qed.

(** Writing back the current watch lists is the identity. *)
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

(** Pointwise falsity from [from] on is falsity of the suffix. *)
Lemma all_false_cl A cl from :
  (forall p, from <= p < length cl -> lval A (nth p cl 0) = 2) -> Forall (fun q => lval A q = 2) (skipn from cl).
Proof.
  intros H. apply Forall_forall. intros q Hq. apply In_nth with (d := 0) in Hq as (p & Hp & <-).
  rewrite length_skipn in Hp. rewrite nth_skipn. apply H. lia.
Qed.

(** The literal a clause propagates at level 0 holds under [val]. *)
Lemma unit_true val st ci cl first :
  Core val st -> nth_error (db st) ci = Some cl -> length (lim st) = 0 ->
  nth_error cl 0 = Some first ->
  (forall p, 1 <= p < length cl -> lval (asg st) (nth p cl 0) = 2) -> holds val first.
Proof.
  intros C Hd H0 Hf Hrest. destruct val as [v|]; [|exact I]. cbn [holds].
  pose proof (Forall_nth_error _ _ _ _ (i_db _ _ C) Hd) as Hex. cbn [cholds] in Hex.
  apply Exists_exists in Hex as (q & Hq & Ht).
  apply In_nth with (d := 0) in Hq as (p & Hp & <-).
  destruct p as [|p].
  - rewrite (nth_of_error cl 0 first 0 Hf) in Ht. exact Ht.
  - exfalso. assert (Hq : lval (asg st) (nth (S p) cl 0) = 2) by (apply Hrest; lia).
    apply (false_l0 v st C _ Hq); [|exact Ht].
    destruct (false_trail _ st C _ Hq) as (k & Hk).
    pose proof (level_le _ st C k _ Hk) as Hl. rewrite lvar_lneg in Hl. lia.
Qed.

(** [tl] is [skipn 1]. *)
Lemma tl_skipn1 {A} (xs : list A) : tl xs = skipn 1 xs.
Proof. now destruct xs. Qed.

(** Advancing the queue head within the trail, or writing the other counters, keeps [Core]. *)
Lemma core_fset_misc val st m :
  Core val st -> qhead st <= nth QHEAD m 0 <= length (tr st) -> Core val (fset st FMisc m).
Proof.
  intros C Hq. destruct C. constructor; cbn [fv fset fld_eqb db]; auto.
  - eapply Forall_impl; [|eassumption]. cbn. lia.
  - lia.
Qed.

(** The negation of a trail literal is false. *)
Lemma lneg_trail_false val st p : Core val st -> In p (tr st) -> lval (asg st) (lneg p) = 2.
Proof.
  intros C Hp. apply lval_neg_true; [rewrite lvar_lneg; apply (i_asg _ _ C)|].
  rewrite lneg_lneg. now apply (true_on_trail val st C).
Qed.

(** Extending a prefix by one position appends its entry. *)
Lemma firstn_S_snoc {A} (xs : list A) i x : nth_error xs i = Some x -> firstn (S i) xs = firstn i xs ++ [x].
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] H; cbn in H |- *; try discriminate.
  - congruence.
  - f_equal. now apply IH.
Qed.

(** A push lands in any suffix that starts within the list. *)
Lemma skipn_snoc {A} (xs : list A) m x : m <= length xs -> skipn m (xs ++ [x]) = skipn m xs ++ [x].
Proof. intros H. rewrite skipn_app. now replace (m - length xs) with 0 by lia. Qed.

(** * Counting marks over trail positions *)

(** Variable [u] is marked in [M], the [seen] vector during analysis. *)
Definition marked (M : list nat) (u : nat) : Prop := nth u M 0 <> 0.

(** The boolean test for [marked]. *)
Definition markedb (M : list nat) (u : nat) : bool := negb (Nat.eqb (nth u M 0) 0).

(** [markedb] reflects [marked]. *)
Lemma markedb_iff M u : markedb M u = true <-> marked M u.
Proof. unfold markedb, marked. destruct (Nat.eqb_spec (nth u M 0) 0); cbn; intuition congruence. Qed.

(** The number of trail positions from [lo] up to, not including, [hi] whose
    variable is marked. *)
Definition cntm (T M : list nat) (lo hi : nat) : nat :=
  length (filter (fun k => markedb M (lvar (nth k T 0))) (seq lo (hi - lo))).

(** Counts add over adjacent ranges. *)
Lemma cntm_split T M lo m hi : lo <= m <= hi -> cntm T M lo hi = cntm T M lo m + cntm T M m hi.
Proof.
  intros H. unfold cntm. replace (hi - lo) with ((m - lo) + (hi - m)) by lia.
  rewrite seq_app, filter_app, length_app. now replace (lo + (m - lo)) with m by lia.
Qed.

(** The count over a single position. *)
Lemma cntm_one T M k : cntm T M k (S k) = if markedb M (lvar (nth k T 0)) then 1 else 0.
Proof. unfold cntm. replace (S k - k) with 1 by lia. cbn. now destruct (markedb _ _). Qed.

(** An empty range counts 0. *)
Lemma cntm_empty T M lo hi : hi <= lo -> cntm T M lo hi = 0.
Proof. intros H. unfold cntm. now replace (hi - lo) with 0 by lia. Qed.

(** The count reads only the marks of the range's variables. *)
Lemma cntm_ext T M M' lo hi :
  (forall k, lo <= k < hi -> markedb M (lvar (nth k T 0)) = markedb M' (lvar (nth k T 0))) ->
  cntm T M lo hi = cntm T M' lo hi.
Proof.
  intros H. unfold cntm. f_equal. apply filter_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

(** More marks, larger counts. *)
Lemma cntm_mono T M M' lo hi : (forall u, marked M u -> marked M' u) -> cntm T M lo hi <= cntm T M' lo hi.
Proof.
  intros H. unfold cntm. generalize (seq lo (hi - lo)). induction l as [|k l IH]; cbn; [lia|].
  destruct (markedb M _) eqn:E1, (markedb M' _) eqn:E2; cbn; try lia.
  apply markedb_iff, H, markedb_iff in E1. congruence.
Qed.

(** A marked position in range counts. *)
Lemma cntm_pos T M lo hi k : lo <= k < hi -> marked M (lvar (nth k T 0)) -> 1 <= cntm T M lo hi.
Proof.
  intros Hk Hm. rewrite (cntm_split T M lo k hi) by lia. rewrite (cntm_split T M k (S k) hi) by lia.
  rewrite cntm_one. apply markedb_iff in Hm. rewrite Hm. lia.
Qed.

(** No marked position, count 0. *)
Lemma cntm_zero T M lo hi : (forall k, lo <= k < hi -> ~ marked M (lvar (nth k T 0))) -> cntm T M lo hi = 0.
Proof.
  intros H. unfold cntm.
  assert (Hl : forall k, In k (seq lo (hi - lo)) -> markedb M (lvar (nth k T 0)) = false).
  { intros k Hk. apply in_seq in Hk. destruct (markedb _ _) eqn:E; [|reflexivity].
    apply markedb_iff in E. exfalso. apply (H k); [lia | exact E]. }
  revert Hl. generalize (seq lo (hi - lo)). intros l Hl.
  induction l as [|k l IH]; cbn; [reflexivity|].
  rewrite (Hl k (or_introl eq_refl)). apply IH. intros; apply Hl; now right.
Qed.

(** Two marked positions in range count at least 2. *)
Lemma cntm_two T M lo hi k1 k2 : lo <= k1 -> k1 < k2 -> k2 < hi ->
  marked M (lvar (nth k1 T 0)) -> marked M (lvar (nth k2 T 0)) -> 2 <= cntm T M lo hi.
Proof.
  intros H1 H12 H2 M1 M2. rewrite (cntm_split T M lo k2 hi) by lia.
  pose proof (cntm_pos T M lo k2 k1 ltac:(lia) M1). pose proof (cntm_pos T M k2 hi k2 ltac:(lia) M2). lia.
Qed.

(** A nonzero count has a marked position in range. *)
Lemma cntm_exists T M lo hi : cntm T M lo hi <> 0 -> exists k, lo <= k < hi /\ marked M (lvar (nth k T 0)).
Proof.
  intros H. destruct (filter (fun k => markedb M (lvar (nth k T 0))) (seq lo (hi - lo))) as [|k l] eqn:E.
  - unfold cntm in H. rewrite E in H. contradiction.
  - assert (Hk : In k (filter (fun k => markedb M (lvar (nth k T 0))) (seq lo (hi - lo)))) by (rewrite E; now left).
    apply filter_In in Hk as [Hk Hm]. apply in_seq in Hk. exists k. split; [lia | now apply markedb_iff].
Qed.

(** Marks after a write to [u]'s entry. *)
Lemma marked_lset M v x u : v < length M ->
  marked (lset M v x) u <-> (if Nat.eqb v u then x <> 0 else marked M u).
Proof.
  intros Hv. unfold marked. rewrite nth_lset. destruct (Nat.eqb v u); [|tauto].
  destruct (Nat.ltb_spec v (length M)); [tauto | lia].
Qed.

(** A write to another variable's mark keeps [u]'s. *)
Lemma markedb_lset_neq M v x u : v <> u -> markedb (lset M v x) u = markedb M u.
Proof. intros. unfold markedb. rewrite nth_lset. destruct (Nat.eqb_spec v u); [congruence | reflexivity]. Qed.

(** [at_pos] in terms of [nth]. *)
Lemma at_pos_nth T k u : at_pos T k u <-> k < length T /\ lvar (nth k T 0) = u.
Proof.
  split.
  - intros (l & Hl & E). split; [apply nth_error_Some; congruence|]. now rewrite (nth_of_error T k l 0 Hl).
  - intros [Hk E]. exists (nth k T 0). split; [now apply nth_error_nth' | exact E].
Qed.

(** * First-UIP analysis *)

(** The trail position of the current level's decision. *)
Definition base (st : astate) : nat := nth (length (lim st) - 1) (lim st) 0.

(** Every decision position is at most the last one. *)
Lemma le_base L x : sorted L -> In x L -> x <= nth (length L - 1) L 0.
Proof.
  intros Hs Hx. apply In_nth with (d := 0) in Hx as (i & Hi & <-).
  destruct (Nat.eq_dec i (length L - 1)) as [-> | Hne]; [lia|]. apply Hs. lia.
Qed.

(** With a decision, the last one is in the list. *)
Lemma base_in L : L <> [] -> In (nth (length L - 1) L 0) L.
Proof. intros H. apply nth_In. destruct L; [congruence | cbn; lia]. Qed.

(** The analysis state: the marks [M], the learnt literals [tl Lr], the
    trail position [index] the next marked literal is looked for at or below,
    and [pathC], the number of marked literals at the current level. *)
Record AInv (st : astate) (M Lr : list nat) (index pathC : nat) : Prop := {
  (** Marked variables are on the trail above level 0. *)
  a_mark : forall u, marked M u -> exists k, at_pos (tr st) k u /\ 0 < count_le (lim st) k;
  (** [Lr] keeps its head slot, reserved for the asserting literal. *)
  a_lr_ne : Lr <> [];
  (** Learnt literals are false, marked, and from levels strictly between 0 and the current one. *)
  a_lr : Forall (fun q => lval (asg st) q = 2 /\ marked M (lvar q) /\
                           0 < nth (lvar q) (lvl st) 0 < length (lim st)) (tl Lr);
  (** Every marked variable below the current level is learnt. *)
  a_low : forall u k, marked M u -> at_pos (tr st) k u -> count_le (lim st) k < length (lim st) ->
            exists q, In q (tl Lr) /\ lvar q = u;
  (** Marked current-level positions are at or below [index]. *)
  a_cur : forall k, base st <= k < length (tr st) -> marked M (lvar (nth k (tr st) 0)) -> k <= index;
  (** [pathC] counts the marked current-level positions up to [index]. *)
  a_cnt : pathC = cntm (tr st) M (base st) (S index);
  (** [index] is a trail position. *)
  a_idx : index < length (tr st);
  (** No variable is learnt twice: the learnt clause fits in [nv + 1] slots. *)
  a_nd : NoDup (map lvar (tl Lr))
}.

(** Analysis runs on a state satisfying [Core] with at least one decision. *)
Section Analysis.
Variables (val : option (nat -> bool)) (st : astate).
Hypothesis C : Core val st.
Hypothesis Hne : lim st <> [].

(** A position is at the current level iff it is at or after [base]. *)
Lemma cur_iff k : count_le (lim st) k = length (lim st) <-> base st <= k.
Proof. apply count_le_cur; [apply (i_sorted _ _ C) | exact Hne]. Qed.

(** A variable's level is that of its trail position. *)
Lemma lvl_at k u : at_pos (tr st) k u -> nth u (lvl st) 0 = count_le (lim st) k.
Proof. intros (l & Hl & <-). apply (i_lvl _ _ C k l Hl). Qed.

(** A trail variable has one position. *)
Lemma pos_unique k k' u : at_pos (tr st) k u -> at_pos (tr st) k' u -> k = k'.
Proof. apply at_pos_unique, (i_nd _ _ C). Qed.

(** Every trail position is the position of its own variable. *)
Lemma at_pos_self k : k < length (tr st) -> at_pos (tr st) k (lvar (nth k (tr st) 0)).
Proof. intros Hk. exists (nth k (tr st) 0). split; [now apply nth_error_nth' | reflexivity]. Qed.

(** Marking [u] keeps the existing marks. *)
Lemma marked_mono1 M u w : u < length M -> marked M w -> marked (lset M u 1) w.
Proof. intros Hu Hw. apply marked_lset; [exact Hu|]. destruct (Nat.eqb u w); auto. Qed.

(** The analysis starts with no marks, no learnt literals, [pathC = 0], and
    [index] at the end of the trail. *)
Lemma ainv_init M : tr st <> [] -> (forall u, nth u M 0 = 0) -> AInv st M [0] (length (tr st) - 1) 0.
Proof.
  intros Ht HM. assert (Hm : forall u, ~ marked M u) by (intros u; unfold marked; rewrite HM; lia).
  constructor.
  - intros u H. now apply Hm in H.
  - discriminate.
  - constructor.
  - intros u k H. now apply Hm in H.
  - intros k _ H. now apply Hm in H.
  - symmetry. apply cntm_zero. intros k _. apply Hm.
  - destruct (tr st); [congruence | cbn; lia].
  - constructor.
Qed.

(** Outside [u]'s own position, writing [u]'s mark changes no count. *)
Lemma cntm_lset_out M u x k lo hi : at_pos (tr st) k u -> (k < lo \/ hi <= k) -> hi <= length (tr st) ->
  cntm (tr st) (lset M u x) lo hi = cntm (tr st) M lo hi.
Proof.
  intros Hk Hout Hhi. apply cntm_ext. intros k' Hk'.
  apply markedb_lset_neq. intros E. assert (Hk2 := at_pos_self k' ltac:(lia)). rewrite <- E in Hk2.
  pose proof (pos_unique _ _ _ Hk Hk2). lia.
Qed.

(** At [u]'s own position, the count changes with [u]'s mark. *)
Lemma cntm_lset_at M u x k lo hi : at_pos (tr st) k u -> lo <= k < hi -> hi <= length (tr st) ->
  cntm (tr st) (lset M u x) lo hi + (if markedb M u then 1 else 0) =
  cntm (tr st) M lo hi + (if markedb (lset M u x) u then 1 else 0).
Proof.
  intros Hk Hr Hhi.
  rewrite (cntm_split _ (lset M u x) lo k hi), (cntm_split _ (lset M u x) k (S k) hi) by lia.
  rewrite (cntm_split _ M lo k hi), (cntm_split _ M k (S k) hi) by lia.
  rewrite !(cntm_lset_out M u x k lo k), !(cntm_lset_out M u x k (S k) hi) by (auto; lia).
  rewrite !cntm_one. destruct Hk as (l & Hl & El). rewrite (nth_of_error _ k l 0 Hl), El.
  destruct (markedb M u), (markedb (lset M u x) u); lia.
Qed.

(** Marking an unmarked current-level variable at or below [index] adds one to [pathC]. *)
Lemma ainv_mark_cur M Lr index pathC k u :
  AInv st M Lr index pathC -> at_pos (tr st) k u -> k <= index -> base st <= k -> ~ marked M u ->
  u < length M -> AInv st (lset M u 1) Lr index (S pathC).
Proof.
  intros A Hk Hki Hbk Hu Hlen. destruct A as [Am Ane Alr Alow Acur Acnt Aidx And].
  assert (Hcur : count_le (lim st) k = length (lim st)) by (now apply cur_iff).
  assert (HD : 0 < length (lim st)) by (destruct (lim st); [congruence | cbn; lia]).
  constructor.
  - intros w Hw. apply marked_lset in Hw; [|exact Hlen]. destruct (Nat.eqb_spec u w) as [E | _]; [subst w|].
    + exists k. split; [exact Hk | lia].
    + now apply Am.
  - exact Ane.
  - eapply Forall_impl; [|exact Alr]. intros q (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
    now apply marked_mono1.
  - intros w k' Hw Hk' Hlt. apply marked_lset in Hw; [|exact Hlen]. destruct (Nat.eqb_spec u w) as [E | _]; [subst w|].
    + rewrite (pos_unique _ _ _ Hk' Hk) in Hlt. lia.
    + eapply Alow; eauto.
  - intros k' Hk' Hm. apply marked_lset in Hm; [|exact Hlen].
    destruct (Nat.eqb_spec u (lvar (nth k' (tr st) 0))) as [E | _].
    + assert (Hk2 := at_pos_self k' ltac:(lia)). rewrite <- E in Hk2.
      rewrite (pos_unique _ _ _ Hk2 Hk). exact Hki.
    + now apply Acur.
  - pose proof (cntm_lset_at M u 1 k (base st) (S index) Hk ltac:(lia) ltac:(lia)) as E.
    assert (markedb M u = false) as E1 by (destruct (markedb M u) eqn:X; [apply markedb_iff in X; contradiction | reflexivity]).
    assert (markedb (lset M u 1) u = true) as E2 by (apply markedb_iff, marked_lset; [exact Hlen | rewrite Nat.eqb_refl; lia]).
    rewrite E1, E2 in E. lia.
  - exact Aidx.
  - exact And.
Qed.

(** Marking an unmarked false variable from a level strictly between 0 and
    the current one learns it; [pathC] is unchanged. *)
Lemma ainv_mark_low M Lr index pathC k q :
  AInv st M Lr index pathC -> at_pos (tr st) k (lvar q) -> count_le (lim st) k < length (lim st) ->
  0 < count_le (lim st) k -> lval (asg st) q = 2 -> ~ marked M (lvar q) -> lvar q < length M ->
  AInv st (lset M (lvar q) 1) (Lr ++ [q]) index pathC.
Proof.
  intros A Hk Hlow Hpos Hq Hu Hlen. destruct A as [Am Ane Alr Alow Acur Acnt Aidx And].
  assert (Hbk : k < base st) by (destruct (Nat.ltb_spec k (base st)); [lia|]; apply cur_iff in H; lia).
  assert (Htl : tl (Lr ++ [q]) = tl Lr ++ [q]) by (destruct Lr; [congruence | reflexivity]).
  constructor.
  - intros w Hw. apply marked_lset in Hw; [|exact Hlen]. destruct (Nat.eqb_spec (lvar q) w) as [E | _]; [subst w|].
    + exists k. auto.
    + now apply Am.
  - destruct Lr; discriminate.
  - rewrite Htl. apply Forall_app. split.
    + eapply Forall_impl; [|exact Alr]. intros q' (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
      now apply marked_mono1.
    + constructor; [|constructor]. split; [exact Hq|]. split.
      * apply marked_lset; [exact Hlen|]. rewrite Nat.eqb_refl. lia.
      * rewrite (lvl_at _ _ Hk). lia.
  - intros w k' Hw Hk' Hlt. rewrite Htl. apply marked_lset in Hw; [|exact Hlen].
    destruct (Nat.eqb_spec (lvar q) w) as [E | _]; [subst w|].
    + exists q. split; [apply in_or_app; right; now left | reflexivity].
    + destruct (Alow w k' Hw Hk' Hlt) as (q' & Hq' & E). exists q'. split; [apply in_or_app; now left | exact E].
  - intros k' Hk' Hm. apply marked_lset in Hm; [|exact Hlen].
    destruct (Nat.eqb_spec (lvar q) (lvar (nth k' (tr st) 0))) as [E | _].
    + exfalso. assert (Hk2 := at_pos_self k' ltac:(lia)). rewrite <- E in Hk2.
      pose proof (pos_unique _ _ _ Hk Hk2). lia.
    + now apply Acur.
  - rewrite Acnt. symmetry. apply (cntm_lset_out M (lvar q) 1 k); auto; lia.
  - exact Aidx.
  - rewrite Htl, map_app. apply nodup_snoc'; [exact And|]. intros Hi.
    apply in_map_iff in Hi as (q' & E & Hq'). rewrite Forall_forall in Alr.
    destruct (Alr q' Hq') as (_ & Hm & _). rewrite E in Hm. contradiction.
Qed.

(** Popping the marked literal at [idx], when more remain at the current level. *)
Lemma ainv_pop M Lr index pathC idx :
  AInv st M Lr index pathC -> base st <= idx <= index ->
  marked M (lvar (nth idx (tr st) 0)) ->
  (forall k, idx < k <= index -> ~ marked M (lvar (nth k (tr st) 0))) ->
  2 <= pathC -> lvar (nth idx (tr st) 0) < length M ->
  base st < idx /\ AInv st (lset M (lvar (nth idx (tr st) 0)) 0) Lr (idx - 1) (pathC - 1).
Proof.
  intros A Hidx Hm Hnone H2 Hlen. pose proof A as [Am Ane Alr Alow Acur Acnt Aidx And].
  set (v := lvar (nth idx (tr st) 0)) in *.
  assert (Hv : at_pos (tr st) idx v) by (apply at_pos_self; lia).
  assert (Hvl : nth v (lvl st) 0 = length (lim st)) by (rewrite (lvl_at _ _ Hv); now apply cur_iff).
  assert (E1 : cntm (tr st) M (S idx) (S index) = 0).
  { apply cntm_zero. intros k Hk. apply Hnone. lia. }
  assert (E2 : cntm (tr st) M (base st) (S idx) = cntm (tr st) M (base st) idx + 1).
  { rewrite (cntm_split _ _ (base st) idx (S idx)), cntm_one by lia. fold v.
    apply markedb_iff in Hm. now rewrite Hm. }
  assert (E3 : pathC = cntm (tr st) M (base st) idx + 1).
  { rewrite Acnt, (cntm_split _ _ (base st) (S idx) (S index)) by lia. lia. }
  assert (Hb : base st < idx).
  { destruct (cntm_exists (tr st) M (base st) idx ltac:(lia)) as (k & Hk & _). lia. }
  split; [exact Hb|].
  assert (Hmv : forall w, marked (lset M v 0) w <-> w <> v /\ marked M w).
  { intros w. rewrite marked_lset by exact Hlen. destruct (Nat.eqb_spec v w); intuition. }
  constructor.
  - intros w Hw. apply Hmv in Hw as [_ Hw]. now apply Am.
  - exact Ane.
  - eapply Forall_impl; [|exact Alr]. intros q (H1' & H2' & H3'). split; [exact H1'|]. split; [|exact H3'].
    apply Hmv. split; [|exact H2']. intros E. rewrite E, Hvl in H3'. lia.
  - intros w k Hw Hk Hlt. apply Hmv in Hw as [_ Hw]. eapply Alow; eauto.
  - intros k Hk Hmk. apply Hmv in Hmk as [Hne' Hmk].
    pose proof (Acur k Hk Hmk). destruct (Nat.ltb_spec idx k) as [Hlt | Hge].
    + exfalso. eapply Hnone; [|exact Hmk]. lia.
    + destruct (Nat.eq_dec k idx) as [-> | ?]; [contradiction | lia].
  - replace (S (idx - 1)) with idx by lia. rewrite (cntm_lset_out M v 0 idx) by (auto; lia). lia.
  - lia.
  - exact And.
Qed.

(** Popping the last marked literal at the current level, the first UIP: every
    variable still marked is learnt. *)
Lemma ainv_final M Lr index pathC idx :
  AInv st M Lr index pathC -> base st <= idx <= index ->
  marked M (lvar (nth idx (tr st) 0)) ->
  (forall k, idx < k <= index -> ~ marked M (lvar (nth k (tr st) 0))) ->
  pathC <= 1 -> lvar (nth idx (tr st) 0) < length M ->
  forall w, marked (lset M (lvar (nth idx (tr st) 0)) 0) w -> exists q, In q (tl Lr) /\ lvar q = w.
Proof.
  intros A Hidx Hm Hnone H1 Hlen w Hw. pose proof A as [Am Ane Alr Alow Acur Acnt Aidx And].
  set (v := lvar (nth idx (tr st) 0)) in *.
  apply marked_lset in Hw; [|exact Hlen]. destruct (Nat.eqb_spec v w) as [E | Hne']; [lia|].
  destruct (Am w Hw) as (k & Hk & Hpos).
  destruct (Nat.ltb_spec (count_le (lim st) k) (length (lim st))) as [Hlow | Hhi].
  - eapply Alow; eauto.
  - exfalso. pose proof (count_le_max (lim st) k).
    assert (Hbk : base st <= k) by (apply cur_iff; lia).
    assert (Hkt : k < length (tr st)) by (eapply at_pos_lt; eauto).
    destruct Hk as (l & Hl & El).
    assert (Hmk : marked M (lvar (nth k (tr st) 0))) by (rewrite (nth_of_error _ k l 0 Hl), El; exact Hw).
    pose proof (Acur k ltac:(lia) Hmk) as Hki.
    destruct (Nat.ltb_spec idx k) as [Hlt | Hge]; [eapply Hnone; [|exact Hmk]; lia|].
    destruct (Nat.eq_dec k idx) as [-> | Hne2].
    + apply Hne'. unfold v. rewrite (nth_of_error _ idx l 0 Hl). exact El.
    + pose proof (cntm_two (tr st) M (base st) (S index) k idx ltac:(lia) ltac:(lia) ltac:(lia) Hmk Hm). lia.
Qed.

(** A literal after the last decision has a reason, so analysis can resolve on it. *)
Lemma reason_exists idx : base st < idx -> idx < length (tr st) ->
  nth (lvar (nth idx (tr st) 0)) (rsn st) 0 <> 0.
Proof.
  intros Hb Hidx H0. pose proof (base_in (lim st) Hne) as Hin.
  destruct (i_dec _ _ C idx (nth idx (tr st) 0) (nth_error_nth' _ _ Hidx) H0) as [F | Hi].
  - rewrite Forall_forall in F. specialize (F _ Hin). unfold base in Hb. lia.
  - pose proof (le_base (lim st) idx (i_sorted _ _ C) Hi). unfold base in Hb. lia.
Qed.

(** A current-level literal's variable is not learnt: the learnt literals
    are from lower levels. *)
Lemma uip_fresh M Lr index pathC idx :
  AInv st M Lr index pathC -> base st <= idx < length (tr st) ->
  ~ In (lvar (nth idx (tr st) 0)) (map lvar (tl Lr)).
Proof.
  intros A Hidx Hi. apply in_map_iff in Hi as (q & E & Hq).
  destruct (proj1 (Forall_forall _ _) (a_lr _ _ _ _ _ A) q Hq) as (_ & _ & Hl).
  rewrite E, (lvl_at idx) in Hl by (now apply at_pos_self).
  assert (Hc : count_le (lim st) idx = length (lim st)) by (apply cur_iff; lia). lia.
Qed.

(** So the learnt clause, with the asserting literal [lneg p] in front, has
    distinct variables. *)
Lemma learnt_nodup M Lr index pathC idx :
  AInv st M Lr index pathC -> base st <= idx < length (tr st) ->
  NoDup (map lvar (lneg (nth idx (tr st) 0) :: tl Lr)).
Proof.
  intros A Hidx. cbn [map]. constructor; [|exact (a_nd _ _ _ _ _ A)].
  rewrite lvar_lneg. eapply uip_fresh; eauto.
Qed.

End Analysis.

(** Positions from 1 on are in the tail. *)
Lemma in_tl_nth (L : list nat) p : 1 <= p < length L -> In (nth p L 0) (tl L).
Proof.
  intros H. destruct L as [|a L]; cbn in H; [lia|]. cbn [tl]. destruct p as [|p]; [lia|]. cbn [nth].
  apply nth_In. lia.
Qed.

(** A suffix member has a position at or after the cut. *)
Lemma in_skipn_nth (L : list nat) start q : In q (skipn start L) -> exists p, start <= p < length L /\ nth p L 0 = q.
Proof.
  intros H. apply In_nth with (d := 0) in H as (p & Hp & <-). rewrite length_skipn in Hp.
  exists (start + p). split; [lia|]. now rewrite nth_skipn.
Qed.

(** Appending a clause, not yet in any watch list, keeps [Wch]. *)
Lemma wch_snoc D W cl : Wch D W -> Wch (D ++ [cl]) W.
Proof.
  intros H ci l Hl. specialize (H ci l Hl). unfold expect in *.
  destruct (Nat.ltb_spec ci (length D)).
  - now rewrite nth_error_app1.
  - rewrite (proj2 (nth_error_None D ci)) in H by lia. lia.
Qed.

(** The next clause index occurs in no watch list yet. *)
Lemma wch_fresh D W l : Wch D W -> l < length W -> cnt W l (length D) = 0.
Proof.
  intros H Hl. specialize (H (length D) l Hl). unfold expect in H.
  rewrite (proj2 (nth_error_None D (length D))) in H by lia. lia.
Qed.

(** Adding [ci] to [a]'s watch list keeps [Wch] while the bound has room. *)
Lemma wch_push D W a Wa ci : Wch D W -> nth_error W a = Some Wa -> cnt W a ci + 1 <= expect D ci a ->
  Wch D (lset W a (Wa ++ [ci])).
Proof.
  intros H Ha Hle ci' l Hl. rewrite lset_length in Hl.
  assert (Hal : a < length W) by (apply nth_error_Some; congruence).
  rewrite cnt_lset by exact Hal. destruct (Nat.eqb_spec a l) as [<- | Hne]; [|now apply H].
  unfold cnt in Hle. rewrite (nth_of_error W a Wa [] Ha) in Hle.
  rewrite count_occ_app. cbn [count_occ]. destruct (Nat.eq_dec ci ci') as [<- | Hne'].
  - lia.
  - pose proof (H ci' a Hal) as H'. unfold cnt in H'. rewrite (nth_of_error W a Wa [] Ha) in H'. lia.
Qed.

(** A decision, taken with an empty queue, opens a new level at the end of the
    trail and keeps [Core]. *)
Lemma core_decide val st :
  Core val st -> qhead st = length (tr st) -> Core val (fset st FLim (lim st ++ [length (tr st)])).
Proof.
  intros C Hq. pose proof (i_limq _ _ C) as F. rewrite Hq in F.
  destruct C. constructor; cbn [fv fset fld_eqb db]; auto.
  - intros k l Hk. rewrite count_le_snoc. assert (k < length (tr st)) by (apply nth_error_Some; congruence).
    destruct (Nat.leb_spec (length (tr st)) k); [lia|]. rewrite Nat.add_0_r. eauto.
  - now apply sorted_snoc.
  - rewrite Hq. apply Forall_app. split; [exact F | constructor; auto].
  - intros k l Hk Hr. assert (k < length (tr st)) by (apply nth_error_Some; congruence).
    destruct (i_dec0 k l Hk Hr) as [G | G].
    + left. apply Forall_app. split; [exact G | constructor; [lia | constructor]].
    + right. apply in_or_app. now left.
Qed.

(** Writing a counter other than the queue head keeps [Inv]. *)
Lemma inv_misc_other val st i x : i <> QHEAD -> Inv val st -> Inv val (fset st FMisc (lset (fv st FMisc) i x)).
Proof.
  intros Hi (C & W & S0). split; [|split; [exact W | exact S0]].
  apply core_fset_misc; [exact C|]. unfold QHEAD in *. rewrite nth_lset.
  destruct (Nat.eqb_spec i 0); [lia|]. split; [lia | apply (i_qtr _ _ C)].
Qed.

(** [lit_of v a] is a literal on [v]. *)
Lemma lvar_lit_of v a : lvar (lit_of v a) = v.
Proof. unfold lit_of. destruct (Nat.eqb a 1); [apply lvar_2v | apply lvar_2v1]. Qed.

(** Forgetting the valuation keeps [Core]: [Core None] is its structural part. *)
Lemma core_forget val st : Core val st -> Core None st.
Proof. intros []. constructor; cbn; auto. apply Forall_forall. intros. exact I. Qed.

(** Forgetting the valuation keeps [Inv]. *)
Lemma inv_forget val st : Inv val st -> Inv None st.
Proof. intros (C & W & S0). split; [eapply core_forget; eauto | auto]. Qed.

(** * The safety invariant *)

(** A successful read was in bounds. *)
Lemma nth_error_lt' {A} (xs : list A) i x : nth_error xs i = Some x -> i < length xs.
Proof. intros H. apply nth_error_Some. congruence. Qed.

(** Prefixes keep [Forall]. *)
Lemma Forall_firstn' {A} (P : A -> Prop) n xs : Forall P xs -> Forall P (firstn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. now apply Forall_app in H as [H _]. Qed.

(** Suffixes keep [Forall]. *)
Lemma Forall_skipn' {A} (P : A -> Prop) n xs : Forall P xs -> Forall P (skipn n xs).
Proof. intros H. rewrite <- (firstn_skipn n xs) in H. now apply Forall_app in H as [_ H]. Qed.

(** A literal below [2 * nv] has its variable below [nv]. *)
Lemma lvar_lt l nv : l < 2 * nv -> lvar l < nv.
Proof. intros H. unfold lvar. apply Nat.Div0.div_lt_upper_bound. lia. Qed.

(** A literal whose variable is below [nv] is below [2 * nv]. *)
Lemma lvar_lt_inv l nv : lvar l < nv -> l < 2 * nv.
Proof. intros H. destruct (lit_cases l) as [[E _] | [E _]]; lia. Qed.

(** Negation keeps a literal below [2 * nv]. *)
Lemma lneg_lt l nv : l < 2 * nv -> lneg l < 2 * nv.
Proof. intros H. apply lvar_lt_inv. rewrite lvar_lneg. now apply lvar_lt. Qed.

(** A literal built from a variable below [nv] is below [2 * nv]. *)
Lemma lit_of_lt v a nv : v < nv -> lit_of v a < 2 * nv.
Proof. intros H. unfold lit_of. destruct (Nat.eqb a 1); lia. Qed.

(** A list of distinct naturals below [n] has at most [n] entries. *)
Lemma nodup_bound xs n : NoDup xs -> Forall (fun x => x < n) xs -> length xs <= n.
Proof.
  intros Hn F. rewrite <- (length_seq n 0). apply NoDup_incl_length; [exact Hn|].
  intros x Hx. apply in_seq. rewrite Forall_forall in F. specialize (F x Hx). lia.
Qed.

(** A watch entry names a clause of length at least 2. *)
Definition wok (D : list (list nat)) (ci : nat) : Prop :=
  exists cl, nth_error D ci = Some cl /\ 2 <= length cl.

(** [l] is strictly increasing. *)
Definition incr (l : list nat) : Prop :=
  forall i j a b, i < j -> nth_error l i = Some a -> nth_error l j = Some b -> a < b.

(** A strictly increasing list has no duplicates. *)
Lemma incr_nodup l : incr l -> NoDup l.
Proof.
  intros H. apply NoDup_nth_error. intros i j Hi E.
  destruct (nth_error l i) as [a|] eqn:Ea; [|apply nth_error_None in Ea; lia].
  destruct (Nat.lt_total i j) as [Hij | [Hij | Hij]]; auto.
  - pose proof (H i j a a Hij Ea (eq_sym E)). lia.
  - pose proof (H j i a a Hij (eq_sym E) Ea). lia.
Qed.

(** Prefixes of an increasing list are increasing. *)
Lemma incr_firstn n l : incr l -> incr (firstn n l).
Proof.
  intros H i j a b Hij Ha Hb. rewrite nth_error_firstn in Ha, Hb.
  destruct (Nat.ltb i n), (Nat.ltb j n); try discriminate. eauto.
Qed.

(** Appending a value above every element keeps a list increasing. *)
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

(** Every entry of an increasing list after index [i] exceeds entry [i]. *)
Lemma incr_firstn_lt l n : incr l -> n < length l -> Forall (fun x => x < nth n l 0) (firstn n l).
Proof.
  intros H Hn. apply Forall_forall. intros x Hx. apply in_firstn_pos in Hx as (k & Hk & Ek).
  eapply (H k n); [exact Hk | exact Ek | now apply nth_error_nth'].
Qed.

(** Compute the field reads and updates of the abstract state. *)
Ltac fvs := cbn [fv fset dset wset cpush fld_eqb db wl enq] in *.

Section Safe.
(** [nv] is the number of variables, so literals are below [2 * nv]. *)
Variable nv : nat.

(** A literal over the [nv] variables. *)
Definition lit_ok (l : nat) : Prop := l < 2 * nv.

(** [lit_ok] bounds the variable. *)
Lemma lit_ok_var l : lit_ok l <-> lvar l < nv.
Proof. unfold lit_ok. split; [apply lvar_lt | apply lvar_lt_inv]. Qed.

(** [lit_ok] is closed under negation. *)
Lemma lit_ok_lneg l : lit_ok (lneg l) <-> lit_ok l.
Proof. rewrite !lit_ok_var, lvar_lneg. reflexivity. Qed.

(** [SI] without [lim_lt]: a decision pushes the trail's length onto
    [trail_lim] one event before it enqueues. *)
Record SIc (st : astate) : Prop := {
  si_asg : length (asg st) = nv;
  si_lvl : length (lvl st) = nv;
  si_rsn : length (rsn st) = nv;
  si_ph : length (fv st FPh) = nv;
  si_st : length (fv st FSt) = nv;
  si_sn : length (sn st) = nv;
  si_misc : length (fv st FMisc) = NMISC;
  (** A watch list per literal. *)
  si_wl : length (wl st) = 2 * nv;
  si_db : Forall (Forall lit_ok) (db st);
  si_tr : Forall lit_ok (tr st);
  (** Watch entries index clauses that have two literals to watch. *)
  si_w : Forall (Forall (wok (db st))) (wl st);
  (** A reason is 0 (none) or a clause index plus one. *)
  si_r : Forall (fun r => r <= length (db st)) (rsn st);
  si_inc : incr (lim st)
}.

(** Every decision's trail position is on the trail. *)
Definition lim_lt (st : astate) : Prop := Forall (fun x => x < length (tr st)) (lim st).

(** The safety invariant. *)
Definition SI (st : astate) : Prop := SIc st /\ lim_lt st.

(** A field constrained only by its length may be replaced by any list of
    that length. *)
Lemma sic_free st f xs :
  SIc st -> f = FAsg \/ f = FLvl \/ f = FPh \/ f = FSt \/ f = FSn \/ f = FMisc ->
  length xs = length (fv st f) -> SIc (fset st f xs).
Proof.
  intros [] Hf Hl. destruct Hf as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    constructor; fvs; auto; lia.
Qed.

(** In particular, one cell of such a field may be written. *)
Lemma sic_lset st f i x :
  SIc st -> f = FAsg \/ f = FLvl \/ f = FPh \/ f = FSt \/ f = FSn \/ f = FMisc ->
  SIc (fset st f (lset (fv st f) i x)).
Proof. intros H Hf. apply sic_free; auto. apply lset_length. Qed.

(** [SIc] does not constrain the learnt clause. *)
Lemma sic_lrn st xs : SIc st -> SIc (fset st FLrn xs).
Proof. intros []. constructor; fvs; auto. Qed.

(** Nor does [SI]. *)
Lemma si_lrn st xs : SI st -> SI (fset st FLrn xs).
Proof. intros [Hs Hl]. split; [now apply sic_lrn | exact Hl]. Qed.

(** A reason may be set to anything up to the number of clauses. *)
Lemma sic_rsn st i r : SIc st -> r <= length (db st) -> SIc (fset st FRsn (lset (rsn st) i r)).
Proof.
  intros [] Hr. constructor; fvs; auto.
  - now rewrite lset_length.
  - now apply Forall_lset.
Qed.

(** Any trail of valid literals. *)
Lemma sic_tr st xs : SIc st -> Forall lit_ok xs -> SIc (fset st FTr xs).
Proof. intros [] Hx. constructor; fvs; auto. Qed.

(** Any strictly increasing [trail_lim]. *)
Lemma sic_lim st xs : SIc st -> incr xs -> SIc (fset st FLim xs).
Proof. intros [] Hx. constructor; fvs; auto. Qed.

(** Replacing a clause by one of the same length keeps watch entries valid. *)
Lemma wok_lset D k cl cl' ci :
  nth_error D k = Some cl -> length cl' = length cl -> wok D ci -> wok (lset D k cl') ci.
Proof.
  intros Hk Hl (c & Hc & H2). destruct (Nat.eqb_spec k ci) as [<- | Hne].
  - rewrite Hk in Hc. injection Hc as <-. exists cl'. split; [| lia].
    apply nth_error_lset_eq, (nth_error_lt' _ _ _ Hk).
  - exists c. split; [| exact H2]. rewrite nth_error_lset_neq; auto.
Qed.

(** Rewriting a clause in place, with its length kept and valid literals. *)
Lemma sic_dset st k cl cl' :
  SIc st -> nth_error (db st) k = Some cl -> length cl' = length cl -> Forall lit_ok cl' ->
  SIc (dset st (lset (db st) k cl')).
Proof.
  intros [] Hk Hl Hc. constructor; fvs; auto.
  - now apply Forall_lset.
  - eapply Forall_impl; [| exact si_w0]. intros L. apply Forall_impl. intros ci. now apply wok_lset with (cl := cl).
  - now rewrite lset_length.
Qed.

(** Replacing the watch lists by [2 * nv] lists of valid entries. *)
Lemma sic_wset st W : SIc st -> length W = 2 * nv -> Forall (Forall (wok (db st))) W -> SIc (wset st W).
Proof. intros [] Hl Hw. constructor; fvs; auto. Qed.

(** Appending a clause keeps watch entries valid. *)
Lemma wok_app D cl ci : wok D ci -> wok (D ++ [cl]) ci.
Proof. intros (c & Hc & H2). exists c. split; [| exact H2]. rewrite nth_error_app1; [exact Hc | eapply nth_error_lt'; eauto]. Qed.

(** Adding a clause of valid literals. *)
Lemma sic_cpush st cl : SIc st -> Forall lit_ok cl -> SIc (cpush st cl).
Proof.
  intros [] Hc. constructor; fvs; auto.
  - apply Forall_app; auto.
  - eapply Forall_impl; [| exact si_w0]. intros L. apply Forall_impl. intros ci. apply wok_app.
  - eapply Forall_impl; [| exact si_r0]. intros r Hr. rewrite length_app. cbn [length] in *. lia.
Qed.

(** [sic_cpush] for [SI]: the trail and decisions are untouched. *)
Lemma si_cpush st cl : SI st -> Forall lit_ok cl -> SI (cpush st cl).
Proof. intros [Hs Hl] Hc. split; [now apply sic_cpush | exact Hl]. Qed.

(** A watch list may get any entries naming long enough clauses. *)
Lemma sic_wl_lset st k L : SIc st -> Forall (wok (db st)) L -> SIc (wset st (lset (wl st) k L)).
Proof.
  intros H HL. apply sic_wset; [exact H | rewrite lset_length; apply (si_wl _ H) |].
  apply Forall_lset; [apply (si_w _ H) | exact HL].
Qed.

(** [lim_lt] survives growing the trail. *)
Lemma lim_lt_grow st st' : lim st' = lim st -> length (tr st) <= length (tr st') -> lim_lt st -> lim_lt st'.
Proof. intros E Hl H. unfold lim_lt in *. rewrite E. revert H. apply Forall_impl. intros x Hx. lia. Qed.

(** Every entry of a watch list is valid. *)
Lemma wl_ok st fl L : SIc st -> nth_error (wl st) fl = Some L -> Forall (wok (db st)) L.
Proof. intros Hs HL. eapply Forall_nth_error; [apply (si_w _ Hs) | exact HL]. Qed.

(** [sic_wl_lset] for [SI]. *)
Lemma si_wl_lset st k L : SI st -> Forall (wok (db st)) L -> SI (wset st (lset (wl st) k L)).
Proof. intros [Hs Hl] HL. split; [now apply sic_wl_lset | exact Hl]. Qed.

(** [sic_dset] for [SI]. *)
Lemma si_dset st k cl cl' :
  SI st -> nth_error (db st) k = Some cl -> length cl' = length cl -> Forall lit_ok cl' ->
  SI (dset st (lset (db st) k cl')).
Proof. intros [Hs Hl] Hk Hc HL. split; [eapply sic_dset; eauto | exact Hl]. Qed.

(** Literals read from the database are valid. *)
Lemma db_lit st k cl j l : SIc st -> nth_error (db st) k = Some cl -> nth_error cl j = Some l -> lit_ok l.
Proof.
  intros Hs Hk Hj. eapply Forall_nth_error; [| exact Hj].
  eapply Forall_nth_error; [apply (si_db _ Hs) | exact Hk].
Qed.

(** Literals read from the trail are valid. *)
Lemma tr_lit st j l : SIc st -> nth_error (tr st) j = Some l -> lit_ok l.
Proof. intros Hs Hj. eapply Forall_nth_error; [apply (si_tr _ Hs) | exact Hj]. Qed.

(** A valid literal's variable indexes every per-variable field. *)
Lemma var_ok st f l : SIc st -> lit_ok l ->
  f = FAsg \/ f = FLvl \/ f = FRsn \/ f = FPh \/ f = FSt \/ f = FSn -> lvar l < length (fv st f).
Proof.
  intros [] Hl Hf. apply lvar_lt in Hl.
  destruct Hf as [-> | [-> | [-> | [-> | [-> | ->]]]]]; lia.
Qed.

(** A valid literal indexes the watch lists. *)
Lemma lit_wl st l : SIc st -> lit_ok l -> l < length (wl st).
Proof. intros Hs Hl. rewrite (si_wl _ Hs). exact Hl. Qed.

(** Every [misc] slot is in range. *)
Lemma misc_ok st i : SIc st -> i < NMISC -> i < length (fv st FMisc).
Proof. intros Hs Hi. now rewrite (si_misc _ Hs). Qed.

(** [enq] of a valid literal with a valid reason keeps [SIc]. *)
Lemma enq_sic st l r : SIc st -> lit_ok l -> r <= length (db st) -> SIc (enq st l r).
Proof.
  intros [] Hl Hr. unfold enq. constructor; fvs; rewrite ?lset_length; auto.
  - apply Forall_app. split; [assumption | constructor; auto].
  - now apply Forall_lset.
Qed.

(** It keeps [SI] too, since the trail only grows. *)
Lemma enq_si st l r : SI st -> lit_ok l -> r <= length (db st) -> SI (enq st l r).
Proof.
  intros [Hs Hl'] Hl Hr. split; [now apply enq_sic|].
  eapply lim_lt_grow; [| | exact Hl']; fvs; [reflexivity | rewrite length_app; lia].
Qed.

(** [st'] differs from [st] only in the per-variable fields, the counters
    and the learnt clause. *)
Definition same (st st' : astate) : Prop :=
  db st' = db st /\ wl st' = wl st /\ tr st' = tr st /\ lim st' = lim st.

(** [same] is reflexive. *)
Lemma same_refl st : same st st.
Proof. repeat split. Qed.

(** [same] is transitive. *)
Lemma same_trans a b c : same a b -> same b c -> same a c.
Proof. intros (E1 & E2 & E3 & E4) (F1 & F2 & F3 & F4). repeat split; congruence. Qed.

(** Writing any field but the trail and [trail_lim] is [same]. *)
Lemma same_fset st f xs : f <> FTr -> f <> FLim -> same st (fset st f xs).
Proof.
  intros H1 H2. unfold same. fvs. repeat split.
  - destruct f; try reflexivity; congruence.
  - destruct f; try reflexivity; congruence.
Qed.

(** [lim_lt] carries across [same], so [SIc] suffices to restore [SI]. *)
Lemma si_same st st' : SI st -> SIc st' -> same st st' -> SI st'.
Proof.
  intros [_ Hl] Hs (_ & _ & E3 & E4). split; [exact Hs|]. unfold lim_lt in *. now rewrite E3, E4.
Qed.

(** ** Capacities of the fixed-size arrays *)

(** The trail's variables are below [nv]. *)
Lemma tr_vars_lt st : SIc st -> Forall (fun v => v < nv) (map lvar (tr st)).
Proof.
  intros Hs. apply Forall_map. eapply Forall_impl; [|exact (si_tr _ Hs)]. intros l. apply lit_ok_var.
Qed.

(** The trail never holds more than [nv] literals: its variables are
    distinct and below [nv]. *)
Lemma tr_len_le val st : Core val st -> SIc st -> length (tr st) <= nv.
Proof.
  intros C Hs. rewrite <- (length_map lvar). apply nodup_bound; [apply (i_nd _ _ C) | now apply tr_vars_lt].
Qed.

(** There is room on the trail for a literal over an unassigned variable
    below [nv]: [enqueue] writes within the trail's capacity [nv]. *)
Lemma tr_room val st l : Core val st -> SIc st -> lvar l < nv -> lval (asg st) l = 0 -> length (tr st) < nv.
Proof.
  intros C Hs Hl H0.
  assert (Hn : ~ In (lvar l) (map lvar (tr st))).
  { intros Hi. apply (i_tr _ _ C) in Hi. apply Hi. now apply (lval_zero _ _ (i_asg _ _ C _)). }
  enough (S (length (map lvar (tr st))) <= nv) by (rewrite length_map in *; lia).
  apply (nodup_bound (lvar l :: map lvar (tr st))).
  - constructor; [exact Hn | apply (i_nd _ _ C)].
  - constructor; [exact Hl | now apply tr_vars_lt].
Qed.

(** There are no more decisions than trail entries: decision positions are
    distinct and below the trail's length. *)
Lemma lim_le_tr st : SI st -> length (lim st) <= length (tr st).
Proof. intros [Hs Hl]. apply nodup_bound; [apply incr_nodup, (si_inc _ Hs) | exact Hl]. Qed.

(** So the trail limits never exceed their capacity [nv]. *)
Lemma lim_len_le val st : Core val st -> SI st -> length (lim st) <= nv.
Proof. intros C Hs. pose proof (lim_le_tr st Hs). pose proof (tr_len_le val st C (proj1 Hs)). lia. Qed.

(** A decision on an unassigned variable below [nv] has room to push onto
    [trail_lim]: its index [length (lim st)] is below the capacity [nv]. *)
Lemma lim_room val st l : Core val st -> SI st -> lvar l < nv -> lval (asg st) l = 0 -> length (lim st) < nv.
Proof.
  intros C Hs Hl H0. pose proof (lim_le_tr st Hs). pose proof (tr_room val st l C (proj1 Hs) Hl H0). lia.
Qed.

(** The decision's push onto [trail_lim] keeps [SIc]: the trail's length
    is above every earlier decision. *)
Lemma sic_decide st : SI st -> SIc (fset st FLim (lim st ++ [length (tr st)])).
Proof. intros [Hs Hl]. apply sic_lim; [exact Hs|]. apply incr_snoc; [apply (si_inc _ Hs) | exact Hl]. Qed.

(** Enqueueing restores [lim_lt] once every decision is at most the trail's length. *)
Lemma lim_lt_enq st l r : Forall (fun x => x <= length (tr st)) (lim st) -> lim_lt (enq st l r).
Proof.
  intros H. unfold lim_lt. fvs. rewrite length_app. cbn [length].
  eapply Forall_impl; [|exact H]. cbn. lia.
Qed.

(** A decision followed by its enqueue keeps [SI]. *)
Lemma si_decide st l r : SI st -> lit_ok l -> r <= length (db st) ->
  SI (enq (fset st FLim (lim st ++ [length (tr st)])) l r).
Proof.
  intros Hs Hl Hr. split.
  - apply enq_sic; [now apply sic_decide | exact Hl | exact Hr].
  - apply lim_lt_enq. fvs. apply Forall_app. split; [|constructor; auto].
    eapply Forall_impl; [|exact (proj2 Hs)]. cbn. lia.
Qed.

(** A backtrack target [lim[lv]] is a trail position. *)
Lemma lim_nth_lt st lv : SI st -> lv < length (lim st) -> nth lv (lim st) 0 < length (tr st).
Proof.
  intros [_ Hl] Hlv. exact (Forall_nth_error (fun x => x < length (tr st)) _ _ _ Hl (nth_error_nth' _ 0 Hlv)).
Qed.

(** Backtracking to an existing level keeps [lim_lt]: the kept decisions
    are below the new trail length [lim[lv]]. *)
Lemma lim_lt_bt st st' lv : SI st -> lv < length (lim st) ->
  tr st' = firstn (nth lv (lim st) 0) (tr st) -> lim st' = firstn lv (lim st) -> lim_lt st'.
Proof.
  intros Hs Hlv Et El. unfold lim_lt. rewrite Et, El, length_firstn.
  pose proof (lim_nth_lt st lv Hs Hlv).
  eapply Forall_impl; [|exact (incr_firstn_lt _ lv (si_inc _ (proj1 Hs)) Hlv)]. cbn. lia.
Qed.

(** And [SIc] after backtracking gives [SI]. *)
Lemma si_bt st st' lv : SI st -> SIc st' -> lv < length (lim st) ->
  tr st' = firstn (nth lv (lim st) 0) (tr st) -> lim st' = firstn lv (lim st) -> SI st'.
Proof. intros Hs Hs' Hlv Et El. split; [exact Hs' | eapply lim_lt_bt; eauto]. Qed.

(** Learnt literals are valid: each is false, so its negation is on the trail. *)
Lemma learnt_ok val st M Lr index pathC :
  Core val st -> SIc st -> AInv st M Lr index pathC -> Forall lit_ok (tl Lr).
Proof.
  intros C Hs A. eapply Forall_impl; [|exact (a_lr _ _ _ _ _ A)]. intros q (Hq & _).
  destruct (false_trail val st C q Hq) as (k & Hk). apply lit_ok_lneg. eapply tr_lit; eauto.
Qed.

(** A learnt clause over distinct variables below [nv] fits the capacity
    [nv + 1] of the [learnt] array. *)
Lemma learnt_len st M Lr index pathC :
  AInv st M Lr index pathC -> Forall (fun q => lvar q < nv) (tl Lr) -> length Lr <= nv + 1.
Proof.
  intros A F. enough (length (tl Lr) <= nv) by (destruct Lr; cbn in *; lia).
  rewrite <- (length_map lvar). apply nodup_bound; [exact (a_nd _ _ _ _ _ A)|].
  now apply Forall_map.
Qed.

(** Under [Core] and [SIc] the variable bound is automatic. *)
Lemma learnt_len_si val st M Lr index pathC :
  Core val st -> SIc st -> AInv st M Lr index pathC -> length Lr <= nv + 1.
Proof.
  intros C Hs A. apply (learnt_len st M Lr index pathC A).
  eapply Forall_impl; [|exact (learnt_ok val st M Lr index pathC C Hs A)]. intros q. apply lit_ok_var.
Qed.

(** [push_learnt q] for an unmarked false [q] writes at index
    [length Lr <= nv], within the capacity [nv + 1]. *)
Lemma learnt_room val st M Lr index pathC q :
  Core val st -> SIc st -> AInv st M Lr index pathC ->
  lval (asg st) q = 2 -> ~ marked M (lvar q) -> length Lr <= nv.
Proof.
  intros C Hs A Hq Hu.
  assert (Hok : Forall lit_ok (q :: tl Lr)).
  { constructor; [|exact (learnt_ok val st M Lr index pathC C Hs A)].
    destruct (false_trail val st C q Hq) as (k & Hk). apply lit_ok_lneg. eapply tr_lit; eauto. }
  assert (Hn : NoDup (map lvar (q :: tl Lr))).
  { cbn [map]. constructor; [|exact (a_nd _ _ _ _ _ A)]. intros Hi.
    apply in_map_iff in Hi as (q' & E & Hq'). pose proof (a_lr _ _ _ _ _ A) as F.
    rewrite Forall_forall in F. destruct (F q' Hq') as (_ & Hm & _). rewrite E in Hm. contradiction. }
  pose proof (nodup_bound _ nv Hn) as H.
  enough (length (tl Lr) < nv) by (destruct Lr; cbn in *; lia).
  rewrite <- (length_map lvar (tl Lr)). cbn [map length] in H. apply H.
  change (lvar q :: map lvar (tl Lr)) with (map lvar (q :: tl Lr)).
  apply Forall_map. eapply Forall_impl; [|exact Hok]. intros l. apply lit_ok_var.
Qed.

End Safe.
