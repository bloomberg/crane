(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import SetoidList FSets.
From Stdlib Require Import Wf_nat Compare_dec.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import Table.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import DFA.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import CanonNF.

(** Interned-DFA builder: given a regex, precomputes a flat [N]-indexed
    transition table equivalent to the regex-keyed [regex2dfa] table, so that
    a per-character transition becomes an O(1) array index ([matrix[id][code]])
    instead of an AVL lookup keyed by structural regex comparison ([re_compare]).

    This module is purely computable "build support": every function here runs
    once per lexical rule, at DFA-construction time (same place [regex2dfa]
    already runs today), never per input character. The per-character hot path
    ([step]/[dfa_nth]) is a plain array index. Correctness of the interning
    is [int_accepts_correct] below, lifted to the lexer interface by
    [Lexer.Memo.IntLexer]. *)
(** Default-returning list index, used both build-time (state ids) and at
    run time (matrix/accept lookups). Maps to C++ [operator[]] at extraction
    (regular [list] [nth] is left untouched).

    Deliberately declared at module top level rather than inside [IntDFAFn]:
    Crane extracts a functor to a C++ *template*, generated from the functor
    body, so a [Crane Extract Inlined Constant] attached to a constant of an
    applied-functor instance never reaches the emitted template and is
    silently ignored. A top-level constant has a stable global name that the
    inline mapping does resolve against. *)
Fixpoint dfa_nth {X : Type} (l : list X) (n : N) (d : X) : X :=
  match l with
  | [] => d
  | h :: t =>
    match n with
    | N0 => h
    | Npos _ => dfa_nth t (N.pred n) d
    end
  end.

(** A random-access sequence, used *only* for the interned DFA's transition
    matrix and accept vector.

    Why not plain [list]? Coq's [list] is mapped project-wide to
    [crane::list], a singly-linked cons list (see [benchmarking/ConsList.v]),
    which is the right default for extracted functional code but has no O(1)
    indexing -- and indexing is the single operation the interned DFA exists
    to make fast. [vec] is structurally identical to [list] but is a distinct
    inductive, so it can carry its own extraction mapping
    ([immer::flex_vector], O(1) [operator[]]) without disturbing the global
    [list] mapping.

    [vec] is built once per lexical rule at DFA-construction time and is
    read-only thereafter. *)
Inductive vec (X : Type) : Type :=
| vnil : vec X
| vcons : X -> vec X -> vec X.

Arguments vnil {X}.
Arguments vcons {X} _ _.

(** Default-returning index into a [vec]. This is the interned DFA's hot-path
    primitive: one per input character for the matrix row, the matrix column
    and the accept vector. It is overridden at extraction to a bounds-checked
    [operator[]] (see [benchmarking/CraneExtraction.v]); the structural
    definition here is the specification the override must agree with. *)
Fixpoint vec_nth {X : Type} (v : vec X) (n : N) (d : X) : X :=
  match v with
  | vnil => d
  | vcons h t =>
    match n with
    | N0 => h
    | Npos _ => vec_nth t (N.pred n) d
    end
  end.

(** Position of [a] in [l] under the boolean equality [eqb], or [0] if absent.

    Top-level (not inside [IntDFAFn]) for the same extraction reason as
    [dfa_nth]/[vec_nth]: in the concrete instantiation this is overridden to
    an O(1) character cast, and an override can only attach to a top-level
    constant.

    The override is sound because the only alphabet instantiated anywhere in
    this project is [AsciiSigma.Alphabet], whose [SigmaEnum] is
    [AsciiFinite.asciiEnum = asciiEnumFn 256]. Beware the order: since
    [asciiEnumFn (S m) = ascii_of_nat m :: asciiEnumFn m], that list runs
    *descending*, [chr 255 ... chr 0], so a character's position in it is
    [255 - codepoint] and NOT [codepoint]. The extraction override must match
    (see [benchmarking/CraneExtraction.v]); getting it backwards silently
    mis-indexes every column of the transition matrix. Both sides are pure
    deterministic functions of [a] alone, and no Coq-level proof here relies
    on which of the two is used. *)
Fixpoint idx_of_eqb {X : Type} (eqb : X -> X -> bool) (a : X) (l : list X) : N :=
  match l with
  | [] => 0%N
  | h :: t => if eqb a h then 0%N else N.succ (idx_of_eqb eqb a t)
  end.

Fixpoint vec_of_list {X : Type} (l : list X) : vec X :=
  match l with
  | [] => vnil
  | h :: t => vcons h (vec_of_list t)
  end.

(** [vec_nth] agrees with [dfa_nth] on converted lists, so switching the
    interned DFA's representation from [list] to [vec] is semantics-
    preserving. *)
Lemma vec_nth_of_list : forall (X : Type) (l : list X) (n : N) (d : X),
    vec_nth (vec_of_list l) n d = dfa_nth l n d.
Proof.
  intros X l. induction l as [| h t IH]; intros n d.
  - reflexivity.
  - simpl. destruct n; [reflexivity | apply IH].
Qed.

(** In-range indexing commutes with [map] without any relation between the
    two defaults, because an in-range index never reaches them. ([dfa_nth_map]
    below drops the range hypothesis at the cost of requiring the defaults to
    correspond, which the matrix's [[]] / [0] defaults do not.) *)
Lemma dfa_nth_map_lt : forall (X Y : Type) (f : X -> Y) (l : list X) i
                              (d : X) (d' : Y),
    (i < N.of_nat (length l))%N ->
    dfa_nth (map f l) i d' = f (dfa_nth l i d).
Proof.
  intros X Y f l. induction l as [| h t IH]; intros i d d' Hlt; simpl in *.
  - lia.
  - destruct i; [reflexivity |]. apply IH. lia.
Qed.

(** An in-range slot holds a genuine member of the list. *)
Lemma dfa_nth_In : forall (X : Type) (l : list X) i (d : X),
    (i < N.of_nat (length l))%N -> In (dfa_nth l i d) l.
Proof.
  intros X l. induction l as [| h t IH]; intros i d Hlt; simpl in *.
  - lia.
  - destruct i; [left; reflexivity |]. right. apply IH. lia.
Qed.

Module IntDFAFn (TabT : Table.T).

  Module Export D := DFAFn TabT.
  Import TabT.
  Import TabT.Defs.

  (** Position of [r] in [l] (build-time only: interning states of a single
      rule's DFA into a small canonical list). Kept as a specification-level
      definition, but NOT used by [build_matrix]/[build_start] below: a naive
      linear scan there makes building the transition matrix O(S^2 * |Sigma|)
      in the number of DFA states S, which was observed to blow up (multi-
      second build-time hangs) for XML's more complex lexical rules. Use
      [idx_of_map] (backed by the O(log S) [reFM] AVL map) instead. *)
  Fixpoint idx_of (r : regex) (l : list regex) : N :=
    match l with
    | [] => 0%N
    | h :: t => if regex_eq r h then 0%N else N.succ (idx_of r t)
    end.

  (** [reFM]-backed [regex -> N] map assigning each state in [l] its
      position, built once in a single O(S log S) fold. *)
  Definition index_map (l : list regex) : reFM.t N :=
    fst (fold_left
           (fun p r => match p with
                       | (m, n) => (reFM.add r n m, N.succ n)
                       end)
           l (reFM.empty N, 0%N)).

  (** O(log S) position lookup via [index_map]; falls back to [0] if [r] is
      (unexpectedly) absent from the map, same fallback behavior as [idx_of]
      when [r] isn't found in the underlying list. *)
  Definition idx_of_map (r : regex) (m : reFM.t N) : N :=
    match reFM.find r m with
    | Some n => n
    | None => 0%N
    end.

  (** The single fold step of [index_map], named so the lemmas below can
      reason about partially-folded prefixes. *)
  Definition im_step (p : reFM.t N * N) (r : regex) : reFM.t N * N :=
    match p with
    | (m, n) => (reFM.add r n m, N.succ n)
    end.

  Lemma index_map_unfold : forall l,
      index_map l = fst (fold_left im_step l (reFM.empty N, 0%N)).
  Proof. reflexivity. Qed.

  (** The accumulator's counter is just the length of the prefix consumed. *)
  Lemma im_fold_snd : forall l m n,
      snd (fold_left im_step l (m, n)) = (n + N.of_nat (length l))%N.
  Proof.
    induction l as [| a l IH]; intros m n; simpl.
    - lia.
    - rewrite IH. lia.
  Qed.

  (** Round-trip, generalized over an arbitrary starting accumulator: a hit in
      the folded map either came from the initial map or names a genuine
      position in [l] (offset by the starting counter).

      The [Hm] hypothesis -- every pre-existing binding is below the starting
      counter -- is what rules out an old binding being mistaken for a new
      one; it holds trivially of the empty map [index_map] actually starts
      from. *)
  Lemma im_fold_spec : forall l m n r i,
      (forall r' j, reFM.find r' m = Some j -> (j < n)%N) ->
      reFM.find r (fst (fold_left im_step l (m, n))) = Some i ->
      reFM.find r m = Some i
      \/ ((n <= i)%N /\ (i < n + N.of_nat (length l))%N
          /\ dfa_nth l (i - n) EmptySet = r).
  Proof.
    induction l as [| a l IH]; intros m n r i Hm Hf.
    - simpl in Hf. left. exact Hf.
    - simpl in Hf.
      assert (Hm' : forall r' j, reFM.find r' (reFM.add a n m) = Some j ->
                                 (j < N.succ n)%N).
      { intros r' j Hj.
        destruct (Regexes.regex_dec a r') as [Heq | Hne].
        - subst. rewrite reFMF.add_eq_o in Hj by reflexivity.
          inversion Hj. lia.
        - rewrite reFMF.add_neq_o in Hj by (intros C; apply Hne; exact C).
          apply Hm in Hj. lia. }
      specialize (IH _ _ _ _ Hm' Hf).
      destruct IH as [Hadd | (Hlo & Hhi & Hnth)].
      + (* the hit was already present before consuming the tail *)
        destruct (Regexes.regex_dec a r) as [Heq | Hne].
        * subst. rewrite reFMF.add_eq_o in Hadd by reflexivity.
          inversion Hadd. right. simpl. split; [lia | split; [lia |]].
          rewrite N.sub_diag. reflexivity.
        * rewrite reFMF.add_neq_o in Hadd by (intros C; apply Hne; exact C).
          left. exact Hadd.
      + right. simpl in *. split; [lia | split; [lia |]].
        destruct (i - n)%N eqn:E; [lia |].
        replace (N.pred (N.pos p)) with (i - N.succ n)%N by lia.
        exact Hnth.
  Qed.

  (** L1: a slot handed out by [index_map] really does name that regex's
      position in the interned state list. This is what licenses reading a
      transition target back as an index. *)
  Lemma index_map_nth : forall l r i,
      reFM.find r (index_map l) = Some i ->
      dfa_nth l i EmptySet = r /\ (i < N.of_nat (length l))%N.
  Proof.
    intros l r i Hf. rewrite index_map_unfold in Hf.
    apply im_fold_spec in Hf.
    - destruct Hf as [Hempty | (_ & Hhi & Hnth)].
      + rewrite reFMF.empty_o in Hempty. discriminate.
      + rewrite N.sub_0_r in Hnth. split; [exact Hnth | lia].
    - intros r' j Hj. rewrite reFMF.empty_o in Hj. discriminate.
  Qed.

  (** Boolean equality on [Sigma] derived from [compareT]. *)
  Definition sigma_eqb (a b : Sigma) : bool :=
    match compareT a b with
    | Eq => true
    | _ => false
    end.

  (** See [IntDFA.idx_of_eqb]: [code] delegates to that top-level constant so
      that the O(1) extraction override can reach it. *)

  (** Position of [a] in [l]. In the concrete (ASCII) instantiation this is
      overridden at extraction to the O(1) [Ascii.N_of_ascii] cast (see
      [benchmarking/CraneExtraction.v]); left as a plain scan here since the
      two representations are extensionally interchangeable (both are pure
      deterministic functions of [a] alone) and the Coq-level spec never
      relies on which one is used. *)
  Definition idx_of_sigma (a : Sigma) (l : list Sigma) : N :=
    idx_of_eqb sigma_eqb a l.

  (** The column index of a character within the (fixed) alphabet enumeration. *)
  Definition code (a : Sigma) : N := idx_of_sigma a SigmaEnum.

  Lemma sigma_eqb_eq : forall a b, sigma_eqb a b = true <-> a = b.
  Proof.
    intros a b. unfold sigma_eqb. split; intros H.
    - destruct (compareT a b) eqn:E; try discriminate.
      apply compareT_eq. exact E.
    - subst. rewrite (proj2 (compareT_eq b b) eq_refl). reflexivity.
  Qed.

  (** L2a: [code a] really is the position of [a] in the alphabet
      enumeration, so reading column [code a] of a matrix row built by
      mapping over [SigmaEnum] recovers the cell for [a]. *)
  Lemma code_nth : forall (d : Sigma) a,
      dfa_nth SigmaEnum (code a) d = a.
  Proof.
    intros d a. unfold code, idx_of_sigma.
    pose proof (Sigma_finite a) as Hin.
    induction SigmaEnum as [| h t IH]; simpl in *.
    - contradiction.
    - destruct (sigma_eqb a h) eqn:E.
      + apply sigma_eqb_eq in E. congruence.
      + destruct Hin as [Heq | Hin].
        * rewrite Heq in E.
          rewrite (proj2 (sigma_eqb_eq a a) eq_refl) in E. discriminate.
        * destruct (N.succ (idx_of_eqb sigma_eqb a t)) eqn:E2; [lia |].
          replace (N.pred (N.pos p)) with (idx_of_eqb sigma_eqb a t) by lia.
          apply IH. exact Hin.
  Qed.

  (** [code a] is in range, so a matrix row built by mapping over [SigmaEnum]
      really has a cell at that column. Companion to [code_nth]. *)
  Lemma code_lt : forall a, (code a < N.of_nat (length SigmaEnum))%N.
  Proof.
    intros a. unfold code, idx_of_sigma.
    pose proof (Sigma_finite a) as Hin.
    induction SigmaEnum as [| h t IH]; simpl in *.
    - contradiction.
    - destruct (sigma_eqb a h) eqn:E; [lia |].
      destruct Hin as [Heq | Hin].
      + rewrite Heq in E. rewrite (proj2 (sigma_eqb_eq a a) eq_refl) in E.
        discriminate.
      + specialize (IH Hin). lia.
  Qed.

  (** L2b: indexing commutes with [map], provided the defaults correspond. *)
  Lemma dfa_nth_map : forall (X Y : Type) (f : X -> Y) (l : list X) i (d : X),
      dfa_nth (map f l) i (f d) = f (dfa_nth l i d).
  Proof.
    intros X Y f l. induction l as [| h t IH]; intros i d; simpl.
    - reflexivity.
    - destruct i; [reflexivity | apply IH].
  Qed.

  (** The canonical, deduplicated list of reachable DFA states for [e]; a
      state's id is its position in this list.

      [get_states T] is populated by [add_state] calls made only for
      *derivative* states discovered while filling the table (see
      [fill_Table_all'_bin] in [Table.v]) -- the root/start state [canon e]
      itself is only added if some other state transitions back to it (e.g.
      via a self-loop). [DFAaccepting] (the un-interned design) tolerates
      this by falling back to computing [nullable e] directly whenever [e]
      isn't a member of [get_states T]; we can't do that generically once
      states are looked up purely by integer id, so instead we make sure the
      start state is always explicitly a member of the interned list (its
      row is still computable via [get_Table]/[nullable] regardless of
      whether it was ever [add_state]'d). *)
  Definition build_states (d : DFA) : list regex :=
    match d with
    | (start, T, _) =>
      let raw := reFS.elements (get_states T) in
      if existsb (regex_eq start) raw then raw else start :: raw
    end.

  (** The regex the DFA moves to from [s] on [a]: the already-filled table
      entry, falling back to a direct derivative computation if a table entry
      is ever absent. Both alternatives are language-equivalent to
      [derivative a s] (see [trans_target_equiv]), which is the only property
      the correctness argument uses. *)
  Definition trans_target (T : Table) (s : regex) (a : Sigma) : regex :=
    match get_Table T s a with
    | Some e' => e'
    | None => canon (derivative a s)
    end.

  (** A table entry and its fallback are both language-equivalent to the
      Brzozowski derivative -- the [Some] case by the [derived] invariant the
      table fill maintains, the [None] case by [canon_equiv]. *)
  Lemma trans_target_equiv : forall T s a,
      derived T -> re_equiv (trans_target T s a) (derivative a s).
  Proof.
    intros T s a Hd. unfold trans_target.
    destruct (get_Table T s a) as [e' |] eqn:E.
    - exact (Hd _ _ _ E).
    - apply canon_equiv.
  Qed.

  (** * Saturating the interned state list

      Interning is sound only when the state list is closed under
      [trans_target] (see [closed_check] below).  The list [build_states]
      reads off the filled table is closed in practice but not provably so:
      the only universe we can prove closed, [CanonNF.Superset], is far too
      large to serve as the table fill's fuel.  So instead of assuming or
      merely checking closure, we *compute* it -- repeatedly add every
      transition target of every listed state until a round adds nothing.

      Termination is where the theory is spent: each round either stops or
      strictly grows a duplicate-free list that [CanonNF.Superset_closed]
      confines to [Superset e], which bounds the number of rounds.  Note that
      [Superset e] is never evaluated: it occurs only inside the erased
      [Prop] arguments [HT], [Hin] and [Ha].  The regex [e0] is threaded
      instead, and it is only there to name that universe.

      In practice the first round reproduces the table's own state set and
      the second stops, so this costs about what [closed_check] used to. *)
  Module NF := CanonNF.CanonNFFn TabT.R TabT.TabTy.

  (** Set membership read off the element list. *)
  Lemma in_elements_In : forall S x, In x (reFS.elements S) -> reFS.In x S.
  Proof.
    intros S x H. apply reFS.elements_2, InA_alt.
    exists x. split; [apply reFS.E.eq_refl | exact H].
  Qed.

  (** Deduplication through the regex [FSet].  [List.nodup] would do the job
      but is quadratic, and a saturation round hands it |states| * |Sigma|
      entries (thousands), so the set-based O(n log n) version is the one
      that can actually run. *)
  Definition set_of (l : list regex) : reFS.t :=
    fold_left (fun s x => reFS.add x s) l reFS.empty.

  Definition dedup (l : list regex) : list regex := reFS.elements (set_of l).

  Lemma add_iff' : forall s a x, reFS.In x (reFS.add a s) <-> x = a \/ reFS.In x s.
  Proof.
    intros s a x. split.
    - intros H. destruct (Regexes.regex_dec x a) as [Heq | Hne]; [left; exact Heq |].
      right. apply reFS.add_3 with (x := a); auto.
    - intros [Heq | H]; [subst; apply reFS.add_1; reflexivity | apply reFS.add_2; exact H].
  Qed.

  Lemma fold_add_spec : forall l s x,
      reFS.In x (fold_left (fun s y => reFS.add y s) l s) <-> (reFS.In x s \/ In x l).
  Proof.
    induction l as [| a l IH]; intros s x; simpl.
    - split; [auto | intros [H | []]; exact H].
    - rewrite IH, add_iff'. split.
      + intros [[Heq | Hs] | Hl];
          [right; left; symmetry; exact Heq | left; exact Hs | right; right; exact Hl].
      + intros [Hs | [Heq | Hl]];
          [left; right; exact Hs | left; left; symmetry; exact Heq | right; exact Hl].
  Qed.

  Lemma dedup_In : forall l x, In x (dedup l) <-> In x l.
  Proof.
    intros l x. unfold dedup, set_of. split.
    - intros H. apply in_elements_In, fold_add_spec in H.
      destruct H as [H | H]; [| exact H].
      exfalso. revert H. apply reFS.empty_1.
    - intros H.
      assert (Hs : reFS.In x (fold_left (fun s y => reFS.add y s) l reFS.empty))
        by (apply fold_add_spec; right; exact H).
      apply reFS.elements_1, InA_alt in Hs as (y & Hy & Hin).
      rewrite Hy. exact Hin.
  Qed.

  Lemma dedup_NoDup : forall l, NoDup (dedup l).
  Proof. intros l. apply NoDupA_NoDup, reFS.elements_3w. Qed.

  (** [U] is closed under the transition function of [T]. *)
  Definition TransIn (U : list regex) (T : Table) : Prop :=
    forall s a, In s U -> In (trans_target T s a) U.

  (** One saturation round: everything reachable in one step, deduplicated. *)
  Definition sat_step (T : Table) (states : list regex) : list regex :=
    dedup
      (states ++ flat_map (fun s => map (trans_target T s) SigmaEnum) states).

  (** The recursion's order: a strictly longer duplicate-free sublist of [U].
      [U] bounds the length, so this is well founded. *)
  Definition satR (U : list regex) (v' v : list regex) : Prop :=
    incl v' U /\ NoDup v' /\ length v < length v'.

  Lemma satR_wf : forall U, well_founded (satR U).
  Proof.
    intros U. apply (well_founded_lt_compat _ (fun v => length U - length v)).
    intros x y (Hincl & Hnd & Hlt).
    pose proof (NoDup_incl_length Hnd Hincl). lia.
  Qed.

  Lemma sat_step_incl : forall T states, incl states (sat_step T states).
  Proof. intros T states x Hx. apply dedup_In, in_or_app. left. exact Hx. Qed.

  Lemma sat_step_target : forall T states s a,
      In s states -> In (trans_target T s a) (sat_step T states).
  Proof.
    intros T states s a Hs. apply dedup_In, in_or_app. right.
    apply in_flat_map. exists s. split; [exact Hs |].
    apply in_map, Sigma_finite.
  Qed.

  Lemma sat_step_U : forall U T states,
      TransIn U T -> incl states U -> incl (sat_step T states) U.
  Proof.
    intros U T states HT Hincl x Hx. unfold sat_step in Hx. rewrite dedup_In in Hx.
    apply in_app_or in Hx as [Hx | Hx]; [auto |].
    apply in_flat_map in Hx as (s & Hs & Hx).
    apply in_map_iff in Hx as (a & <- & _).
    apply HT, Hincl, Hs.
  Qed.

  Fixpoint saturate (T : Table) (e0 : regex)
           (HT : TransIn (NF.Superset e0) T)
           (states : list regex) (Hin : incl states (NF.Superset e0))
           (Ha : Acc (satR (NF.Superset e0)) states) {struct Ha} : list regex :=
    match le_lt_dec (length (sat_step T states)) (length states) with
    | left _ => states
    | right Hlt =>
        saturate T e0 HT (sat_step T states) (sat_step_U _ T states HT Hin)
          (Acc_inv Ha (conj (sat_step_U _ T states HT Hin)
                            (conj (dedup_NoDup _) Hlt)))
    end.

  (** What the saturation delivers: a duplicate-free extension of the input
      that is genuinely closed under [trans_target]. *)
  Lemma saturate_spec : forall T e0 (HT : TransIn (NF.Superset e0) T) states
                               (Hin : incl states (NF.Superset e0))
                               (Ha : Acc (satR (NF.Superset e0)) states),
      NoDup states ->
      NoDup (saturate T e0 HT states Hin Ha)
      /\ incl states (saturate T e0 HT states Hin Ha)
      /\ (forall x a, In x (saturate T e0 HT states Hin Ha) ->
                      In (trans_target T x a) (saturate T e0 HT states Hin Ha)).
  Proof.
    intros T e0 HT states.
    induction states as [states IH]
      using (well_founded_induction (satR_wf (NF.Superset e0))).
    intros Hin Ha HN. destruct Ha as [Hacc]. cbn [saturate].
    destruct (le_lt_dec (length (sat_step T states)) (length states))
      as [Hle | Hlt].
    - assert (Hback : incl (sat_step T states) states)
        by (apply NoDup_length_incl; [exact HN | exact Hle | apply sat_step_incl]).
      repeat split; [exact HN | apply incl_refl |].
      intros x a Hx. apply Hback, sat_step_target, Hx.
    - assert (Hsat : satR (NF.Superset e0) (sat_step T states) states)
        by (repeat split;
            [apply sat_step_U; assumption | apply dedup_NoDup | exact Hlt]).
      match goal with
      | |- context [saturate T e0 HT ?s ?p ?q] =>
          destruct (IH s Hsat p q (dedup_NoDup _))
            as (H1 & H2 & H3)
      end.
      repeat split; [exact H1 | | exact H3].
      eapply incl_tran; [apply sat_step_incl | exact H2].
  Qed.

  (** [matrix[id s][code a] = idx_of (trans_target T s a) states]. State
      positions are looked up via the O(log S) [im] map (see [index_map]),
      not the O(S) [idx_of] scan, to keep the overall build cost
      O(S * |Sigma| * log S) rather than O(S^2 * |Sigma|). *)
  Definition build_matrix (d : DFA) (states : list regex) : list (list N) :=
    match d with
    | (_, T, _) =>
      let im := index_map states in
      map (fun s => map (fun a => idx_of_map (trans_target T s a) im) SigmaEnum)
          states
    end.

  (** * Closure certificate

      Interning is sound exactly when the interned state list is *closed*:
      every state's transition target on every character is itself in the
      list, and the start state is in the list. Only then does an integer id
      faithfully stand for a regex, because only then does
      [dfa_nth states (matrix[id][code a])] recover the target regex rather
      than the [idx_of_map]/[dfa_nth] fallback (index [0], resp. [EmptySet]).

      Closure is not a property the table fill is known to deliver: its fuel
      ([Brzozowski_bound]) cannot be shown sufficient, since the only
      universe we can prove closed ([CanonNF.Superset]) is astronomically
      too large to serve as fuel. So the state list is *saturated* instead
      (see [int_states]), and [int_states_closed] proves this check accepts
      it. The check therefore always succeeds; it is kept because the
      simulation lemmas below are stated over it, and because it costs only
      O(S * |Sigma| * log S) once per lexical rule at build time, nothing on
      the per-character hot path.

      [mem_states im r] is the primitive: does [r] have an id? *)
  Definition mem_states (im : reFM.t N) (r : regex) : bool :=
    match reFM.find r im with
    | Some _ => true
    | None => false
    end.

  Definition closed_check (d : DFA) (states : list regex) : bool :=
    match d with
    | (start, T, _) =>
      let im := index_map states in
      andb (mem_states im start)
           (forallb (fun s => forallb (fun a => mem_states im (trans_target T s a))
                                      SigmaEnum)
                    states)
    end.

  (** [mem_states] reflected: a hit names a genuine position in [states]. *)
  Lemma mem_states_nth : forall states r,
      mem_states (index_map states) r = true ->
      dfa_nth states (idx_of_map r (index_map states)) EmptySet = r
      /\ (idx_of_map r (index_map states) < N.of_nat (length states))%N.
  Proof.
    intros states r H. unfold mem_states, idx_of_map in *.
    destruct (reFM.find r (index_map states)) as [i |] eqn:E; [| discriminate].
    apply index_map_nth. exact E.
  Qed.

  (** L3: the certificate delivers exactly the fact the simulation needs --
      every matrix cell reachable from a listed state names a slot whose
      regex *is* the transition target. *)
  Lemma closed_check_step : forall start T o states s a,
      closed_check (start, T, o) states = true ->
      In s states ->
      dfa_nth states (idx_of_map (trans_target T s a) (index_map states)) EmptySet
      = trans_target T s a.
  Proof.
    intros start T o states s a Hc Hin.
    simpl in Hc. apply andb_prop in Hc as (_ & Hall).
    rewrite forallb_forall in Hall. specialize (Hall s Hin).
    rewrite forallb_forall in Hall. specialize (Hall a (Sigma_finite a)).
    apply mem_states_nth. exact Hall.
  Qed.

  (** L3': and that the start state is listed, so [build_start] (which is
      exactly this [idx_of_map]) is faithful. *)
  Lemma closed_check_start : forall start T o states,
      closed_check (start, T, o) states = true ->
      dfa_nth states (idx_of_map start (index_map states)) EmptySet = start.
  Proof.
    intros start T o states Hc.
    simpl in Hc. apply andb_prop in Hc as (Hs & _).
    apply mem_states_nth. exact Hs.
  Qed.

  (** ** The state list is closed by construction

      Rather than hoping [build_states] is closed, we saturate it: the
      resulting [int_states] provably satisfies [closed_check], so the
      certificate is a formality and the un-interned fallback is dead code. *)

  (** The converse of [index_map_nth]: every listed state does get an id. *)
  Lemma im_fold_mem : forall l m n r,
      (In r l \/ (exists j, reFM.find r m = Some j)) ->
      exists i, reFM.find r (fst (fold_left im_step l (m, n))) = Some i.
  Proof.
    induction l as [| a l IH]; intros m n r H; simpl.
    - destruct H as [Hf | (j & Hj)]; [destruct Hf |]. exists j. exact Hj.
    - apply IH. destruct (Regexes.regex_dec a r) as [Heq | Hne].
      + right. exists n. subst. apply reFMF.add_eq_o. reflexivity.
      + destruct H as [[Ha | Ht] | (j & Hj)].
        * exfalso. auto.
        * left. exact Ht.
        * right. exists j.
          rewrite reFMF.add_neq_o by (intros C; apply Hne; exact C). exact Hj.
  Qed.

  Lemma mem_states_In : forall states r,
      In r states -> mem_states (index_map states) r = true.
  Proof.
    intros states r H. unfold mem_states. rewrite index_map_unfold.
    destruct (im_fold_mem states (reFM.empty N) 0%N r (or_introl H)) as (i & Hi).
    rewrite Hi. reflexivity.
  Qed.

  Definition dfa_table (d : DFA) : Table := snd (fst d).

  Lemma regex2dfa_shape : forall e,
      regex2dfa e = (canon e, dfa_table (regex2dfa e),
                     fin_states (get_states (dfa_table (regex2dfa e)))).
  Proof. reflexivity. Qed.

  Lemma build_states_eq : forall e,
      build_states (regex2dfa e) =
      (let raw := reFS.elements (get_states (dfa_table (regex2dfa e))) in
       if existsb (regex_eq (canon e)) raw then raw else canon e :: raw).
  Proof. reflexivity. Qed.

  (** The table [regex2dfa] leaves behind never leaves [Superset e], and
      every entry it holds is the canonical derivative of its key.  Both come
      straight from [Table.fill_Table_all_bin_invariants]; neither needs a
      fuel bound. *)
  Lemma regex2dfa_invariants : forall e,
      StatesIn (NF.Superset e) (dfa_table (regex2dfa e))
      /\ DerivedEq (dfa_table (regex2dfa e)).
  Proof.
    intros e.
    assert (HU : UClosed (NF.Superset e) (char_set e))
      by (intros x c Hx _; apply NF.Superset_closed, Hx).
    assert (HS : In (canon (canon e)) (NF.Superset e))
      by (rewrite NF.canon_idem; apply NF.start_in_Superset).
    exact (fill_Table_all_bin_invariants (NF.Superset e) (char_set e) (canon e)
                                         (Brzozowski_bound e) HU HS).
  Qed.

  (** Hence [Superset e] is closed under that table's transition function --
      the termination fact [saturate] runs on. *)
  Lemma regex2dfa_TransIn : forall e,
      TransIn (NF.Superset e) (dfa_table (regex2dfa e)).
  Proof.
    intros e s a Hs. destruct (regex2dfa_invariants e) as (_ & Hd).
    unfold trans_target.
    destruct (get_Table (dfa_table (regex2dfa e)) s a) as [s' |] eqn:E.
    - rewrite (Hd _ _ _ E). apply NF.Superset_closed, Hs.
    - apply NF.Superset_closed, Hs.
  Qed.

  Lemma start_in_build_states : forall e, In (canon e) (build_states (regex2dfa e)).
  Proof.
    intros e. rewrite build_states_eq. cbv zeta.
    destruct (existsb (regex_eq (canon e))
                      (reFS.elements (get_states (dfa_table (regex2dfa e))))) eqn:E.
    - apply existsb_exists in E as (x & Hx & Hex).
      apply regex_eq_correct in Hex. rewrite Hex. exact Hx.
    - left. reflexivity.
  Qed.

  Lemma build_states_incl : forall e,
      incl (build_states (regex2dfa e)) (NF.Superset e).
  Proof.
    intros e x Hx. destruct (regex2dfa_invariants e) as (Hs & _).
    rewrite build_states_eq in Hx. cbv zeta in Hx.
    assert (Hraw : In x (reFS.elements (get_states (dfa_table (regex2dfa e)))) ->
                   In x (NF.Superset e))
      by (intros H; apply Hs, in_elements_In, H).
    destruct (existsb (regex_eq (canon e))
                      (reFS.elements (get_states (dfa_table (regex2dfa e)))));
      [auto |].
    destruct Hx as [Heq | Hx]; [| auto].
    rewrite <- Heq. apply NF.start_in_Superset.
  Qed.

  Lemma dedup_build_states_incl : forall e,
      incl (dedup (build_states (regex2dfa e))) (NF.Superset e).
  Proof. intros e x Hx. rewrite dedup_In in Hx. apply build_states_incl, Hx. Qed.

  Lemma TransIn_of : forall e d,
      regex2dfa e = d -> TransIn (NF.Superset e) (dfa_table d).
  Proof. intros e d H. subst. apply regex2dfa_TransIn. Qed.

  Lemma incl_of : forall e d,
      regex2dfa e = d -> incl (dedup (build_states d)) (NF.Superset e).
  Proof. intros e d H. subst. apply dedup_build_states_incl. Qed.

  (** The interned state list.  The common case is that the table fill has
      already produced a closed set, and then the certificate alone settles
      it -- one pass, the same order as building the matrix.  Only when it
      does not do we saturate, which is where the termination argument is
      spent.  Either way the result is closed, unconditionally
      ([int_states_closed]).

      [d] is passed in rather than recomputed so that a caller which already
      has [regex2dfa e] does not pay for the Brzozowski fill twice; [H] ties
      it back to [e] and is erased at extraction, as are [saturate]'s other
      [Prop] arguments -- so [NF.Superset] is never built. *)
  Definition int_states_d (e : regex) (d : DFA) (H : regex2dfa e = d)
    : list regex :=
    let bs := build_states d in
    if closed_check d bs then bs
    else saturate (dfa_table d) e (TransIn_of e d H)
                  (dedup bs) (incl_of e d H) (satR_wf (NF.Superset e) _).

  Definition int_states (e : regex) : list regex :=
    int_states_d e (regex2dfa e) eq_refl.

  Lemma closed_check_intro : forall e states,
      In (canon e) states ->
      (forall x a, In x states ->
                   In (trans_target (dfa_table (regex2dfa e)) x a) states) ->
      closed_check (regex2dfa e) states = true.
  Proof.
    intros e states Hst Hcl. unfold closed_check.
    rewrite regex2dfa_shape. apply andb_true_intro. split.
    - apply mem_states_In, Hst.
    - apply forallb_forall. intros s Hs.
      apply forallb_forall. intros a _.
      apply mem_states_In, Hcl, Hs.
  Qed.

  Lemma saturate_closed : forall e,
      let T := dfa_table (regex2dfa e) in
      forall (HT : TransIn (NF.Superset e) T) states
             (Hin : incl states (NF.Superset e))
             (Ha : Acc (satR (NF.Superset e)) states),
        NoDup states -> In (canon e) states ->
        closed_check (regex2dfa e) (saturate T e HT states Hin Ha) = true.
  Proof.
    intros e T HT states Hin Ha HN Hst.
    destruct (saturate_spec T e HT states Hin Ha HN) as (_ & Hgrow & Hclo).
    apply closed_check_intro; [apply Hgrow, Hst | exact Hclo].
  Qed.

  (** The certificate always succeeds on the interned list, so interning is
      sound for every regex and the un-interned fallback is unreachable. *)
  Theorem int_states_closed : forall e d (H : regex2dfa e = d),
      closed_check d (int_states_d e d H) = true.
  Proof.
    intros e d H. destruct H. unfold int_states_d. cbv zeta.
    destruct (closed_check (regex2dfa e) (build_states (regex2dfa e))) eqn:E;
      [exact E |].
    apply saturate_closed;
      [apply dedup_NoDup | apply dedup_In, start_in_build_states].
  Qed.

  (** [accept[id s] = nullable s]. *)
  Definition build_accept (states : list regex) : list bool :=
    map nullable states.

  (** The id of the initial (canonicalized) state. *)
  Definition build_start (d : DFA) (states : list regex) : N :=
    match d with
    | (start, _, _) => idx_of_map start (index_map states)
    end.

  (** Builds the full interned representation for rule [e]: initial state id
      plus the [(matrix, accept, orig)] triple threaded as [Delta]. *)
  (** Interning plus its closure certificate. The boolean is [true] exactly
      when the interned table is closed (see [closed_check]); a caller that
      needs unconditional soundness branches on it and falls back to the
      un-interned lexer when it is [false]. [intern] below is this with the
      certificate discarded, so the two never diverge. *)
  Definition intern_full (e : regex)
    : bool * (N * (vec (vec N) * vec bool * regex)) :=
    let d := regex2dfa e in
    let states := int_states_d e d eq_refl in
    let m := build_matrix d states in
    let acc := build_accept states in
    let sid := build_start d states in
    (closed_check d states,
     (sid, (vec_of_list (map vec_of_list m), vec_of_list acc, e))).

  Definition intern (e : regex) : N * (vec (vec N) * vec bool * regex) :=
    (* [regex2dfa] runs [fill_Table_all_bin], the (expensive) Brzozowski
       table fill.  It is evaluated ONCE here and threaded into the three
       builders below; each of them used to call [regex2dfa e] itself, so
       interning a rule paid the full table-construction cost three times
       over. *)
    let d := regex2dfa e in
    let states := int_states_d e d eq_refl in
    let m := build_matrix d states in
    let acc := build_accept states in
    let sid := build_start d states in
    (sid, (vec_of_list (map vec_of_list m), vec_of_list acc, e)).

  (** [intern] is [intern_full] with the certificate discarded, so a proof
      conditioned on [fst (intern_full e) = true] transfers to [intern]. *)
  Lemma intern_full_intern : forall e, snd (intern_full e) = intern e.
  Proof. reflexivity. Qed.

  (** One interned transition step: O(1) double array index. *)
  Definition step (m : vec (vec N)) (id : N) (a : Sigma) : N :=
    vec_nth (vec_nth m id vnil) (code a) 0%N.

  (** Whether interned state [id] is accepting. *)
  Definition is_accepting (acc : vec bool) (id : N) : bool :=
    vec_nth acc id false.

  (** * Simulation

      [gamma states] reads an id back as the regex it stands for. The two
      lemmas below say the interned operations commute with it: a [step] on
      ids is a [trans_target] on regexes, and [is_accepting] on an id is
      [nullable] on its regex. Together with [trans_target_equiv] they reduce
      the interned automaton to the regex-keyed one. *)
  Definition gamma (states : list regex) (id : N) : regex :=
    dfa_nth states id EmptySet.

  (** An id is *valid* when it names a slot of the state list. Validity is
      what the closure certificate propagates: [step] maps valid ids to valid
      ids (see [step_gamma] below). *)
  Definition valid (states : list regex) (id : N) : Prop :=
    (id < N.of_nat (length states))%N.

  Lemma valid_In : forall states id, valid states id -> In (gamma states id) states.
  Proof. intros. apply dfa_nth_In. exact H. Qed.

  (** [step] on the built matrix is [trans_target] on the denoted regexes,
      and it keeps the id valid -- the latter is exactly what the closure
      certificate buys, and is why an id can be iterated. *)
  Lemma step_gamma : forall start T o states id a,
      closed_check (start, T, o) states = true ->
      valid states id ->
      gamma states (step (vec_of_list (map vec_of_list
                            (build_matrix (start, T, o) states))) id a)
      = trans_target T (gamma states id) a
      /\ valid states (step (vec_of_list (map vec_of_list
                              (build_matrix (start, T, o) states))) id a).
  Proof.
    intros start T o states id a Hc Hv.
    unfold step, gamma, valid in *.
    assert (Hm : (id < N.of_nat (length (build_matrix (start, T, o) states)))%N).
    { unfold build_matrix. rewrite length_map. exact Hv. }
    (* peel the two [vec] layers back to [dfa_nth] on the underlying lists *)
    rewrite vec_nth_of_list.
    rewrite (dfa_nth_map_lt _ _ vec_of_list _ _ [] vnil) by exact Hm.
    rewrite vec_nth_of_list.
    (* select the row for [gamma states id] *)
    unfold build_matrix.
    rewrite (dfa_nth_map_lt _ _ _ _ _ EmptySet []) by exact Hv.
    (* select the column for [a]; [code a] is in range by [code_lt] *)
    rewrite (dfa_nth_map_lt _ _ _ _ _ a 0%N) by apply code_lt.
    rewrite code_nth.
    (* the certificate says that cell's target is listed *)
    assert (Hin : In (dfa_nth states id EmptySet) states) by (apply dfa_nth_In; exact Hv).
    simpl in Hc. apply andb_prop in Hc as (_ & Hall).
    rewrite forallb_forall in Hall. specialize (Hall _ Hin).
    rewrite forallb_forall in Hall. specialize (Hall a (Sigma_finite a)).
    apply mem_states_nth in Hall as (Hnth & Hlt).
    split; [exact Hnth | exact Hlt].
  Qed.

  (** [is_accepting] on an id is [nullable] on its regex. No closure needed:
      the accept vector is [map nullable states] and the two defaults agree
      ([nullable EmptySet = false]). *)
  Lemma is_accepting_gamma : forall states id,
      is_accepting (vec_of_list (build_accept states)) id
      = nullable (gamma states id).
  Proof.
    intros states id. unfold is_accepting, build_accept, gamma.
    rewrite vec_nth_of_list.
    exact (dfa_nth_map _ _ nullable states id EmptySet).
  Qed.

  (** * Running a whole string

      [run] iterates the interned [step]; [run_re] iterates [trans_target] on
      the regexes those ids denote. The two theorems below say [run] tracks
      [run_re] (given the certificate), and that [run_re] lands on a regex
      matching exactly the residual language -- so testing [nullable] at the
      end decides membership. *)
  Fixpoint run (m : vec (vec N)) (id : N) (bs : list Sigma) : N :=
    match bs with
    | [] => id
    | b :: bs' => run m (step m id b) bs'
    end.

  Fixpoint run_re (T : Table) (s : regex) (bs : list Sigma) : regex :=
    match bs with
    | [] => s
    | b :: bs' => run_re T (trans_target T s b) bs'
    end.

  Theorem run_gamma : forall start T o states bs id,
      closed_check (start, T, o) states = true ->
      valid states id ->
      gamma states (run (vec_of_list (map vec_of_list
                           (build_matrix (start, T, o) states))) id bs)
      = run_re T (gamma states id) bs
      /\ valid states (run (vec_of_list (map vec_of_list
                              (build_matrix (start, T, o) states))) id bs).
  Proof.
    intros start T o states bs. induction bs as [| b bs IH]; intros id Hc Hv.
    - split; [reflexivity | exact Hv].
    - cbn [run run_re]. destruct (step_gamma _ _ _ _ id b Hc Hv) as (Hstep & Hval).
      destruct (IH _ Hc Hval) as (Hrun & Hval').
      rewrite Hrun, Hstep. split; [reflexivity | exact Hval'].
  Qed.

  (** After consuming [bs], the state reached matches exactly the strings [z]
      for which [bs ++ z] matched the state we started from.

      Phrasing the invariant semantically (rather than as [re_equiv] to
      [derivative_list bs s]) is what keeps this short: it needs only
      [trans_target_equiv] and [der_match] at each step, and no congruence of
      [derivative] with respect to [re_equiv]. *)
  Theorem run_re_spec : forall T bs s z,
      derived T ->
      (exp_match z (run_re T s bs) <-> exp_match (bs ++ z) s).
  Proof.
    intros T bs. induction bs as [| b bs IH]; intros s z Hd; simpl.
    - reflexivity.
    - rewrite (IH (trans_target T s b) z Hd).
      rewrite (trans_target_equiv T s b Hd (bs ++ z)).
      split; apply der_match.
  Qed.

  (** Membership decided at the end of a run: the accept bit of the state
      reached after [bs] is [true] exactly when [bs] matched the start. *)
  Corollary run_re_nullable : forall T bs s,
      derived T -> (nullable (run_re T s bs) = true <-> exp_match bs s).
  Proof.
    intros T bs s Hd. rewrite nullable_bridge'.
    rewrite (run_re_spec T bs s [] Hd). rewrite app_nil_r. reflexivity.
  Qed.

  (** * Top-level correctness of the interned automaton

      [int_accepts e bs] is exactly what a lexer state built by [intern e]
      computes after consuming [bs]: run the matrix from the start id, read
      the accept bit. The theorem below says that bit decides [exp_match],
      provided the closure certificate for [e] came out [true]. *)
  Definition int_accepts (e : regex) (bs : list Sigma) : bool :=
    match intern e with
    | (sid, (m, acc, _)) => is_accepting acc (run m sid bs)
    end.

  (** The certificate also pins the start id down: it names a real slot, and
      that slot holds the start state itself. *)
  Lemma closed_check_start_valid : forall start T o states,
      closed_check (start, T, o) states = true ->
      gamma states (idx_of_map start (index_map states)) = start
      /\ valid states (idx_of_map start (index_map states)).
  Proof.
    intros start T o states Hc.
    simpl in Hc. apply andb_prop in Hc as (Hs & _).
    apply mem_states_nth. exact Hs.
  Qed.

  (** The simulation argument, over an arbitrary certified state list: the
      accept bit the interned run lands on decides [exp_match]. *)
  Lemma int_accepts_states : forall e bs states,
      closed_check (regex2dfa e) states = true ->
      (is_accepting (vec_of_list (build_accept states))
         (run (vec_of_list (map vec_of_list (build_matrix (regex2dfa e) states)))
              (build_start (regex2dfa e) states) bs) = true
       <-> exp_match bs e).
  Proof.
    intros e bs states Hc.
    destruct (regex2dfa e) as [[start T] o] eqn:E.
    (* the table [regex2dfa] built is derived, and its start state is [canon e] *)
    apply transition_Table_correct in E as (Hd & _ & Hce).
    cbn [build_start].
    destruct (closed_check_start_valid _ _ _ _ Hc) as (Hg & Hv).
    (* accept bit = [nullable] of the regex the final id denotes *)
    rewrite is_accepting_gamma.
    destruct (run_gamma _ _ _ _ bs _ Hc Hv) as (Hrun & _).
    rewrite Hrun, Hg.
    (* and that regex decides membership in the start state's language *)
    rewrite (run_re_nullable T bs start Hd).
    rewrite <- Hce. apply canon_equiv.
  Qed.

  Theorem int_accepts_match : forall e bs,
      fst (intern_full e) = true ->
      (int_accepts e bs = true <-> exp_match bs e).
  Proof.
    intros e bs Hc. unfold int_accepts, intern. cbn [fst] in Hc.
    apply int_accepts_states, Hc.
  Qed.

  (** The certificate is now discharged rather than assumed: [intern] runs on
      the saturated state list, which [int_states_closed] proves closed.  So
      the interned automaton is unconditionally correct, and the un-interned
      fallback a caller used to need is unreachable. *)
  Corollary intern_closed : forall e, fst (intern_full e) = true.
  Proof. intros e. apply int_states_closed. Qed.

  Theorem int_accepts_correct : forall e bs,
      int_accepts e bs = true <-> exp_match bs e.
  Proof. intros e bs. apply int_accepts_match, intern_closed. Qed.

End IntDFAFn.
