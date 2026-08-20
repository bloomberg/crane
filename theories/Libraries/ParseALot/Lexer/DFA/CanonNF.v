(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorted.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import Table.

(** * Normal forms and a finite superset of the canonical derivative states.

    Purpose: [Lexer.Memo.IntLexer] interns a rule's DFA into an [N]-indexed
    matrix. That is only sound if the interned state list is *closed* under
    [fun s a => canon (derivative a s)] -- every arrow of the matrix has to
    point at a state that is itself in the list. This file builds the
    ingredient that closure needs: a computable, finite set [Superset e] that
    provably contains every state reachable from [canon e].

    Why a superset rather than a bound. [DFA.Brzozowski_bound] is
    [2^(regex_length e + 1) - 1], and the argument it was designed around is
    the Antimirov one: a regex of length [n] has at most [n] partial-derivative
    terms, states are unions of those, hence at most [2^n + 1] states (see the
    comment on [DFA.Brzozowski_bound']). That argument does *not* apply to this
    [canon]: [canon] does not distribute [App] over [Union] (and does not
    recurse under [Star] at all, see [Table.canon]), so the union-atoms of a
    state are not partial-derivative terms and their number is *not* bounded by
    [regex_length]. Measured counterexample: the reachable states of
    [Star ((a|b)* a (a|b)^7)] -- length 35 -- use 264 distinct atoms.

    So we do not bound the state count at all. Nothing downstream needs a
    bound; closure is enough, and closure only needs *some* computable finite
    superset. [Superset] below is astronomically larger than the true state
    set (it is a nested powerset construction, so its size is a tower in the
    star-nesting depth of [e]) and it is never evaluated -- it exists solely as
    the well-founded measure that makes the closure computation terminate. *)
Module CanonNFFn (R : Regex.T) (TabTy : Table R).

  Import R.
  Import R.Ty.
  Import R.Defs.Regexes.
  Import R.Defs.Helpers.
  Module Export Defs := Table.DefsFn R TabTy.

  (** ** Sorted, duplicate-free atom lists

      Union-atoms are kept in [re_compare] order with duplicates removed --
      the same discipline [canon] itself imposes via [merge]. Keeping the
      superset's atom lists sorted is what lets [sublists] (which enumerates
      sub*sequences*, in order) cover every sorted subset. *)
  Fixpoint rinsert (x : regex) (l : list regex) : list regex :=
    match l with
    | [] => [x]
    | h :: t =>
      match re_compare x h with
      | Eq => l
      | Lt => x :: l
      | Gt => h :: rinsert x t
      end
    end.

  Definition rsort (l : list regex) : list regex := fold_right rinsert [] l.

  (** All subsequences of [l], in order. For a sorted [l] this enumerates
      every sorted subset. *)
  Fixpoint sublists (l : list regex) : list (list regex) :=
    match l with
    | [] => [[]]
    | h :: t => let s := sublists t in map (cons h) s ++ s
    end.

  (** Every union that can be formed from the atoms [l]. *)
  Definition unions (l : list regex) : list regex := map IterUnion (sublists l).

  (** Concatenation of two already-canonical regexes, exactly as [canon]'s
      [App] case forms it (identities for [EmptySet]/[EmptyStr], otherwise
      right-associated factor lists). *)
  Definition appcat (x y : regex) : regex :=
    match x, y with
    | EmptySet, _ => EmptySet
    | _, EmptySet => EmptySet
    | EmptyStr, _ => y
    | _, EmptyStr => x
    | _, _ => IterApp (mkIterApp' x ++ mkIterApp' y)
    end.

  (** [Atoms e]: a superset of the union-atoms of every state reachable from
      [canon e] in *at least one* derivative step.

      The two interesting cases are [App] and [Star], and they have the same
      shape: because [canon] does not distribute [App] over [Union], the left
      factor of a resulting atom is a whole *state* of the sub-regex (an
      arbitrary union of its atoms), not a single atom. Hence [unions (...)]
      rather than a plain [map] -- this is precisely the step that makes the
      construction a nested powerset, and the step whose omission makes the
      Antimirov bound fail.

      [EmptyStr] is added to each left-factor pool because a derivative can
      cancel the left factor entirely ([appcat EmptyStr y = y]), and the
      [Union]/[App] cases fold in the *states* of the right operand
      ([mkIterUnion' (canon b)]) because a derivative can also collapse to the
      right operand untouched. Both gaps were found by exhaustive testing of
      every regex up to size 7 over a two-letter alphabet.

      Three details are there for the *proof* rather than for coverage, and
      all three are invariants of the form "every element of the pool is a
      canonical union-atom":

      - each product [appcat u (canon b)] is broken back into its union-atoms
        by [mkIterUnion'], because [appcat EmptyStr (canon b)] is [canon b],
        which may itself be a [Union];
      - [EmptySet] is filtered out of each left-factor pool ([mkpool]), so an
        [IterUnion] of a sub*set* of the pool is canonical -- [Canonical]
        forbids [EmptySet] under a [Union]. Nothing is lost: a residual that
        collapses to [EmptySet] contributes [appcat EmptySet _ = EmptySet],
        which [AllAtoms] carries anyway;
      - the [Star] arm uses [canon (Star r)] rather than [Star r], since
        [Star EmptySet] and [Star EmptyStr] are not canonical.

      Each is validated in [models/atoms2.py] against the previous, coverage-
      equivalent definition. *)
  Definition notEmptySet (y : regex) : bool :=
    if Regexes.regex_dec y EmptySet then false else true.

  (** The left-factor pool of a subterm: its atom list, sorted, without
      [EmptySet], plus [EmptyStr]. *)
  Definition mkpool (base : list regex) : list regex :=
    rinsert EmptyStr (filter notEmptySet (rsort base)).

  Fixpoint Atoms (e : regex) : list regex :=
    match e with
    | EmptySet => []
    | EmptyStr => []
    | Char _ => [EmptyStr]
    | Union a b => rsort (Atoms a ++ Atoms b)
    | App a b =>
      let la := mkpool (mkIterUnion' (canon a) ++ Atoms a) in
      rsort (flat_map (fun u => mkIterUnion' (appcat u (canon b))) (unions la)
             ++ mkIterUnion' (canon b) ++ Atoms b)
    | Star r =>
      let sr := canon (Star r) in
      let lr := mkpool (mkIterUnion' (canon r) ++ Atoms r) in
      rsort (mkIterUnion' sr
             ++ flat_map (fun u => mkIterUnion' (appcat u sr)) (unions lr))
    end.

  (** [AllAtoms e]: [Atoms e] together with the atoms of the start state
      itself, which no derivative step need ever produce (for [Char c] the
      start state is [Char c], while [Atoms (Char c) = [EmptyStr]]).

      [EmptySet] is included because the empty union is *represented* as
      [EmptySet] rather than as the empty atom list: [mkIterUnion' EmptySet]
      is [[EmptySet]], not [[]], so the dead state would otherwise fail to be
      covered by [canon_in_Superset] even though [IterUnion [] = EmptySet] is
      in [Superset e]. Enlarging a superset is free. *)
  Definition AllAtoms (e : regex) : list regex :=
    rinsert EmptySet (rsort (mkIterUnion' (canon e) ++ Atoms e)).

  (** The finite superset of reachable states: every union of a subset of
      [AllAtoms e]. Closure of the reachable set inside [Superset e] is what
      licenses interning; [length (Superset e)] is the termination measure for
      the closure computation. *)
  Definition Superset (e : regex) : list regex := unions (AllAtoms e).

  (** ** Basic facts about the list machinery *)

  Lemma rinsert_In : forall x l y,
      In y (rinsert x l) <-> y = x \/ In y l.
  Proof.
    intros x l. induction l as [| h t IH]; intros y.
    - simpl. split; intros H; destruct H as [H | H];
        solve [left; congruence | contradiction].
    - simpl. destruct (re_compare x h) eqn:E.
      + apply re_compare_eq in E. subst h. simpl. split; intros H.
        * right. exact H.
        * destruct H as [H | H]; [left; congruence | exact H].
      + simpl. split; intros H; destruct H as [H | H];
          solve [left; congruence | right; exact H].
      + simpl. split; intros H.
        * destruct H as [H | H]; [right; left; congruence |].
          apply IH in H. destruct H as [H | H];
            [left; exact H | right; right; exact H].
        * destruct H as [H | [H | H]].
          -- right. apply IH. left. exact H.
          -- left. congruence.
          -- right. apply IH. right. exact H.
  Qed.

  Lemma rsort_In : forall l y, In y (rsort l) <-> In y l.
  Proof.
    induction l as [| h t IH]; intros y.
    - simpl. reflexivity.
    - unfold rsort in *. simpl. rewrite rinsert_In. rewrite IH.
      split; intros H; destruct H as [H | H];
        solve [left; congruence | right; exact H].
  Qed.

  (** [sublists] really does enumerate every subsequence. *)
  Lemma sublists_In_nil : forall l, In [] (sublists l).
  Proof.
    induction l as [| h t IH]; simpl; auto.
    apply in_or_app. right. exact IH.
  Qed.

  Lemma sublists_cons : forall h t s,
      In s (sublists t) -> In (h :: s) (sublists (h :: t)).
  Proof.
    intros h t s H. simpl. apply in_or_app. left.
    apply in_map. exact H.
  Qed.

  Lemma sublists_skip : forall h t s,
      In s (sublists t) -> In s (sublists (h :: t)).
  Proof.
    intros h t s H. simpl. apply in_or_app. right. exact H.
  Qed.

  (** Every union of a subsequence of [l] is in [unions l]. *)
  Lemma unions_In : forall l s,
      In s (sublists l) -> In (IterUnion s) (unions l).
  Proof.
    intros l s H. unfold unions. apply in_map. exact H.
  Qed.

  (** ** The strict order induced by [re_compare]

      [Regex.Sigma] supplies only [compareT_eq] and [compareT_trans] -- there
      is deliberately no antisymmetry parameter. It is not needed: antisymmetry
      is *derivable*, because [comparison] has exactly three values and the
      other two are ruled out ([Eq] would force [x = y], and [Gt] both ways
      would force [re_compare x x = Gt] against [re_compare_eq']). So the whole
      order theory below is available for an arbitrary alphabet without
      strengthening the module type. *)
  Definition rlt (x y : regex) : Prop := re_compare x y = Lt.

  Lemma re_compare_Gt_Lt : forall x y,
      re_compare x y = Gt -> re_compare y x = Lt.
  Proof.
    intros x y H. destruct (re_compare y x) eqn:E.
    - apply re_compare_eq in E. subst. rewrite re_compare_eq' in H. discriminate.
    - reflexivity.
    - pose proof (re_compare_trans Gt _ _ _ H E) as C.
      rewrite re_compare_eq' in C. discriminate.
  Qed.

  Lemma rlt_irrefl : forall x, ~ rlt x x.
  Proof.
    intros x H. unfold rlt in H. rewrite re_compare_eq' in H. discriminate.
  Qed.

  Lemma rlt_trans : forall x y z, rlt x y -> rlt y z -> rlt x z.
  Proof. intros x y z Hxy Hyz. exact (re_compare_trans Lt _ _ _ Hxy Hyz). Qed.

  Lemma rlt_asym : forall x y, rlt x y -> rlt y x -> False.
  Proof. intros x y H1 H2. apply (rlt_irrefl x). eapply rlt_trans; eauto. Qed.

  (** ** [rinsert]/[rsort] produce sorted lists

      Sortedness is not cosmetic: [sublists] enumerates sub*sequences*, so it
      only covers an arbitrary subset when the ambient list is sorted and the
      subset is sorted the same way. That is exactly the gap
      [sorted_incl_sublists] below closes. *)
  Lemma rinsert_sorted : forall x l,
      StronglySorted rlt l -> StronglySorted rlt (rinsert x l).
  Proof.
    intros x l. induction l as [| h t IH]; intros Hs.
    - simpl. apply SSorted_cons; [apply SSorted_nil | apply Forall_nil].
    - inversion Hs as [| h' t' Hst Hfa]; subst. simpl.
      destruct (re_compare x h) eqn:E.
      + exact Hs.
      + apply SSorted_cons; [exact Hs |].
        apply Forall_cons; [exact E |].
        eapply Forall_impl; [| exact Hfa].
        intros y Hy. eapply rlt_trans; [exact E | exact Hy].
      + apply SSorted_cons; [apply IH; exact Hst |].
        apply Forall_forall. intros y Hy.
        apply rinsert_In in Hy. destruct Hy as [Hy | Hy].
        * subst y. apply re_compare_Gt_Lt. exact E.
        * eapply Forall_forall in Hfa; eauto.
  Qed.

  Lemma rsort_sorted : forall l, StronglySorted rlt (rsort l).
  Proof.
    induction l as [| h t IH]; simpl.
    - apply SSorted_nil.
    - apply rinsert_sorted. exact IH.
  Qed.

  (** The completeness half of [sublists]: a sorted sub*set* of a sorted list
      is one of its subsequences. *)
  Lemma sorted_incl_sublists : forall l s,
      StronglySorted rlt l ->
      StronglySorted rlt s ->
      incl s l ->
      In s (sublists l).
  Proof.
    induction l as [| h t IH]; intros s Hl Hs Hincl.
    - destruct s as [| r s'].
      + simpl. left. reflexivity.
      + exfalso. apply (Hincl r). left. reflexivity.
    - inversion Hl as [| h' t' Hlt Hlfa]; subst.
      destruct s as [| r s'].
      + apply sublists_In_nil.
      + inversion Hs as [| r' s'' Hss Hsfa]; subst.
        destruct (Regexes.regex_dec r h) as [Heq | Hne].
        * subst r. apply sublists_cons. apply IH; [exact Hlt | exact Hss |].
          intros y Hy.
          assert (Hyh : rlt h y) by (eapply Forall_forall in Hsfa; eauto).
          destruct (Hincl y (or_intror Hy)) as [Hy' | Hy'].
          -- exfalso. subst y. apply (rlt_irrefl h). exact Hyh.
          -- exact Hy'.
        * apply sublists_skip. apply IH; [exact Hlt | exact Hs |].
          intros y Hy.
          destruct (Hincl y Hy) as [Hy' | Hy']; [| exact Hy'].
          exfalso. subst y.
          (* [h] is in [s], and [r] -- the head of [s] -- is in [t], so the two
             sortedness facts contradict each other. *)
          assert (Hrt : In r t).
          { destruct (Hincl r (or_introl eq_refl)) as [Hr | Hr];
              [exfalso; apply Hne; symmetry; exact Hr | exact Hr]. }
          assert (Hhr : rlt h r) by (eapply Forall_forall in Hlfa; eauto).
          destruct Hy as [Hy | Hy].
          -- apply Hne. exact Hy.
          -- assert (Hrh : rlt r h) by (eapply Forall_forall in Hsfa; eauto).
             eapply rlt_asym; eauto.
  Qed.

  (** Consequently [unions l] contains the union of *every* subset of a sorted
      [l], not merely of its subsequences. *)
  Corollary unions_complete : forall l s,
      StronglySorted rlt l ->
      StronglySorted rlt s ->
      incl s l ->
      In (IterUnion s) (unions l).
  Proof.
    intros l s Hl Hs Hincl. apply unions_In.
    apply sorted_incl_sublists; assumption.
  Qed.

  Lemma AllAtoms_sorted : forall e, StronglySorted rlt (AllAtoms e).
  Proof. intros e. apply rinsert_sorted. apply rsort_sorted. Qed.

  Lemma AllAtoms_In : forall e y,
      In y (AllAtoms e) <->
      y = EmptySet \/ In y (mkIterUnion' (canon e)) \/ In y (Atoms e).
  Proof.
    intros e y. unfold AllAtoms. rewrite rinsert_In, rsort_In.
    split; intros H.
    - destruct H as [H | H]; [left; exact H |].
      apply in_app_or in H. destruct H; [right; left | right; right]; assumption.
    - destruct H as [H | [H | H]]; [left; exact H | |];
        right; apply in_or_app; [left | right]; assumption.
  Qed.

  (** The form in which the closure proof will use the superset: a state is in
      [Superset e] as soon as its atom list is sorted and drawn from
      [AllAtoms e]. Both obligations are discharged by the [canon] normal-form
      theory (a canonical state's atoms are [merge]-sorted) plus the closure
      theorem (they are drawn from [AllAtoms e]). *)
  Corollary Superset_intro : forall e s,
      StronglySorted rlt s ->
      incl s (AllAtoms e) ->
      In (IterUnion s) (Superset e).
  Proof.
    intros e s Hs Hincl. unfold Superset.
    apply unions_complete; [apply AllAtoms_sorted | exact Hs | exact Hincl].
  Qed.

  (** ** [canon] normal form

      [Superset_intro] needs a canonical state's atom list to be sorted. That
      cannot be proved on its own, because [mkIterUnion'] only flattens the
      *right* spine of a union: [mkIterUnion' (Union (Union a b) c)] is
      [[Union a b; c]], and [IterUnion] does not invert it. So the invariant
      has to be strengthened -- a canonical regex's atoms are sorted *and*
      none of them is itself a [Union] -- and the two halves are proved
      together. *)
  Definition notUnion (r : regex) : Prop :=
    match r with
    | Union _ _ => False
    | _ => True
    end.

  Definition UnionNF (e : regex) : Prop :=
    StronglySorted rlt (mkIterUnion' e) /\ Forall notUnion (mkIterUnion' e).

  Lemma mkIterUnion'_nonempty : forall e, mkIterUnion' e <> [].
  Proof. intros e. destruct e; simpl; discriminate. Qed.

  Lemma mkIterApp'_nonempty : forall e, mkIterApp' e <> [].
  Proof. intros e. destruct e; simpl; discriminate. Qed.

  Lemma mkIterUnion'_notUnion : forall e, notUnion e -> mkIterUnion' e = [e].
  Proof. intros e H. destruct e; simpl; try reflexivity. contradiction. Qed.

  Lemma UnionNF_notUnion : forall e, notUnion e -> UnionNF e.
  Proof.
    intros e H. unfold UnionNF. rewrite mkIterUnion'_notUnion by exact H.
    split.
    - apply SSorted_cons; [apply SSorted_nil | apply Forall_nil].
    - apply Forall_cons; [exact H | apply Forall_nil].
  Qed.

  (** [IterUnion] inverts [mkIterUnion'] exactly on the lists the invariant
      describes: non-empty, and free of nested unions. *)
  Lemma mkIterUnion'_IterUnion : forall l,
      l <> [] -> Forall notUnion l -> mkIterUnion' (IterUnion l) = l.
  Proof.
    induction l as [| x t IH]; intros Hne Hfa.
    - contradiction.
    - inversion Hfa as [| x' t' Hx Ht]; subst.
      destruct t as [| y t'].
      + simpl. apply mkIterUnion'_notUnion. exact Hx.
      + simpl IterUnion. simpl mkIterUnion'. f_equal.
        apply IH; [discriminate | exact Ht].
  Qed.

  (** The other direction of the round trip, which needs no side condition at
      all: [mkIterUnion'] peels the right spine and [IterUnion] rebuilds it. *)
  Lemma IterUnion_cons : forall a l,
      l <> [] -> IterUnion (a :: l) = Union a (IterUnion l).
  Proof. intros a l H. destruct l; [contradiction | reflexivity]. Qed.

  Lemma IterUnion_mkIterUnion' : forall x, IterUnion (mkIterUnion' x) = x.
  Proof.
    induction x as [ | | c | x1 _ x2 _ | x1 _ x2 IH2 | r _ ];
      try reflexivity.
    simpl mkIterUnion'.
    rewrite IterUnion_cons by apply mkIterUnion'_nonempty.
    rewrite IH2. reflexivity.
  Qed.

  (** ** [merge] preserves the invariant *)

  Lemma merge_nonempty : forall l1 l2 h t,
      l1 = h :: t -> merge l1 l2 <> [].
  Proof.
    intros l1 l2 h t Heq C.
    assert (Hin : In h (merge l1 l2)) by (apply merge_In; left; subst; left; auto).
    rewrite C in Hin. contradiction.
  Qed.

  Lemma merge_Forall : forall (P : regex -> Prop) l1 l2,
      Forall P l1 -> Forall P l2 -> Forall P (merge l1 l2).
  Proof.
    intros P l1 l2 H1 H2. apply Forall_forall. intros y Hy.
    apply merge_In in Hy. destruct Hy as [Hy | Hy];
      [eapply Forall_forall in H1 | eapply Forall_forall in H2]; eauto.
  Qed.

  Lemma merge_sorted' : forall n l1 l2,
      length l1 + length l2 <= n ->
      StronglySorted rlt l1 -> StronglySorted rlt l2 ->
      StronglySorted rlt (merge l1 l2).
  Proof.
    induction n as [| n IH]; intros l1 l2 Hn H1 H2.
    - destruct l1; [| simpl in Hn; lia].
      rewrite merge_nil1. exact H2.
    - destruct l1 as [| h1 t1]; [rewrite merge_nil1; exact H2 |].
      destruct l2 as [| h2 t2]; [rewrite merge_nil2; exact H1 |].
      inversion H1 as [| a1 b1 Hs1 Hf1]; subst.
      inversion H2 as [| a2 b2 Hs2 Hf2]; subst.
      pose proof (merge_cons t1 t2 h1 h2) as Hmc.
      simpl in Hn. destruct (re_compare h1 h2) eqn:E; rewrite Hmc.
      + apply IH; [simpl; lia | exact H1 | exact Hs2].
      + apply SSorted_cons; [apply IH; [simpl; lia | exact Hs1 | exact H2] |].
        apply Forall_forall. intros y Hy. apply merge_In in Hy.
        destruct Hy as [Hy | [Hy | Hy]].
        * eapply Forall_forall in Hf1; eauto.
        * subst y. exact E.
        * eapply rlt_trans; [exact E |].
          eapply Forall_forall in Hf2; eauto.
      + apply SSorted_cons; [apply IH; [simpl; lia | exact H1 | exact Hs2] |].
        assert (Eh : rlt h2 h1) by (apply re_compare_Gt_Lt; exact E).
        apply Forall_forall. intros y Hy. apply merge_In in Hy.
        destruct Hy as [[Hy | Hy] | Hy].
        * subst y. exact Eh.
        * eapply rlt_trans; [exact Eh |].
          eapply Forall_forall in Hf1; eauto.
        * eapply Forall_forall in Hf2; eauto.
  Qed.

  Lemma merge_sorted : forall l1 l2,
      StronglySorted rlt l1 -> StronglySorted rlt l2 ->
      StronglySorted rlt (merge l1 l2).
  Proof. intros l1 l2 H1 H2. eapply merge_sorted'; eauto. Qed.

  (** ** Case analysis on [canon]

      [canon]'s [Union]/[App] arms are nested matches on the two recursive
      results, so a direct induction fans out into dozens of goals. These
      three lemmas do that fan-out once, by brute force, and expose the
      handful of shapes the result can actually take. *)
  Lemma canon_Union_cases : forall e1 e2,
      canon (Union e1 e2) = canon e1
      \/ canon (Union e1 e2) = canon e2
      \/ canon (Union e1 e2)
         = IterUnion (merge (mkIterUnion' (canon e1)) (mkIterUnion' (canon e2))).
  Proof.
    intros e1 e2. simpl.
    destruct (canon e1); destruct (canon e2); auto.
  Qed.

  Lemma canon_App_cases : forall e1 e2,
      canon (App e1 e2) = EmptySet
      \/ canon (App e1 e2) = canon e1
      \/ canon (App e1 e2) = canon e2
      \/ canon (App e1 e2)
         = IterApp (mkIterApp' (canon e1) ++ mkIterApp' (canon e2)).
  Proof.
    intros e1 e2. simpl.
    destruct (canon e1); destruct (canon e2); auto.
  Qed.

  Lemma canon_Star_cases : forall r,
      canon (Star r) = EmptyStr \/ canon (Star r) = Star r.
  Proof. intros r. destruct r; simpl; auto. Qed.

  (** An [IterApp] over two or more factors is headed by [App], hence is never
      a [Union]. This is what makes [canon]'s [App] arm satisfy the
      invariant. *)
  Lemma IterApp_notUnion : forall l,
      2 <= length l -> notUnion (IterApp l).
  Proof.
    intros l H. destruct l as [| a [| b t]]; simpl in *; try lia; try exact I.
  Qed.

  Lemma canon_App_notUnion : forall e1 e2, notUnion (canon (App e1 e2)) \/
      canon (App e1 e2) = canon e1 \/ canon (App e1 e2) = canon e2.
  Proof.
    intros e1 e2.
    destruct (canon_App_cases e1 e2) as [H | [H | [H | H]]];
      [left; rewrite H; exact I | right; left; exact H | right; right; exact H |].
    left. rewrite H. apply IterApp_notUnion.
    rewrite length_app.
    pose proof (mkIterApp'_nonempty (canon e1)) as N1.
    pose proof (mkIterApp'_nonempty (canon e2)) as N2.
    destruct (mkIterApp' (canon e1)); [contradiction |].
    destruct (mkIterApp' (canon e2)); [contradiction |].
    simpl. lia.
  Qed.

  (** The normal-form theorem: every canonical regex has a sorted,
      nesting-free atom list. *)
  Theorem canon_UnionNF : forall e, UnionNF (canon e).
  Proof.
    induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | r IHr ].
    - apply UnionNF_notUnion. exact I.
    - apply UnionNF_notUnion. exact I.
    - apply UnionNF_notUnion. exact I.
    - (* App *)
      destruct (canon_App_notUnion e1 e2) as [H | [H | H]].
      + apply UnionNF_notUnion. exact H.
      + rewrite H. exact IH1.
      + rewrite H. exact IH2.
    - (* Union *)
      destruct (canon_Union_cases e1 e2) as [H | [H | H]]; rewrite H;
        [exact IH1 | exact IH2 |].
      destruct IH1 as [S1 F1]. destruct IH2 as [S2 F2].
      assert (Hne : merge (mkIterUnion' (canon e1)) (mkIterUnion' (canon e2)) <> []).
      { pose proof (mkIterUnion'_nonempty (canon e1)) as N1.
        destruct (mkIterUnion' (canon e1)) as [| h t]; [contradiction |].
        eapply merge_nonempty. reflexivity. }
      assert (Hfa : Forall notUnion
                      (merge (mkIterUnion' (canon e1)) (mkIterUnion' (canon e2))))
        by (apply merge_Forall; assumption).
      unfold UnionNF. rewrite mkIterUnion'_IterUnion by assumption.
      split; [apply merge_sorted; assumption | exact Hfa].
    - (* Star *)
      destruct (canon_Star_cases r) as [H | H]; rewrite H;
        apply UnionNF_notUnion; exact I.
  Qed.

  (** ** Closure, compositional half

      A state is a union of atoms, and [derivative] distributes over [Union].
      So the closure obligation reduces from "every reachable state" to "every
      single atom": if each atom's derivative stays inside [Atoms e], so does
      every state's. These lemmas perform that reduction. *)
  Notation atoms x := (mkIterUnion' (canon x)).

  Lemma atoms_incl_Union : forall u v,
      incl (atoms (Union u v)) (atoms u ++ atoms v).
  Proof.
    intros u v.
    destruct (canon_Union_cases u v) as [H | [H | H]]; rewrite H.
    - apply incl_appl. apply incl_refl.
    - apply incl_appr. apply incl_refl.
    - rewrite mkIterUnion'_IterUnion.
      + intros y Hy. apply merge_In in Hy. apply in_or_app. exact Hy.
      + pose proof (mkIterUnion'_nonempty (canon u)) as N.
        destruct (mkIterUnion' (canon u)) as [| h t]; [contradiction |].
        eapply merge_nonempty. reflexivity.
      + apply merge_Forall; [apply (canon_UnionNF u) | apply (canon_UnionNF v)].
  Qed.

  Lemma atoms_incl_smart_union : forall u v,
      incl (atoms (smart_union u v)) (atoms u ++ atoms v).
  Proof.
    intros u v. unfold smart_union.
    destruct u; destruct v;
      solve [ apply atoms_incl_Union
            | apply incl_appl; apply incl_refl
            | apply incl_appr; apply incl_refl ].
  Qed.

  (** The reduction itself: the atoms of a state's derivative are covered by
      the atoms of its atoms' derivatives. *)
  Lemma atoms_deriv_IterUnion : forall a l,
      l <> [] ->
      Forall notUnion l ->
      incl (atoms (derivative a (IterUnion l)))
           (concat (map (fun x => atoms (derivative a x)) l)).
  Proof.
    intros a l. induction l as [| h t IH]; intros Hne Hfa; [contradiction |].
    inversion Hfa as [| h' t' Hh Ht]; subst.
    destruct t as [| y t'].
    - simpl. rewrite app_nil_r. apply incl_refl.
    - rewrite IterUnion_cons by discriminate.
      simpl derivative.
      eapply incl_tran; [apply atoms_incl_smart_union |].
      simpl concat. apply incl_app.
      + apply incl_appl. apply incl_refl.
      + apply incl_appr. apply IH; [discriminate | exact Ht].
  Qed.

  (** The form the closure proof consumes: a canonical state lands in
      [Superset e] as soon as its atoms are drawn from [AllAtoms e]. All the
      sortedness side conditions are now discharged. *)
  Corollary canon_in_Superset : forall e s,
      incl (mkIterUnion' (canon s)) (AllAtoms e) ->
      In (canon s) (Superset e).
  Proof.
    intros e s Hincl.
    destruct (canon_UnionNF s) as [Hsort _].
    pose proof (Superset_intro e _ Hsort Hincl) as Hin.
    rewrite IterUnion_mkIterUnion' in Hin. exact Hin.
  Qed.

  (** ** [canon] is idempotent

      The closure proof cannot avoid a double [canon]: [Atoms (App a b)] forms
      atoms as [appcat u (canon b)], and taking a derivative of such an atom
      re-canonicalizes a term that already contains [canon b]. So
      [canon (canon x) = canon x] is a prerequisite, not a convenience.

      It is proved through a [Canonical] predicate -- an explicit description
      of canon's image -- rather than directly, because a direct induction has
      no handle on canon's nested matches. Note what [Canonical] does *not*
      say about [Star r]: only that [r] is neither [EmptySet] nor [EmptyStr].
      [canon] does not recurse under [Star] (that arm is commented out in
      [Table.canon]), so [r] itself need not be canonical, and demanding that
      it be would make the predicate false of canon's own output. *)
  Definition notApp (r : regex) : Prop :=
    match r with
    | App _ _ => False
    | _ => True
    end.

  Fixpoint Canonical (e : regex) : Prop :=
    match e with
    | EmptySet => True
    | EmptyStr => True
    | Char _ => True
    | Star r => r <> EmptySet /\ r <> EmptyStr
    | App e1 e2 =>
      Canonical e1 /\ Canonical e2 /\ notApp e1
      /\ e1 <> EmptySet /\ e1 <> EmptyStr
      /\ e2 <> EmptySet /\ e2 <> EmptyStr
    | Union e1 e2 =>
      Canonical e1 /\ Canonical e2 /\ notUnion e1
      /\ e1 <> EmptySet /\ e2 <> EmptySet
      /\ (forall y, In y (mkIterUnion' e2) -> rlt e1 y)
    end.

  Definition AppElt (x : regex) : Prop :=
    Canonical x /\ notApp x /\ x <> EmptySet /\ x <> EmptyStr.

  Definition UnElt (x : regex) : Prop :=
    Canonical x /\ notUnion x /\ x <> EmptySet.

  (** *** Round-trip and splitting helpers for [IterApp] *)

  Lemma mkIterApp'_notApp : forall e, notApp e -> mkIterApp' e = [e].
  Proof. intros e H. destruct e; simpl; try reflexivity. contradiction. Qed.

  Lemma IterApp_cons : forall a l,
      l <> [] -> IterApp (a :: l) = App a (IterApp l).
  Proof. intros a l H. destruct l; [contradiction | reflexivity]. Qed.

  Lemma IterApp_mkIterApp' : forall x, IterApp (mkIterApp' x) = x.
  Proof.
    induction x as [ | | c | x1 _ x2 IH2 | x1 _ x2 _ | r _ ]; try reflexivity.
    simpl mkIterApp'.
    rewrite IterApp_cons by apply mkIterApp'_nonempty.
    rewrite IH2. reflexivity.
  Qed.

  Lemma IterApp_split : forall x y,
      notApp x -> IterApp (mkIterApp' x ++ mkIterApp' y) = App x y.
  Proof.
    intros x y H. rewrite (mkIterApp'_notApp x H). simpl app.
    rewrite IterApp_cons by apply mkIterApp'_nonempty.
    rewrite IterApp_mkIterApp'. reflexivity.
  Qed.

  Lemma merge_singleton_lt : forall x l,
      l <> [] -> (forall y, In y l -> rlt x y) -> merge [x] l = x :: l.
  Proof.
    intros x l Hne Hlt. destruct l as [| h t]; [contradiction |].
    pose proof (merge_cons [] t x h) as Hmc.
    assert (E : re_compare x h = Lt) by (apply Hlt; left; reflexivity).
    rewrite E in Hmc. rewrite Hmc. rewrite merge_nil1. reflexivity.
  Qed.

  Lemma IterUnion_split : forall x y,
      notUnion x ->
      (forall z, In z (mkIterUnion' y) -> rlt x z) ->
      IterUnion (merge (mkIterUnion' x) (mkIterUnion' y)) = Union x y.
  Proof.
    intros x y Hnu Hlt. rewrite (mkIterUnion'_notUnion x Hnu).
    rewrite merge_singleton_lt by (auto using mkIterUnion'_nonempty).
    rewrite IterUnion_cons by apply mkIterUnion'_nonempty.
    rewrite IterUnion_mkIterUnion'. reflexivity.
  Qed.

  Lemma app_nonempty : forall (l1 l2 : list regex), l1 <> [] -> l1 ++ l2 <> [].
  Proof. intros l1 l2 H. destruct l1; [contradiction | discriminate]. Qed.

  (** *** [Canonical] is closed under the constructions [canon] uses

      These two introduction lemmas exist so the proofs below never have to
      [simpl] the goal: [simpl Canonical] also reduces the [IterApp]/
      [IterUnion] call sitting inside it, which then no longer matches the
      lemmas about those functions. *)
  Lemma Canonical_App_intro : forall x y,
      Canonical x -> Canonical y -> notApp x ->
      x <> EmptySet -> x <> EmptyStr -> y <> EmptySet -> y <> EmptyStr ->
      Canonical (App x y).
  Proof. intros. simpl. repeat split; assumption. Qed.

  Lemma Canonical_Union_intro : forall x y,
      Canonical x -> Canonical y -> notUnion x ->
      x <> EmptySet -> y <> EmptySet ->
      (forall z, In z (mkIterUnion' y) -> rlt x z) ->
      Canonical (Union x y).
  Proof. intros. simpl. repeat split; assumption. Qed.

  Lemma UnElt_notUnion : forall x, UnElt x -> notUnion x.
  Proof. intros x H. destruct H as (_ & N & _). exact N. Qed.

  Lemma mkIterApp'_elts : forall x,
      Canonical x -> x <> EmptySet -> x <> EmptyStr -> Forall AppElt (mkIterApp' x).
  Proof.
    induction x as [ | | c | x1 _ x2 IH2 | x1 _ x2 _ | r _ ];
      intros HC H0 H1; try congruence; simpl mkIterApp'.
    - (* Char *)
      apply Forall_cons; [| apply Forall_nil].
      unfold AppElt. split; [exact HC |]. split; [exact I |]. split; discriminate.
    - (* App: recurse down the right spine *)
      simpl in HC. destruct HC as (C1 & C2 & N1 & E1 & E2 & E3 & E4).
      apply Forall_cons.
      + unfold AppElt. split; [exact C1 |]. split; [exact N1 |]. split; assumption.
      + apply IH2; assumption.
    - apply Forall_cons; [| apply Forall_nil].
      unfold AppElt. split; [exact HC |]. split; [exact I |]. split; discriminate.
    - apply Forall_cons; [| apply Forall_nil].
      unfold AppElt. split; [exact HC |]. split; [exact I |]. split; discriminate.
  Qed.

  Lemma IterApp_neq : forall l,
      l <> [] -> Forall AppElt l ->
      IterApp l <> EmptySet /\ IterApp l <> EmptyStr.
  Proof.
    intros l Hne Hfa. destruct l as [| x [| y t]]; [contradiction | |].
    - inversion Hfa as [| a b Hx _]; subst.
      destruct Hx as (_ & _ & A & B). simpl. split; assumption.
    - simpl. split; discriminate.
  Qed.

  Lemma Canonical_IterApp : forall l,
      l <> [] -> Forall AppElt l -> Canonical (IterApp l).
  Proof.
    induction l as [| x t IH]; intros Hne Hfa; [contradiction |].
    inversion Hfa as [| a b Hx Ht]; subst.
    destruct Hx as (Cx & Nx & Ax & Bx).
    destruct t as [| y t'].
    - simpl. exact Cx.
    - rewrite IterApp_cons by discriminate.
      destruct (IterApp_neq (y :: t') ltac:(discriminate) Ht) as [P1 P2].
      apply Canonical_App_intro; try assumption.
      apply IH; [discriminate | exact Ht].
  Qed.

  Lemma mkIterUnion'_elts : forall x,
      Canonical x -> x <> EmptySet -> Forall UnElt (mkIterUnion' x).
  Proof.
    induction x as [ | | c | x1 _ x2 _ | x1 _ x2 IH2 | r _ ];
      intros HC H0; try congruence; simpl mkIterUnion'.
    - (* EmptyStr: unlike mkIterApp'_elts there is no [x <> EmptyStr]
         hypothesis here, so this case is real rather than vacuous. *)
      apply Forall_cons; [| apply Forall_nil].
      unfold UnElt. split; [exact HC |]. split; [exact I |]. discriminate.
    - (* Char *)
      apply Forall_cons; [| apply Forall_nil].
      unfold UnElt. split; [exact HC |]. split; [exact I |]. discriminate.
    - (* App *)
      apply Forall_cons; [| apply Forall_nil].
      unfold UnElt. split; [exact HC |]. split; [exact I |]. discriminate.
    - (* Union: recurse down the right spine *)
      simpl in HC. destruct HC as (C1 & C2 & N1 & E1 & E2 & Hlt).
      apply Forall_cons.
      + unfold UnElt. split; [exact C1 |]. split; [exact N1 |]. exact E1.
      + apply IH2; assumption.
    - (* Star *)
      apply Forall_cons; [| apply Forall_nil].
      unfold UnElt. split; [exact HC |]. split; [exact I |]. discriminate.
  Qed.

  Lemma IterUnion_neq : forall l,
      l <> [] -> Forall UnElt l -> IterUnion l <> EmptySet.
  Proof.
    intros l Hne Hfa. destruct l as [| x [| y t]]; [contradiction | |].
    - inversion Hfa as [| a b Hx _]; subst.
      destruct Hx as (_ & _ & A). simpl. exact A.
    - simpl. discriminate.
  Qed.

  Lemma Canonical_IterUnion : forall l,
      l <> [] -> Forall UnElt l -> StronglySorted rlt l -> Canonical (IterUnion l).
  Proof.
    induction l as [| x t IH]; intros Hne Hfa Hs; [contradiction |].
    inversion Hfa as [| a b Hx Ht]; subst.
    destruct Hx as (Cx & Nx & Ex).
    inversion Hs as [| a' b' Hst Hfs]; subst.
    destruct t as [| y t'].
    - simpl. exact Cx.
    - rewrite IterUnion_cons by discriminate.
      assert (Hnu : Forall notUnion (y :: t')).
      { eapply Forall_impl; [apply UnElt_notUnion | exact Ht]. }
      apply Canonical_Union_intro; try assumption.
      + apply IH; [discriminate | exact Ht | exact Hst].
      + apply IterUnion_neq; [discriminate | exact Ht].
      + intros z Hz.
        rewrite mkIterUnion'_IterUnion in Hz by (assumption || discriminate).
        eapply Forall_forall in Hfs; eauto.
  Qed.

  Lemma Canonical_sorted : forall x,
      Canonical x -> StronglySorted rlt (mkIterUnion' x).
  Proof.
    induction x as [ | | c | x1 _ x2 _ | x1 _ x2 IH2 | r _ ]; intros HC;
      simpl mkIterUnion';
      try (apply SSorted_cons; [apply SSorted_nil | apply Forall_nil]).
    simpl in HC. destruct HC as (C1 & C2 & N1 & E1 & E2 & Hlt).
    apply SSorted_cons; [apply IH2; exact C2 | apply Forall_forall; exact Hlt].
  Qed.

  (** *** [canon]'s output is [Canonical] *)

  (** Sharper versions of [canon_{App,Union}_cases] that also record the side
      conditions holding in the general arm. Stated so the general arm's
      result stays *folded* as an [IterApp]/[IterUnion] application: reducing
      it (as [simpl canon] would) leaves a term the lemmas about those
      functions no longer match. *)
  Lemma canon_App_shape : forall e1 e2,
      canon (App e1 e2) = EmptySet
      \/ canon (App e1 e2) = canon e1
      \/ canon (App e1 e2) = canon e2
      \/ (canon (App e1 e2)
          = IterApp (mkIterApp' (canon e1) ++ mkIterApp' (canon e2))
          /\ canon e1 <> EmptySet /\ canon e1 <> EmptyStr
          /\ canon e2 <> EmptySet /\ canon e2 <> EmptyStr).
  Proof.
    intros e1 e2. simpl canon.
    destruct (canon e1); destruct (canon e2);
      try (left; reflexivity);
      try (right; left; reflexivity);
      try (right; right; left; reflexivity);
      right; right; right; repeat split; try reflexivity; discriminate.
  Qed.

  Lemma canon_Union_shape : forall e1 e2,
      canon (Union e1 e2) = canon e1
      \/ canon (Union e1 e2) = canon e2
      \/ (canon (Union e1 e2)
          = IterUnion (merge (mkIterUnion' (canon e1)) (mkIterUnion' (canon e2)))
          /\ canon e1 <> EmptySet /\ canon e2 <> EmptySet).
  Proof.
    intros e1 e2. simpl canon.
    destruct (canon e1); destruct (canon e2);
      try (left; reflexivity);
      try (right; left; reflexivity);
      right; right; repeat split; try reflexivity; discriminate.
  Qed.

  Lemma Canonical_canon_App : forall e1 e2,
      Canonical (canon e1) -> Canonical (canon e2) -> Canonical (canon (App e1 e2)).
  Proof.
    intros e1 e2 H1 H2.
    destruct (canon_App_shape e1 e2) as [H | [H | [H | (H & A1 & A2 & B1 & B2)]]];
      rewrite H.
    - exact I.
    - exact H1.
    - exact H2.
    - apply Canonical_IterApp.
      + apply app_nonempty. apply mkIterApp'_nonempty.
      + apply Forall_app. split; apply mkIterApp'_elts; assumption.
  Qed.

  Lemma Canonical_canon_Union : forall e1 e2,
      Canonical (canon e1) -> Canonical (canon e2) -> Canonical (canon (Union e1 e2)).
  Proof.
    intros e1 e2 H1 H2.
    destruct (canon_Union_shape e1 e2) as [H | [H | (H & A1 & A2)]]; rewrite H.
    - exact H1.
    - exact H2.
    - apply Canonical_IterUnion.
      + pose proof (mkIterUnion'_nonempty (canon e1)) as N.
        destruct (mkIterUnion' (canon e1)) as [| h t]; [contradiction |].
        eapply merge_nonempty. reflexivity.
      + apply merge_Forall; apply mkIterUnion'_elts; assumption.
      + apply merge_sorted; apply Canonical_sorted; assumption.
  Qed.

  Theorem canon_Canonical : forall e, Canonical (canon e).
  Proof.
    induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | r IHr ];
      try exact I.
    - apply Canonical_canon_App; assumption.
    - apply Canonical_canon_Union; assumption.
    - destruct r; simpl; try exact I; split; discriminate.
  Qed.

  (** *** [canon] is the identity on [Canonical] regexes *)

  (** When neither side is degenerate, [canon] takes its general arm. Stated
      separately from the [_shape] lemmas because here the *conclusion* is the
      general arm rather than one disjunct among several, which is what the
      identity proof needs. *)
  Lemma canon_App_general : forall e1 e2,
      canon e1 <> EmptySet -> canon e1 <> EmptyStr ->
      canon e2 <> EmptySet -> canon e2 <> EmptyStr ->
      canon (App e1 e2) = IterApp (mkIterApp' (canon e1) ++ mkIterApp' (canon e2)).
  Proof.
    intros e1 e2 A1 A2 B1 B2. revert A1 A2 B1 B2. simpl canon.
    destruct (canon e1); destruct (canon e2); intros A1 A2 B1 B2;
      try congruence; reflexivity.
  Qed.

  Lemma canon_Union_general : forall e1 e2,
      canon e1 <> EmptySet -> canon e2 <> EmptySet ->
      canon (Union e1 e2)
      = IterUnion (merge (mkIterUnion' (canon e1)) (mkIterUnion' (canon e2))).
  Proof.
    intros e1 e2 A1 B1. revert A1 B1. simpl canon.
    destruct (canon e1); destruct (canon e2); intros A1 B1;
      try congruence; reflexivity.
  Qed.

  Lemma Canonical_canon_id : forall x, Canonical x -> canon x = x.
  Proof.
    induction x as [ | | c | x1 IH1 x2 IH2 | x1 IH1 x2 IH2 | r _ ];
      intros HC; try reflexivity.
    - (* App *)
      simpl in HC. destruct HC as (C1 & C2 & N1 & E1 & E2 & E3 & E4).
      rewrite canon_App_general by (rewrite ?(IH1 C1), ?(IH2 C2); assumption).
      rewrite (IH1 C1), (IH2 C2).
      apply IterApp_split. exact N1.
    - (* Union *)
      simpl in HC. destruct HC as (C1 & C2 & N1 & E1 & E2 & Hlt).
      rewrite canon_Union_general by (rewrite ?(IH1 C1), ?(IH2 C2); assumption).
      rewrite (IH1 C1), (IH2 C2).
      apply IterUnion_split; [exact N1 | exact Hlt].
    - (* Star *)
      simpl in HC. destruct HC as (E1 & E2).
      destruct r; simpl; congruence.
  Qed.

  Theorem canon_idem : forall e, canon (canon e) = canon e.
  Proof. intros e. apply Canonical_canon_id. apply canon_Canonical. Qed.


  (** ** [canon] versus the smart constructors

      [appcat] was written to mirror [canon]'s [App] arm, and it does so
      exactly; the same holds one level up for the smart constructors that
      [derivative] builds its results with. These two equations are what let
      the closure proof push [canon] through a derivative step and land on
      the [appcat]-shaped terms that [Atoms] is built from. *)

  Lemma canon_App_appcat : forall e1 e2,
      canon (App e1 e2) = appcat (canon e1) (canon e2).
  Proof.
    intros e1 e2. simpl. unfold appcat.
    destruct (canon e1); destruct (canon e2); reflexivity.
  Qed.

  (** [appcat] absorbs and cancels on already-canonical arguments, so the
      degenerate arms of [smart_app] agree with it. *)
  Lemma appcat_EmptySet_r : forall x, appcat x EmptySet = EmptySet.
  Proof. intros x. unfold appcat. destruct x; reflexivity. Qed.

  Lemma appcat_EmptyStr_l : forall y, appcat EmptyStr y = y.
  Proof. intros y. unfold appcat. destruct y; reflexivity. Qed.

  Lemma appcat_EmptyStr_r : forall x, appcat x EmptyStr = x.
  Proof. intros x. unfold appcat. destruct x; reflexivity. Qed.

  Theorem canon_smart_app : forall x y,
      canon (smart_app x y) = appcat (canon x) (canon y).
  Proof.
    intros x y.
    destruct x; destruct y; try apply canon_App_appcat; simpl smart_app;
      simpl (canon EmptySet); simpl (canon EmptyStr);
      try reflexivity;
      first [ rewrite appcat_EmptySet_r; reflexivity
            | rewrite appcat_EmptyStr_l; reflexivity
            | rewrite appcat_EmptyStr_r; reflexivity ].
  Qed.

  Lemma canon_Union_unfold : forall e1 e2,
      canon (Union e1 e2) =
      match canon e1, canon e2 with
      | EmptySet, ec2 => ec2
      | ec1, EmptySet => ec1
      | ec1, ec2 => IterUnion (merge (mkIterUnion' ec1) (mkIterUnion' ec2))
      end.
  Proof. reflexivity. Qed.

  Lemma canon_Union_EmptySet_l : forall y, canon (Union EmptySet y) = canon y.
  Proof. intros y. rewrite canon_Union_unfold. reflexivity. Qed.

  Lemma canon_Union_EmptySet_r : forall x, canon (Union x EmptySet) = canon x.
  Proof.
    intros x. rewrite canon_Union_unfold.
    simpl (canon EmptySet). destruct (canon x); reflexivity.
  Qed.

  Theorem canon_smart_union : forall x y,
      canon (smart_union x y) = canon (Union x y).
  Proof.
    intros x y. destruct x; destruct y; cbn [smart_union]; try reflexivity;
      rewrite ?canon_Union_EmptySet_l, ?canon_Union_EmptySet_r; reflexivity.
  Qed.

  Corollary canon_smart_app' : forall x y,
      canon (smart_app x y) = canon (App x y).
  Proof.
    intros x y. rewrite canon_smart_app, canon_App_appcat. reflexivity.
  Qed.

  (** ** [derivative] respects [canon] through the plain constructors

      [canon (App _ _)] and [canon (Union _ _)] look only at their operands'
      canonical forms, so a derivative step may be read off the *plain*
      constructors and the smart ones forgotten. Unlike the refuted
      commutation lemma these carry no side conditions at all: they say
      nothing about pushing [canon] *inside* a derivative, only about the
      shell [derivative] builds around its recursive calls. *)

  Lemma canon_App_cong : forall a b a' b',
      canon a = canon a' -> canon b = canon b' ->
      canon (App a b) = canon (App a' b').
  Proof.
    intros a b a' b' Ha Hb. rewrite !canon_App_appcat, Ha, Hb. reflexivity.
  Qed.

  Lemma canon_Union_cong : forall a b a' b',
      canon a = canon a' -> canon b = canon b' ->
      canon (Union a b) = canon (Union a' b').
  Proof.
    intros a b a' b' Ha Hb. rewrite !canon_Union_unfold, Ha, Hb. reflexivity.
  Qed.

  Theorem canon_deriv_App : forall c u v,
      canon (derivative c (App u v)) =
      canon (if nullable u
             then Union (App (derivative c u) v) (derivative c v)
             else App (derivative c u) v).
  Proof.
    intros c u v. simpl derivative. destruct (nullable u).
    - rewrite canon_smart_union.
      apply canon_Union_cong; [apply canon_smart_app' | reflexivity].
    - apply canon_smart_app'.
  Qed.

  Theorem canon_deriv_Union : forall c u v,
      canon (derivative c (Union u v)) =
      canon (Union (derivative c u) (derivative c v)).
  Proof. intros c u v. simpl derivative. apply canon_smart_union. Qed.

  Theorem canon_deriv_Star : forall c r,
      canon (derivative c (Star r)) = canon (App (derivative c r) (Star r)).
  Proof. intros c r. simpl derivative. apply canon_smart_app'. Qed.


  (** ** [appcat] algebra

      [appcat] is a monoid operation on canonical regexes, with [EmptyStr] as
      unit and [EmptySet] as zero. Associativity is what lets the closure
      proof re-bracket a state [appcat u v] as [appcat f (appcat rest v)] and
      recurse down [u]'s factor spine -- the step the naive per-atom lemma
      gets wrong, because [canon] does not distribute [App] over [Union] and
      so a residual left factor must stay whole. *)

  Lemma AppElt_notApp : forall x, AppElt x -> notApp x.
  Proof. intros x (_ & H & _). exact H. Qed.

  (** The [App] analogue of [mkIterUnion'_IterUnion]. *)
  Lemma mkIterApp'_IterApp : forall l,
      l <> [] -> Forall notApp l -> mkIterApp' (IterApp l) = l.
  Proof.
    induction l as [| x t IH]; intros Hne Hfa; [contradiction |].
    inversion Hfa as [| x' t' Hx Ht]; subst.
    destruct t as [| y t'].
    - simpl. apply mkIterApp'_notApp. exact Hx.
    - rewrite IterApp_cons by discriminate. simpl mkIterApp'. f_equal.
      apply IH; [discriminate | exact Ht].
  Qed.

  Lemma Canonical_appcat : forall x y,
      Canonical x -> Canonical y -> Canonical (appcat x y).
  Proof.
    intros x y Hx Hy.
    rewrite <- (Canonical_canon_id x Hx) at 1.
    rewrite <- (Canonical_canon_id y Hy) at 1.
    rewrite <- canon_App_appcat. apply canon_Canonical.
  Qed.

  Lemma canon_appcat_id : forall x y,
      Canonical x -> Canonical y -> canon (appcat x y) = appcat x y.
  Proof.
    intros x y Hx Hy. apply Canonical_canon_id, Canonical_appcat; assumption.
  Qed.

  (** On non-degenerate canonical operands [appcat] is exactly factor-list
      concatenation. *)
  Lemma mkIterApp'_appcat : forall x y,
      Canonical x -> Canonical y ->
      x <> EmptySet -> x <> EmptyStr -> y <> EmptySet -> y <> EmptyStr ->
      mkIterApp' (appcat x y) = mkIterApp' x ++ mkIterApp' y.
  Proof.
    intros x y Cx Cy X0 X1 Y0 Y1.
    assert (Hfa : Forall AppElt (mkIterApp' x ++ mkIterApp' y)).
    { apply Forall_app. split; apply mkIterApp'_elts; assumption. }
    assert (Hne : mkIterApp' x ++ mkIterApp' y <> [])
      by (apply app_nonempty, mkIterApp'_nonempty).
    assert (E : appcat x y = IterApp (mkIterApp' x ++ mkIterApp' y)).
    { unfold appcat. destruct x; try congruence; destruct y; congruence. }
    rewrite E. apply mkIterApp'_IterApp; [exact Hne |].
    eapply Forall_impl; [apply AppElt_notApp | exact Hfa].
  Qed.

  Lemma appcat_neq : forall x y,
      Canonical x -> Canonical y ->
      x <> EmptySet -> x <> EmptyStr -> y <> EmptySet -> y <> EmptyStr ->
      appcat x y <> EmptySet /\ appcat x y <> EmptyStr.
  Proof.
    intros x y Cx Cy X0 X1 Y0 Y1.
    assert (E : appcat x y = IterApp (mkIterApp' x ++ mkIterApp' y)).
    { unfold appcat. destruct x; try congruence; destruct y; congruence. }
    rewrite E. apply IterApp_neq.
    - apply app_nonempty, mkIterApp'_nonempty.
    - apply Forall_app. split; apply mkIterApp'_elts; assumption.
  Qed.

  Theorem appcat_assoc : forall x y z,
      Canonical x -> Canonical y -> Canonical z ->
      appcat (appcat x y) z = appcat x (appcat y z).
  Proof.
    intros x y z Cx Cy Cz.
    (* The degenerate operands are handled by the unit and zero laws. *)
    destruct (regex_dec x EmptySet) as [-> | X0].
    { unfold appcat at 2 3. reflexivity. }
    destruct (regex_dec x EmptyStr) as [-> | X1].
    { rewrite !appcat_EmptyStr_l. reflexivity. }
    destruct (regex_dec y EmptySet) as [-> | Y0].
    { rewrite appcat_EmptySet_r. unfold appcat at 3.
      rewrite appcat_EmptySet_r. reflexivity. }
    destruct (regex_dec y EmptyStr) as [-> | Y1].
    { rewrite appcat_EmptyStr_r, appcat_EmptyStr_l. reflexivity. }
    destruct (regex_dec z EmptySet) as [-> | Z0].
    { rewrite !appcat_EmptySet_r. reflexivity. }
    destruct (regex_dec z EmptyStr) as [-> | Z1].
    { rewrite !appcat_EmptyStr_r. reflexivity. }
    (* All six factors non-degenerate: both sides are the concatenated
       factor list. *)
    destruct (appcat_neq x y Cx Cy X0 X1 Y0 Y1) as (XY0 & XY1).
    destruct (appcat_neq y z Cy Cz Y0 Y1 Z0 Z1) as (YZ0 & YZ1).
    assert (Cxy : Canonical (appcat x y)) by (apply Canonical_appcat; assumption).
    assert (Cyz : Canonical (appcat y z)) by (apply Canonical_appcat; assumption).
    assert (E1 : appcat (appcat x y) z
                 = IterApp (mkIterApp' (appcat x y) ++ mkIterApp' z)).
    { unfold appcat at 1. destruct (appcat x y); try congruence;
        destruct z; congruence. }
    assert (E2 : appcat x (appcat y z)
                 = IterApp (mkIterApp' x ++ mkIterApp' (appcat y z))).
    { unfold appcat at 1. destruct x; try congruence;
        destruct (appcat y z); congruence. }
    rewrite E1, E2.
    rewrite (mkIterApp'_appcat x y), (mkIterApp'_appcat y z) by assumption.
    rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma appcat_notApp : forall x y,
      notApp x ->
      x <> EmptySet -> x <> EmptyStr -> y <> EmptySet -> y <> EmptyStr ->
      appcat x y = App x y.
  Proof.
    intros x y Hna X0 X1 Y0 Y1. unfold appcat.
    destruct x; try congruence; try contradiction;
      destruct y; try congruence; apply IterApp_split; exact Hna.
  Qed.


  (** ** The chain rule for a derivative under a right context

      [LeftRes c u] is the list of *left residuals* of [u] after reading [c]:
      the left factors that a derivative of [appcat u v] can leave standing in
      front of [v]. For a [u] with no [App] at the root there is exactly one,
      [canon (derivative c u)]; for [u = App f rest] the derivative may either
      consume [f] -- leaving [appcat (canon (derivative c f)) rest] -- or, when
      [f] is nullable, skip it and recurse into [rest].

      Splitting [canon (derivative c u)] into atoms and pairing each with [v]
      separately would be simpler, and is *false*: [canon] does not distribute
      [App] over [Union], so a residual that happens to be a union stays whole
      under the context. That is exactly what [LeftRes] keeps track of. *)
  Fixpoint LeftRes (c : Sigma) (u : regex) : list regex :=
    match u with
    | App f rest =>
      appcat (canon (derivative c f)) rest
      :: (if nullable f then LeftRes c rest else [])
    | _ => [canon (derivative c u)]
    end.

  Theorem deriv_appcat_chain : forall u v c,
      Canonical u -> u <> EmptySet -> u <> EmptyStr ->
      Canonical v -> v <> EmptySet -> v <> EmptyStr ->
      incl (atoms (derivative c (appcat u v)))
           (flat_map (fun s => atoms (appcat s v)) (LeftRes c u)
            ++ (if nullable u then atoms (derivative c v) else [])).
  Proof.
    intros u. induction u as [ | | ch | f _ rest IH | u1 _ u2 _ | r _ ];
      intros v c Cu U0 U1 Cv V0 V1; try congruence.
    - (* Char: no App at the root, and not nullable *)
      rewrite appcat_notApp by (assumption || exact I || discriminate).
      rewrite canon_deriv_App. simpl (nullable (Char ch)).
      cbn [LeftRes flat_map]. rewrite app_nil_r, app_nil_r.
      rewrite canon_App_appcat, (Canonical_canon_id v Cv).
      rewrite canon_appcat_id by (apply canon_Canonical || exact Cv).
      apply incl_refl.
    - (* App: peel the head factor and recurse down the spine *)
      simpl in Cu. destruct Cu as (Cf & Cr & Nf & F0 & F1 & R0 & R1).
      destruct (appcat_neq rest v Cr Cv R0 R1 V0 V1) as (W0 & W1).
      assert (Cw : Canonical (appcat rest v)) by (apply Canonical_appcat; assumption).
      assert (Hsplit : appcat (App f rest) v = App f (appcat rest v)).
      { rewrite <- (appcat_notApp f rest Nf F0 F1 R0 R1).
        rewrite appcat_assoc by assumption.
        apply appcat_notApp; assumption. }
      rewrite Hsplit, canon_deriv_App.
      (* the head residual, common to both branches *)
      assert (Hhead : atoms (App (derivative c f) (appcat rest v))
                      = atoms (appcat (appcat (canon (derivative c f)) rest) v)).
      { rewrite canon_App_appcat, (Canonical_canon_id _ Cw).
        rewrite appcat_assoc by (apply canon_Canonical || assumption).
        rewrite canon_appcat_id; [reflexivity | apply canon_Canonical | exact Cw]. }
      simpl (nullable (App f rest)).
      destruct (nullable f) eqn:Ef; cbn [LeftRes flat_map]; rewrite ?Ef.
      + replace (if negb (nullable rest) then false else true)
          with (nullable rest) by (destruct (nullable rest); reflexivity).
        eapply incl_tran; [apply atoms_incl_Union |].
        apply incl_app.
        * rewrite Hhead. intros y Hy. apply in_or_app. left.
          apply in_or_app. left. exact Hy.
        * eapply incl_tran; [apply IH; assumption |].
          apply incl_app.
          -- intros y Hy. apply in_or_app. left.
             apply in_or_app. right. exact Hy.
          -- apply incl_appr, incl_refl.
      + replace (if negb (nullable rest) then false else false)
          with false by (destruct (nullable rest); reflexivity).
        rewrite app_nil_r, app_nil_r, Hhead. apply incl_refl.
    - (* Union: no App at the root *)
      rewrite appcat_notApp by (assumption || exact I).
      rewrite canon_deriv_App.
      cbn [LeftRes flat_map]. rewrite app_nil_r.
      assert (Hhead : atoms (App (derivative c (Union u1 u2)) v)
                      = atoms (appcat (canon (derivative c (Union u1 u2))) v)).
      { rewrite canon_App_appcat, (Canonical_canon_id v Cv).
        rewrite canon_appcat_id; [reflexivity | apply canon_Canonical | exact Cv]. }
      destruct (nullable (Union u1 u2)).
      + eapply incl_tran; [apply atoms_incl_Union |].
        rewrite Hhead. apply incl_refl.
      + rewrite app_nil_r, Hhead. apply incl_refl.
    - (* Star: no App at the root, and always nullable *)
      rewrite appcat_notApp by (assumption || exact I || discriminate).
      rewrite canon_deriv_App. simpl (nullable (Star r)).
      cbn [LeftRes flat_map]. rewrite app_nil_r.
      assert (Hhead : atoms (App (derivative c (Star r)) v)
                      = atoms (appcat (canon (derivative c (Star r))) v)).
      { rewrite canon_App_appcat, (Canonical_canon_id v Cv).
        rewrite canon_appcat_id; [reflexivity | apply canon_Canonical | exact Cv]. }
      eapply incl_tran; [apply atoms_incl_Union |].
      rewrite Hhead. apply incl_refl.
  Qed.


  (** ** Closure, per-atom half

      With the compositional half above, the closure obligation is now
      per-atom:

        [AtomClosed e]: every atom of [AllAtoms e] has all the atoms of its
        derivative back in [AllAtoms e].

      This section discharges the leaf and [Union] cases and reduces the
      whole theorem to [App] and [Star], which are the two that the false
      commutation lemma blocks (see the closing note). *)
  Definition AtomClosed (e : regex) : Prop :=
    forall a x, In x (AllAtoms e) -> incl (atoms (derivative a x)) (AllAtoms e).

  (** [AllAtoms] membership, unfolded once and for all. *)
  Lemma In_AllAtoms : forall e x,
      In x (AllAtoms e) <-> x = EmptySet \/ In x (atoms e) \/ In x (Atoms e).
  Proof.
    intros e x. unfold AllAtoms.
    rewrite rinsert_In. rewrite rsort_In. rewrite in_app_iff. reflexivity.
  Qed.

  Lemma EmptySet_AllAtoms : forall e, In EmptySet (AllAtoms e).
  Proof. intros e. apply In_AllAtoms. left. reflexivity. Qed.

  (** The dead state's atoms are covered by every [AllAtoms]. *)
  Lemma incl_atoms_EmptySet : forall e, incl (atoms EmptySet) (AllAtoms e).
  Proof.
    intros e y Hy. simpl in Hy. destruct Hy as [Hy | []].
    subst y. apply EmptySet_AllAtoms.
  Qed.

  (** A sharper [canon_Union_cases]: the two collapsing branches only fire
      when the operand they drop canonicalises to [EmptySet], which is what
      lets the dropped operand's atoms still be accounted for. *)
  Lemma canon_Union_cases' : forall e1 e2,
      (canon e1 = EmptySet /\ canon (Union e1 e2) = canon e2)
      \/ (canon e2 = EmptySet /\ canon (Union e1 e2) = canon e1)
      \/ canon (Union e1 e2) = IterUnion (merge (atoms e1) (atoms e2)).
  Proof.
    intros e1 e2. simpl canon.
    destruct (canon e1) eqn:E1; destruct (canon e2) eqn:E2;
      solve [left; split; reflexivity
            | right; left; split; reflexivity
            | right; right; reflexivity].
  Qed.

  (** The [merge] branch really does expose both operands' atoms. *)
  Lemma atoms_Union_merge : forall e1 e2,
      canon (Union e1 e2) = IterUnion (merge (atoms e1) (atoms e2)) ->
      atoms (Union e1 e2) = merge (atoms e1) (atoms e2).
  Proof.
    intros e1 e2 H. rewrite H. apply mkIterUnion'_IterUnion.
    - pose proof (mkIterUnion'_nonempty (canon e1)) as N.
      destruct (mkIterUnion' (canon e1)) as [| h t]; [contradiction |].
      eapply merge_nonempty. reflexivity.
    - apply merge_Forall; [apply (canon_UnionNF e1) | apply (canon_UnionNF e2)].
  Qed.

  (** An operand's atoms survive into the union's, except that a collapsing
      operand contributes [EmptySet] instead. *)
  Lemma atoms_incl_Union_l : forall x y,
      incl (atoms x) (EmptySet :: atoms (Union x y)).
  Proof.
    intros x y z Hz.
    destruct (canon_Union_cases' x y) as [(H1 & _) | [(_ & H2) | H3]].
    - rewrite H1 in Hz. destruct Hz as [Hz | []]. left. congruence.
    - right. rewrite H2. exact Hz.
    - right. rewrite (atoms_Union_merge _ _ H3). apply merge_In. left. exact Hz.
  Qed.

  Lemma atoms_incl_Union_r : forall x y,
      incl (atoms y) (EmptySet :: atoms (Union x y)).
  Proof.
    intros x y z Hz.
    destruct (canon_Union_cases' x y) as [(_ & H1) | [(H2 & _) | H3]].
    - right. rewrite H1. exact Hz.
    - rewrite H2 in Hz. destruct Hz as [Hz | []]. left. congruence.
    - right. rewrite (atoms_Union_merge _ _ H3). apply merge_In. right. exact Hz.
  Qed.

  (** The residual-containment invariant: every left residual of [u] is a
      union of atoms of [canon (derivative c u)] (plus possibly [EmptySet],
      which a dead residual collapses to). So a hypothesis about the atoms of
      a *single* derivative step -- which is all [AtomClosed] gives -- already
      controls every residual [deriv_appcat_chain] can produce. *)
  Lemma LeftRes_atoms : forall u c,
      Canonical u -> u <> EmptySet -> u <> EmptyStr ->
      forall s, In s (LeftRes c u) ->
      incl (atoms s) (EmptySet :: atoms (derivative c u)).
  Proof.
    intros u. induction u as [ | | ch | f _ rest IH | u1 _ u2 _ | r _ ];
      intros c Cu U0 U1 s Hs; try congruence;
      (* Char, Union and Star have no [App] at the root: one residual, and it
         is the canonical derivative itself. *)
      try (cbn [LeftRes] in Hs; destruct Hs as [<- | []];
           rewrite canon_idem; apply incl_tl, incl_refl).
    (* App: the head residual, then the spine *)
    simpl in Cu. destruct Cu as (Cf & Cr & Nf & F0 & F1 & R0 & R1).
    assert (Hhead : atoms (appcat (canon (derivative c f)) rest)
                    = atoms (App (derivative c f) rest)).
    { rewrite canon_App_appcat, (Canonical_canon_id rest Cr).
      rewrite canon_appcat_id by (apply canon_Canonical || exact Cr).
      reflexivity. }
    rewrite canon_deriv_App.
    cbn [LeftRes] in Hs. destruct (nullable f) eqn:Ef; cbn in Hs.
    - destruct Hs as [<- | Hs].
      + rewrite Hhead. apply atoms_incl_Union_l.
      + eapply incl_tran; [apply (IH c Cr R0 R1 s Hs) |].
        intros z [<- | Hz]; [left; reflexivity | apply atoms_incl_Union_r; exact Hz].
    - destruct Hs as [<- | []].
      rewrite Hhead. apply incl_tl, incl_refl.
  Qed.

  (** [Atoms] of a [Union] is just the two operands' [Atoms]. *)
  Lemma In_Atoms_Union : forall e1 e2 x,
      In x (Atoms (Union e1 e2)) <-> In x (Atoms e1) \/ In x (Atoms e2).
  Proof.
    intros e1 e2 x. simpl Atoms. rewrite rsort_In. apply in_app_iff.
  Qed.

  (** Each operand's universe embeds in the [Union]'s. The collapsing cases
      are fine precisely because of [canon_Union_cases']: when an operand is
      dropped its [canon] is [EmptySet], whose only atom is [EmptySet]. *)
  Lemma AllAtoms_Union_l : forall e1 e2, incl (AllAtoms e1) (AllAtoms (Union e1 e2)).
  Proof.
    intros e1 e2 x Hx. apply In_AllAtoms in Hx as [-> | [Hx | Hx]].
    - apply EmptySet_AllAtoms.
    - destruct (canon_Union_cases' e1 e2) as [(H1 & _) | [(_ & H2) | H3]].
      + rewrite H1 in Hx. destruct Hx as [Hx | []]. subst x.
        apply EmptySet_AllAtoms.
      + apply In_AllAtoms. right. left. unfold AllAtoms. rewrite H2. exact Hx.
      + apply In_AllAtoms. right. left.
        rewrite (atoms_Union_merge _ _ H3). apply merge_In. left. exact Hx.
    - apply In_AllAtoms. right. right. apply In_Atoms_Union. left. exact Hx.
  Qed.

  Lemma AllAtoms_Union_r : forall e1 e2, incl (AllAtoms e2) (AllAtoms (Union e1 e2)).
  Proof.
    intros e1 e2 x Hx. apply In_AllAtoms in Hx as [-> | [Hx | Hx]].
    - apply EmptySet_AllAtoms.
    - destruct (canon_Union_cases' e1 e2) as [(_ & H1) | [(H2 & _) | H3]].
      + apply In_AllAtoms. right. left. unfold AllAtoms. rewrite H1. exact Hx.
      + rewrite H2 in Hx. destruct Hx as [Hx | []]. subst x.
        apply EmptySet_AllAtoms.
      + apply In_AllAtoms. right. left.
        rewrite (atoms_Union_merge _ _ H3). apply merge_In. right. exact Hx.
    - apply In_AllAtoms. right. right. apply In_Atoms_Union. right. exact Hx.
  Qed.

  (** ... and conversely the [Union]'s universe is covered by the operands'. *)
  Lemma AllAtoms_Union_split : forall e1 e2 x,
      In x (AllAtoms (Union e1 e2)) ->
      In x (AllAtoms e1) \/ In x (AllAtoms e2).
  Proof.
    intros e1 e2 x Hx. apply In_AllAtoms in Hx as [-> | [Hx | Hx]].
    - left. apply EmptySet_AllAtoms.
    - apply atoms_incl_Union in Hx. apply in_app_iff in Hx as [Hx | Hx];
        [left | right]; apply In_AllAtoms; right; left; exact Hx.
    - apply In_Atoms_Union in Hx as [Hx | Hx];
        [left | right]; apply In_AllAtoms; right; right; exact Hx.
  Qed.

  Theorem AtomClosed_Union : forall e1 e2,
      AtomClosed e1 -> AtomClosed e2 -> AtomClosed (Union e1 e2).
  Proof.
    intros e1 e2 H1 H2 a x Hx. apply AllAtoms_Union_split in Hx as [Hx | Hx].
    - eapply incl_tran; [apply H1; exact Hx | apply AllAtoms_Union_l].
    - eapply incl_tran; [apply H2; exact Hx | apply AllAtoms_Union_r].
  Qed.

  (** The leaves. [Atoms] is [[]] for the two constants and [[EmptyStr]] for
      a character, so the universes are small enough to enumerate. *)
  Theorem AtomClosed_EmptySet : AtomClosed EmptySet.
  Proof.
    intros a x Hx. apply In_AllAtoms in Hx as [-> | [Hx | []]].
    - apply incl_atoms_EmptySet.
    - destruct Hx as [Hx | []]. subst x. apply incl_atoms_EmptySet.
  Qed.

  Theorem AtomClosed_EmptyStr : AtomClosed EmptyStr.
  Proof.
    intros a x Hx. apply In_AllAtoms in Hx as [-> | [Hx | []]].
    - apply incl_atoms_EmptySet.
    - destruct Hx as [Hx | []]. subst x. apply incl_atoms_EmptySet.
  Qed.

  Theorem AtomClosed_Char : forall c, AtomClosed (Char c).
  Proof.
    intros c a x Hx. apply In_AllAtoms in Hx as [-> | [Hx | Hx]].
    - apply incl_atoms_EmptySet.
    - destruct Hx as [Hx | []]. subst x. simpl derivative.
      destruct (Ty.Sigma_dec c a); [| apply incl_atoms_EmptySet].
      intros y Hy. destruct Hy as [Hy | []]. subst y.
      apply In_AllAtoms. right. right. simpl. left. reflexivity.
    - destruct Hx as [Hx | []]. subst x. apply incl_atoms_EmptySet.
  Qed.

  (** ** The left-factor pools

      [App] and [Star] are the two cases where a derivative's atoms are
      products [appcat u v] whose left factor [u] is a whole *state* of the
      subterm, so the closure argument has to reason about [unions (pool a)]
      rather than about single atoms. This subsection establishes the one
      invariant that makes that possible: every pool element is a canonical
      union-atom, hence every [IterUnion] of a sorted subset of a pool is
      itself canonical. *)

  Definition pool (e : regex) : list regex :=
    mkpool (mkIterUnion' (canon e) ++ Atoms e).

  Lemma Atoms_App_unfold : forall a b,
      Atoms (App a b) =
      rsort (flat_map (fun u => mkIterUnion' (appcat u (canon b)))
                      (unions (pool a))
             ++ mkIterUnion' (canon b) ++ Atoms b).
  Proof. reflexivity. Qed.

  Lemma Atoms_Star_unfold : forall r,
      Atoms (Star r) =
      rsort (mkIterUnion' (canon (Star r))
             ++ flat_map (fun u => mkIterUnion' (appcat u (canon (Star r))))
                         (unions (pool r))).
  Proof. reflexivity. Qed.

  (** *** Singleton and empty subsets *)

  Lemma sublists_single : forall l y, In y l -> In [y] (sublists l).
  Proof.
    induction l as [| h t IH]; intros y Hy; [contradiction |].
    destruct Hy as [<- | Hy].
    - apply sublists_cons, sublists_In_nil.
    - apply sublists_skip, IH, Hy.
  Qed.

  Lemma unions_single : forall l y, In y l -> In y (unions l).
  Proof.
    intros l y H. pose proof (unions_In l [y] (sublists_single l y H)) as Hin.
    simpl in Hin. exact Hin.
  Qed.

  Lemma unions_EmptySet : forall l, In EmptySet (unions l).
  Proof.
    intros l. pose proof (unions_In l [] (sublists_In_nil l)) as Hin.
    simpl in Hin. exact Hin.
  Qed.

  (** *** Sublists inherit inclusion and sortedness *)

  Lemma sublists_incl : forall l s, In s (sublists l) -> incl s l.
  Proof.
    induction l as [| h t IH]; intros s Hs.
    - destruct Hs as [<- | []]. apply incl_refl.
    - simpl in Hs. apply in_app_or in Hs as [Hs | Hs].
      + apply in_map_iff in Hs as (s' & <- & Hs').
        apply incl_cons; [left; reflexivity |].
        apply incl_tl, IH, Hs'.
      + apply incl_tl, IH, Hs.
  Qed.

  Lemma sublists_sorted : forall l s,
      StronglySorted rlt l -> In s (sublists l) -> StronglySorted rlt s.
  Proof.
    induction l as [| h t IH]; intros s Hl Hs.
    - destruct Hs as [<- | []]. constructor.
    - inversion Hl as [| h' t' Hss Hfa]; subst.
      simpl in Hs. apply in_app_or in Hs as [Hs | Hs].
      + apply in_map_iff in Hs as (s' & <- & Hs').
        constructor; [apply IH; assumption |].
        apply Forall_forall. intros y Hy.
        rewrite Forall_forall in Hfa. apply Hfa.
        apply (sublists_incl t s' Hs'). exact Hy.
      + apply IH; assumption.
  Qed.

  (** *** [mkpool] *)

  Lemma filter_sorted : forall f l,
      StronglySorted rlt l -> StronglySorted rlt (filter f l).
  Proof.
    intros f. induction l as [| h t IH]; intros H; [constructor |].
    inversion H as [| h' t' Hss Hfa]; subst.
    simpl. destruct (f h).
    - constructor; [apply IH, Hss |].
      apply Forall_forall. intros y Hy. apply filter_In in Hy as (Hy & _).
      rewrite Forall_forall in Hfa. apply Hfa, Hy.
    - apply IH, Hss.
  Qed.

  Lemma mkpool_sorted : forall base, StronglySorted rlt (mkpool base).
  Proof.
    intros base. apply rinsert_sorted, filter_sorted, rsort_sorted.
  Qed.

  Lemma mkpool_In : forall base y,
      In y (mkpool base) <-> y = EmptyStr \/ (In y base /\ y <> EmptySet).
  Proof.
    intros base y. unfold mkpool. rewrite rinsert_In, filter_In, rsort_In.
    unfold notEmptySet. split.
    - intros [H | (H1 & H2)]; [left; exact H | right; split; [exact H1 |]].
      destruct (Regexes.regex_dec y EmptySet); [discriminate H2 | assumption].
    - intros [H | (H1 & H2)]; [left; exact H | right; split; [exact H1 |]].
      destruct (Regexes.regex_dec y EmptySet); [contradiction | reflexivity].
  Qed.

  (** *** Every pool element is a canonical union-atom *)

  Definition AtomOk (x : regex) : Prop := Canonical x /\ notUnion x.

  Lemma mkIterUnion'_ok : forall x, Canonical x -> Forall AtomOk (mkIterUnion' x).
  Proof.
    intros x HC. destruct (Regexes.regex_dec x EmptySet) as [-> | H0].
    - apply Forall_cons; [split; exact I | apply Forall_nil].
    - eapply Forall_impl; [| apply mkIterUnion'_elts; assumption].
      intros y (Cy & Ny & _). split; assumption.
  Qed.

  Lemma mkpool_ok : forall base,
      Forall AtomOk base ->
      Forall (fun x => AtomOk x /\ x <> EmptySet) (mkpool base).
  Proof.
    intros base H. apply Forall_forall. intros y Hy.
    apply mkpool_In in Hy as [-> | (Hy & Hne)].
    - split; [split; exact I | discriminate].
    - split; [| exact Hne]. rewrite Forall_forall in H. apply H, Hy.
  Qed.

  (** [unions] of such a pool consists of canonical regexes: the [EmptySet]
      filter is exactly what [Canonical]'s "no [EmptySet] under a [Union]"
      clause needs, and sortedness gives the strict-order clause. *)
  Lemma unions_Canonical : forall l u,
      StronglySorted rlt l ->
      Forall (fun x => AtomOk x /\ x <> EmptySet) l ->
      In u (unions l) -> Canonical u.
  Proof.
    intros l u Hl Hfa Hu. unfold unions in Hu.
    apply in_map_iff in Hu as (s & <- & Hs).
    destruct s as [| y s']; [exact I |].
    apply Canonical_IterUnion;
      [discriminate | | eapply sublists_sorted; [exact Hl | exact Hs]].
    apply Forall_forall. intros z Hz.
    assert (Hin : In z l) by (apply (sublists_incl l _ Hs); exact Hz).
    rewrite Forall_forall in Hfa. destruct (Hfa z Hin) as ((Cz & Nz) & Ez).
    split; [exact Cz | split; assumption].
  Qed.

  (** ... and their atoms are drawn from the pool (or are [EmptySet], for the
      empty subset). *)
  Lemma unions_atoms : forall l s,
      Forall notUnion l -> incl s l ->
      incl (mkIterUnion' (IterUnion s)) (EmptySet :: l).
  Proof.
    intros l. induction s as [| y s' IH]; intros Hnu Hincl.
    - intros z Hz. destruct Hz as [<- | []]. left. reflexivity.
    - destruct s' as [| w s''].
      + assert (Hy : In y l) by (apply Hincl; left; reflexivity).
        rewrite mkIterUnion'_notUnion
          by (rewrite Forall_forall in Hnu; apply Hnu, Hy).
        intros z Hz. destruct Hz as [<- | []]. right. exact Hy.
      + rewrite IterUnion_cons by discriminate.
        simpl mkIterUnion'. intros z [<- | Hz].
        * right. apply Hincl. left. reflexivity.
        * apply IH; [exact Hnu | | exact Hz].
          intros t Ht. apply Hincl. right. exact Ht.
  Qed.

  (** The structural invariant, by induction over [e]. *)
  Lemma Atoms_ok : forall e, Forall AtomOk (Atoms e).
  Proof.
    induction e as [ | | c | a IHa b IHb | a IHa b IHb | r IHr ].
    - apply Forall_nil.
    - apply Forall_nil.
    - apply Forall_cons; [split; exact I | apply Forall_nil].
    - (* App *)
      assert (Hbase : Forall AtomOk (mkIterUnion' (canon a) ++ Atoms a)).
      { apply Forall_app. split; [apply mkIterUnion'_ok, canon_Canonical | exact IHa]. }
      rewrite Atoms_App_unfold. apply Forall_forall. intros y Hy.
      rewrite rsort_In in Hy. apply in_app_or in Hy as [Hy | Hy].
      + apply in_flat_map in Hy as (u & Hu & Hy).
        assert (Cu : Canonical u).
        { eapply unions_Canonical;
            [apply mkpool_sorted | apply mkpool_ok, Hbase | exact Hu]. }
        eapply Forall_forall;
          [apply mkIterUnion'_ok, Canonical_appcat;
             [exact Cu | apply canon_Canonical] | exact Hy].
      + apply in_app_or in Hy as [Hy | Hy].
        * eapply Forall_forall;
            [apply mkIterUnion'_ok, canon_Canonical | exact Hy].
        * rewrite Forall_forall in IHb. apply IHb, Hy.
    - (* Union *)
      simpl Atoms. apply Forall_forall. intros y Hy.
      rewrite rsort_In in Hy. apply in_app_or in Hy as [Hy | Hy];
        [rewrite Forall_forall in IHa; apply IHa, Hy
        | rewrite Forall_forall in IHb; apply IHb, Hy].
    - (* Star *)
      assert (Hbase : Forall AtomOk (mkIterUnion' (canon r) ++ Atoms r)).
      { apply Forall_app. split; [apply mkIterUnion'_ok, canon_Canonical | exact IHr]. }
      rewrite Atoms_Star_unfold. apply Forall_forall. intros y Hy.
      rewrite rsort_In in Hy. apply in_app_or in Hy as [Hy | Hy].
      + eapply Forall_forall; [apply mkIterUnion'_ok, canon_Canonical | exact Hy].
      + apply in_flat_map in Hy as (u & Hu & Hy).
        assert (Cu : Canonical u).
        { eapply unions_Canonical;
            [apply mkpool_sorted | apply mkpool_ok, Hbase | exact Hu]. }
        eapply Forall_forall;
          [apply mkIterUnion'_ok, Canonical_appcat;
             [exact Cu | apply canon_Canonical] | exact Hy].
  Qed.

  Lemma pool_ok : forall e,
      Forall (fun x => AtomOk x /\ x <> EmptySet) (pool e).
  Proof.
    intros e. apply mkpool_ok. apply Forall_app.
    split; [apply mkIterUnion'_ok, canon_Canonical | apply Atoms_ok].
  Qed.

  Lemma pool_notUnion : forall e, Forall notUnion (pool e).
  Proof.
    intros e. eapply Forall_impl; [| apply pool_ok].
    intros x ((_ & N) & _). exact N.
  Qed.

  Lemma pool_Canonical : forall e u, In u (unions (pool e)) -> Canonical u.
  Proof.
    intros e u H.
    eapply unions_Canonical; [apply mkpool_sorted | apply pool_ok | exact H].
  Qed.

  (** *** Moving between a subterm's universe and the compound's *)

  Lemma In_pool_AllAtoms : forall e y,
      In y (pool e) -> y = EmptyStr \/ In y (AllAtoms e).
  Proof.
    intros e y H. apply mkpool_In in H as [-> | (H & _)];
      [left; reflexivity | right].
    apply In_AllAtoms. right. apply in_app_or in H as [H | H];
      [left | right]; exact H.
  Qed.

  Lemma AllAtoms_incl_pool : forall e y,
      In y (AllAtoms e) -> y = EmptySet \/ In y (pool e).
  Proof.
    intros e y H.
    destruct (Regexes.regex_dec y EmptySet) as [-> | Hne];
      [left; reflexivity | right].
    apply mkpool_In. right. split; [| exact Hne].
    apply In_AllAtoms in H as [-> | [H | H]];
      [congruence | apply in_or_app; left; exact H
       | apply in_or_app; right; exact H].
  Qed.

  Lemma AllAtoms_App_prod : forall a b u,
      In u (unions (pool a)) ->
      incl (mkIterUnion' (appcat u (canon b))) (AllAtoms (App a b)).
  Proof.
    intros a b u Hu y Hy. apply In_AllAtoms. right. right.
    rewrite Atoms_App_unfold, rsort_In. apply in_or_app. left.
    apply in_flat_map. exists u. split; assumption.
  Qed.

  Lemma AllAtoms_Star_prod : forall r u,
      In u (unions (pool r)) ->
      incl (mkIterUnion' (appcat u (canon (Star r)))) (AllAtoms (Star r)).
  Proof.
    intros r u Hu y Hy. apply In_AllAtoms. right. right.
    rewrite Atoms_Star_unfold, rsort_In. apply in_or_app. right.
    apply in_flat_map. exists u. split; assumption.
  Qed.

  Lemma AllAtoms_App_r : forall a b, incl (AllAtoms b) (AllAtoms (App a b)).
  Proof.
    intros a b y Hy. apply In_AllAtoms in Hy as [-> | [Hy | Hy]].
    - apply EmptySet_AllAtoms.
    - apply In_AllAtoms. right. right.
      rewrite Atoms_App_unfold, rsort_In.
      apply in_or_app. right. apply in_or_app. left. exact Hy.
    - apply In_AllAtoms. right. right.
      rewrite Atoms_App_unfold, rsort_In.
      apply in_or_app. right. apply in_or_app. right. exact Hy.
  Qed.

  (** When the right factor cancels, the left subterm's whole universe is
      carried over: [appcat y EmptyStr = y] and each pool element is its own
      only atom. *)
  Lemma AllAtoms_App_l : forall a b,
      canon b = EmptyStr -> incl (AllAtoms a) (AllAtoms (App a b)).
  Proof.
    intros a b Hb y Hy.
    apply AllAtoms_incl_pool in Hy as [-> | Hy]; [apply EmptySet_AllAtoms |].
    apply (AllAtoms_App_prod a b y (unions_single _ _ Hy)).
    rewrite Hb, appcat_EmptyStr_r.
    rewrite mkIterUnion'_notUnion;
      [left; reflexivity |].
    pose proof (pool_notUnion a) as Hnu. rewrite Forall_forall in Hnu.
    apply Hnu, Hy.
  Qed.

  Lemma AllAtoms_Star_l : forall r,
      canon (Star r) = EmptyStr -> incl (AllAtoms r) (AllAtoms (Star r)).
  Proof.
    intros r Hr y Hy.
    apply AllAtoms_incl_pool in Hy as [-> | Hy]; [apply EmptySet_AllAtoms |].
    apply (AllAtoms_Star_prod r y (unions_single _ _ Hy)).
    rewrite Hr, appcat_EmptyStr_r.
    rewrite mkIterUnion'_notUnion;
      [left; reflexivity |].
    pose proof (pool_notUnion r) as Hnu. rewrite Forall_forall in Hnu.
    apply Hnu, Hy.
  Qed.

  (** A canonical state whose atoms lie in [AllAtoms e] is one of the unions
      the pool generates. (The [EmptySet] state is the empty subset.) *)
  Lemma canon_in_unions_pool : forall e s,
      Canonical s -> incl (mkIterUnion' s) (AllAtoms e) -> In s (unions (pool e)).
  Proof.
    intros e s Cs Hincl.
    destruct (Regexes.regex_dec s EmptySet) as [-> | H0];
      [apply unions_EmptySet |].
    assert (Hp : incl (mkIterUnion' s) (pool e)).
    { intros y Hy.
      pose proof (mkIterUnion'_elts s Cs H0) as Hfa.
      rewrite Forall_forall in Hfa. destruct (Hfa y Hy) as (_ & _ & Hne).
      destruct (AllAtoms_incl_pool e y (Hincl y Hy)) as [-> | Hin];
        [congruence | exact Hin]. }
    pose proof (unions_complete (pool e) (mkIterUnion' s)
                  (mkpool_sorted _) (Canonical_sorted s Cs) Hp) as Hin.
    rewrite IterUnion_mkIterUnion' in Hin. exact Hin.
  Qed.

  (** *** The pool is closed under one derivative step *)

  Lemma pool_elt_deriv : forall e c y,
      AtomClosed e -> In y (pool e) ->
      incl (atoms (derivative c y)) (AllAtoms e).
  Proof.
    intros e c y Hac Hy.
    destruct (In_pool_AllAtoms e y Hy) as [-> | Hin].
    - apply incl_atoms_EmptySet.
    - apply Hac, Hin.
  Qed.

  Lemma unions_deriv_closed : forall e c s,
      AtomClosed e -> incl s (pool e) ->
      incl (atoms (derivative c (IterUnion s))) (AllAtoms e).
  Proof.
    intros e c s Hac. induction s as [| y s' IH]; intros Hincl.
    - apply incl_atoms_EmptySet.
    - destruct s' as [| w s''].
      + apply pool_elt_deriv;
          [exact Hac | apply Hincl; left; reflexivity].
      + rewrite IterUnion_cons by discriminate.
        simpl derivative.
        eapply incl_tran; [apply atoms_incl_smart_union |].
        apply incl_app.
        * apply pool_elt_deriv;
            [exact Hac | apply Hincl; left; reflexivity].
        * apply IH. intros t Ht. apply Hincl. right. exact Ht.
  Qed.

  Lemma pool_closed : forall e c u,
      AtomClosed e -> In u (unions (pool e)) ->
      incl (atoms (derivative c u)) (AllAtoms e).
  Proof.
    intros e c u Hac Hu. unfold unions in Hu.
    apply in_map_iff in Hu as (s & <- & Hs).
    apply unions_deriv_closed; [exact Hac | apply sublists_incl, Hs].
  Qed.

  (** *** A non-degenerate product is a single atom *)

  Lemma appcat_EmptySet_l : forall y, appcat EmptySet y = EmptySet.
  Proof. reflexivity. Qed.

  Lemma appcat_IterApp : forall x y,
      x <> EmptySet -> x <> EmptyStr -> y <> EmptySet -> y <> EmptyStr ->
      appcat x y = IterApp (mkIterApp' x ++ mkIterApp' y).
  Proof.
    intros x y X0 X1 Y0 Y1. unfold appcat.
    destruct x; try congruence; destruct y; try congruence; reflexivity.
  Qed.

  Lemma appcat_notUnion : forall x y,
      x <> EmptySet -> x <> EmptyStr -> y <> EmptySet -> y <> EmptyStr ->
      notUnion (appcat x y).
  Proof.
    intros x y X0 X1 Y0 Y1. rewrite appcat_IterApp by assumption.
    apply IterApp_notUnion. rewrite length_app.
    pose proof (mkIterApp'_nonempty x) as N1.
    pose proof (mkIterApp'_nonempty y) as N2.
    destruct (mkIterApp' x); [contradiction |].
    destruct (mkIterApp' y); [contradiction |].
    simpl. lia.
  Qed.

  (** *** Residuals are canonical *)

  Lemma LeftRes_Canonical : forall u c s,
      Canonical u -> In s (LeftRes c u) -> Canonical s.
  Proof.
    induction u as [ | | ch | f _ rest IH | u1 _ u2 _ | r _ ];
      intros c s Cu Hs;
      try (destruct Hs as [<- | []]; apply canon_Canonical).
    simpl in Cu. destruct Cu as (Cf & Cr & _).
    cbn [LeftRes] in Hs. destruct (nullable f); cbn in Hs.
    - destruct Hs as [<- | Hs].
      + apply Canonical_appcat; [apply canon_Canonical | exact Cr].
      + apply (IH c s Cr Hs).
    - destruct Hs as [<- | []].
      apply Canonical_appcat; [apply canon_Canonical | exact Cr].
  Qed.

  (** The compositional and per-atom halves, joined: an atom-closed [e] has a
      state set closed under [fun s a => canon (derivative a s)]. This is the
      statement the interned builder needs; [AtomClosed] for [App] and [Star]
      is all that is left. *)
  Theorem AtomClosed_state_step : forall e a s,
      AtomClosed e ->
      incl (atoms s) (AllAtoms e) ->
      incl (atoms (derivative a (canon s))) (AllAtoms e).
  Proof.
    intros e a s Hac Hs.
    destruct (canon_UnionNF s) as (Hsort & Hfa).
    rewrite <- (IterUnion_mkIterUnion' (canon s)).
    eapply incl_tran;
      [apply atoms_deriv_IterUnion; [apply mkIterUnion'_nonempty | exact Hfa] |].
    intros y Hy. apply in_concat in Hy as (l & Hl & Hy).
    apply in_map_iff in Hl as (z & <- & Hz).
    apply (Hac a z (Hs _ Hz)). exact Hy.
  Qed.

  (** ** [App] and [Star]

      The two remaining constructors. Both need, besides [AtomClosed] on the
      subterms, the auxiliary invariant [Deriv1]: [Star]'s canonical form
      keeps the *raw* [r] inside ([canon] does not recurse under [Star]), so
      the closure argument meets [derivative c r] rather than
      [derivative c (canon r)], and the two are not interchangeable -- that is
      exactly the commutation refuted in the note below. [Deriv1] states the
      one fact about the raw subterm that is needed, and it is an easy
      induction of its own. *)
  Definition Deriv1 (e : regex) : Prop :=
    forall c, incl (atoms (derivative c e)) (AllAtoms e).

  Lemma Deriv1_EmptySet : Deriv1 EmptySet.
  Proof. intros c. apply incl_atoms_EmptySet. Qed.

  Lemma Deriv1_EmptyStr : Deriv1 EmptyStr.
  Proof. intros c. apply incl_atoms_EmptySet. Qed.

  Lemma Deriv1_Char : forall ch, Deriv1 (Char ch).
  Proof.
    intros ch c. simpl derivative. destruct (Ty.Sigma_dec ch c);
      [| apply incl_atoms_EmptySet].
    intros y Hy. destruct Hy as [<- | []].
    apply In_AllAtoms. right. right. left. reflexivity.
  Qed.

  Lemma Deriv1_Union : forall a b, Deriv1 a -> Deriv1 b -> Deriv1 (Union a b).
  Proof.
    intros a b Ha Hb c. rewrite canon_deriv_Union.
    eapply incl_tran; [apply atoms_incl_Union |].
    apply incl_app.
    - eapply incl_tran; [apply Ha | apply AllAtoms_Union_l].
    - eapply incl_tran; [apply Hb | apply AllAtoms_Union_r].
  Qed.

  Lemma Deriv1_App : forall a b, Deriv1 a -> Deriv1 b -> Deriv1 (App a b).
  Proof.
    intros a b Ha Hb c.
    assert (Hx : incl (atoms (App (derivative c a) b)) (AllAtoms (App a b))).
    { rewrite canon_App_appcat. apply AllAtoms_App_prod.
      apply canon_in_unions_pool; [apply canon_Canonical | apply Ha]. }
    rewrite canon_deriv_App. destruct (nullable a); [| exact Hx].
    eapply incl_tran; [apply atoms_incl_Union |].
    apply incl_app; [exact Hx |].
    eapply incl_tran; [apply Hb | apply AllAtoms_App_r].
  Qed.

  Lemma Deriv1_Star : forall r, Deriv1 r -> Deriv1 (Star r).
  Proof.
    intros r Hr c. rewrite canon_deriv_Star, canon_App_appcat.
    apply AllAtoms_Star_prod.
    apply canon_in_unions_pool; [apply canon_Canonical | apply Hr].
  Qed.

  (** *** Classifying the compound universes

      Every element of [AllAtoms (App a b)] is [EmptySet], an element of
      [AllAtoms b], or an atom of a product [appcat u (canon b)] over a pool
      state [u] -- including the atoms of the start state itself, since
      [canon (App a b)] is the product with [u := canon a]. *)
  Lemma AllAtoms_App_cases : forall a b x,
      In x (AllAtoms (App a b)) ->
      x = EmptySet
      \/ In x (AllAtoms b)
      \/ (exists u, In u (unions (pool a))
                    /\ In x (mkIterUnion' (appcat u (canon b)))).
  Proof.
    intros a b x Hx. apply In_AllAtoms in Hx as [-> | [Hx | Hx]].
    - left. reflexivity.
    - rewrite canon_App_appcat in Hx. right. right.
      exists (canon a). split; [| exact Hx].
      apply canon_in_unions_pool; [apply canon_Canonical |].
      intros y Hy. apply In_AllAtoms. right. left. exact Hy.
    - rewrite Atoms_App_unfold, rsort_In in Hx.
      apply in_app_or in Hx as [Hx | Hx].
      + apply in_flat_map in Hx as (u & Hu & Hx).
        right. right. exists u. split; assumption.
      + apply in_app_or in Hx as [Hx | Hx]; right; left;
          apply In_AllAtoms; [right; left | right; right]; exact Hx.
  Qed.

  Lemma AllAtoms_Star_cases : forall r x,
      In x (AllAtoms (Star r)) ->
      x = EmptySet
      \/ (exists u, In u (unions (pool r))
                    /\ In x (mkIterUnion' (appcat u (canon (Star r))))).
  Proof.
    intros r x Hx.
    (* the start state is the product with [u := EmptyStr], which every pool
       contains *)
    assert (Hstart : In x (mkIterUnion' (canon (Star r))) ->
                     exists u, In u (unions (pool r))
                               /\ In x (mkIterUnion' (appcat u (canon (Star r))))).
    { intros H. exists EmptyStr. split.
      - apply unions_single, mkpool_In. left. reflexivity.
      - rewrite appcat_EmptyStr_l. exact H. }
    apply In_AllAtoms in Hx as [-> | [Hx | Hx]].
    - left. reflexivity.
    - right. apply Hstart, Hx.
    - rewrite Atoms_Star_unfold, rsort_In in Hx.
      apply in_app_or in Hx as [Hx | Hx].
      + right. apply Hstart, Hx.
      + apply in_flat_map in Hx as (u & Hu & Hx).
        right. exists u. split; assumption.
  Qed.

  (** *** The two theorems

      Both proofs have the same five-way split on the product [appcat u v]:
      three degenerate collapses ([u] or [v] absorbing), the case where the
      right factor cancels, and the genuine case, where [deriv_appcat_chain]
      sends the derivative to residual products [appcat s v] and (if [u] is
      nullable) to [v]'s own derivative. [LeftRes_atoms] plus [pool_closed]
      puts every residual [s] back in [unions (pool _)], which closes the
      loop. *)
  Theorem AtomClosed_App : forall a b,
      AtomClosed a -> AtomClosed b -> AtomClosed (App a b).
  Proof.
    intros a b Ha Hb c x Hx.
    apply AllAtoms_App_cases in Hx as [-> | [Hx | (u & Hu & Hx)]].
    - apply incl_atoms_EmptySet.
    - eapply incl_tran; [apply Hb, Hx | apply AllAtoms_App_r].
    - assert (Cu : Canonical u) by (eapply pool_Canonical; exact Hu).
      destruct (Regexes.regex_dec (canon b) EmptySet) as [Hv0 | Hv0].
      { rewrite Hv0, appcat_EmptySet_r in Hx.
        destruct Hx as [<- | []]. apply incl_atoms_EmptySet. }
      destruct (Regexes.regex_dec u EmptySet) as [Hu0 | Hu0].
      { rewrite Hu0, appcat_EmptySet_l in Hx.
        destruct Hx as [<- | []]. apply incl_atoms_EmptySet. }
      destruct (Regexes.regex_dec u EmptyStr) as [Hu1 | Hu1].
      { rewrite Hu1, appcat_EmptyStr_l in Hx.
        eapply incl_tran; [apply Hb | apply AllAtoms_App_r].
        apply In_AllAtoms. right. left. exact Hx. }
      destruct (Regexes.regex_dec (canon b) EmptyStr) as [Hv1 | Hv1].
      { (* the right factor cancels: [x] is an atom of the pool state [u] *)
        rewrite Hv1, appcat_EmptyStr_r in Hx.
        assert (Hxp : In x (EmptySet :: pool a)).
        { unfold unions in Hu. apply in_map_iff in Hu as (s & <- & Hs).
          apply (unions_atoms (pool a) s (pool_notUnion a)
                   (sublists_incl _ _ Hs)). exact Hx. }
        destruct Hxp as [<- | Hxp].
        - apply incl_atoms_EmptySet.
        - eapply incl_tran;
            [apply pool_elt_deriv; [exact Ha | exact Hxp] |].
          apply AllAtoms_App_l, Hv1. }
      (* the genuine case *)
      rewrite (mkIterUnion'_notUnion _
                 (appcat_notUnion u (canon b) Hu0 Hu1 Hv0 Hv1)) in Hx.
      destruct Hx as [<- | []].
      eapply incl_tran;
        [apply (deriv_appcat_chain u (canon b) c Cu Hu0 Hu1
                  (canon_Canonical b) Hv0 Hv1) |].
      apply incl_app.
      + intros y Hy. apply in_flat_map in Hy as (s & Hs & Hy).
        assert (Cs : Canonical s)
          by (eapply LeftRes_Canonical; [exact Cu | exact Hs]).
        assert (Hsp : In s (unions (pool a))).
        { apply canon_in_unions_pool; [exact Cs |].
          pose proof (LeftRes_atoms u c Cu Hu0 Hu1 s Hs) as HL.
          rewrite (Canonical_canon_id s Cs) in HL.
          eapply incl_tran; [exact HL |].
          intros z [<- | Hz];
            [apply EmptySet_AllAtoms | apply (pool_closed a c u Ha Hu), Hz]. }
        rewrite (canon_appcat_id s (canon b) Cs (canon_Canonical b)) in Hy.
        apply (AllAtoms_App_prod a b s Hsp), Hy.
      + destruct (nullable u); [| apply incl_nil_l].
        eapply incl_tran; [| apply AllAtoms_App_r].
        apply (AtomClosed_state_step b c b Hb).
        intros z Hz. apply In_AllAtoms. right. left. exact Hz.
  Qed.

  Theorem AtomClosed_Star : forall r,
      AtomClosed r -> Deriv1 r -> AtomClosed (Star r).
  Proof.
    intros r Hr Dr c x Hx.
    apply AllAtoms_Star_cases in Hx as [-> | (u & Hu & Hx)].
    - apply incl_atoms_EmptySet.
    - assert (Cu : Canonical u) by (eapply pool_Canonical; exact Hu).
      destruct (Regexes.regex_dec u EmptySet) as [Hu0 | Hu0].
      { rewrite Hu0, appcat_EmptySet_l in Hx.
        destruct Hx as [<- | []]. apply incl_atoms_EmptySet. }
      destruct (canon_Star_cases r) as [Hv1 | Hv1].
      { (* [canon (Star r) = EmptyStr]: the product cancels *)
        rewrite Hv1, appcat_EmptyStr_r in Hx.
        assert (Hxp : In x (EmptySet :: pool r)).
        { unfold unions in Hu. apply in_map_iff in Hu as (s & <- & Hs).
          apply (unions_atoms (pool r) s (pool_notUnion r)
                   (sublists_incl _ _ Hs)). exact Hx. }
        destruct Hxp as [<- | Hxp].
        - apply incl_atoms_EmptySet.
        - eapply incl_tran;
            [apply pool_elt_deriv; [exact Hr | exact Hxp] |].
          apply AllAtoms_Star_l, Hv1. }
      assert (Hv0 : canon (Star r) <> EmptySet) by (rewrite Hv1; discriminate).
      assert (Hvs : canon (Star r) <> EmptyStr) by (rewrite Hv1; discriminate).
      destruct (Regexes.regex_dec u EmptyStr) as [Hu1 | Hu1].
      { rewrite Hu1, appcat_EmptyStr_l, Hv1 in Hx.
        simpl in Hx. destruct Hx as [<- | []].
        apply (Deriv1_Star r Dr c). }
      (* the genuine case *)
      rewrite (mkIterUnion'_notUnion _
                 (appcat_notUnion u (canon (Star r)) Hu0 Hu1 Hv0 Hvs)) in Hx.
      destruct Hx as [<- | []].
      eapply incl_tran;
        [apply (deriv_appcat_chain u (canon (Star r)) c Cu Hu0 Hu1
                  (canon_Canonical (Star r)) Hv0 Hvs) |].
      apply incl_app.
      + intros y Hy. apply in_flat_map in Hy as (s & Hs & Hy).
        assert (Cs : Canonical s)
          by (eapply LeftRes_Canonical; [exact Cu | exact Hs]).
        assert (Hsp : In s (unions (pool r))).
        { apply canon_in_unions_pool; [exact Cs |].
          pose proof (LeftRes_atoms u c Cu Hu0 Hu1 s Hs) as HL.
          rewrite (Canonical_canon_id s Cs) in HL.
          eapply incl_tran; [exact HL |].
          intros z [<- | Hz];
            [apply EmptySet_AllAtoms | apply (pool_closed r c u Hr Hu), Hz]. }
        rewrite (canon_appcat_id s (canon (Star r)) Cs
                   (canon_Canonical (Star r))) in Hy.
        apply (AllAtoms_Star_prod r s Hsp), Hy.
      + destruct (nullable u); [| apply incl_nil_l].
        rewrite Hv1. apply (Deriv1_Star r Dr c).
  Qed.

  (** ** Closure, unconditionally

      [AtomClosed] and [Deriv1] are proved together because [Star] needs both
      of the subterm. *)
  Theorem AtomClosed_and_Deriv1 : forall e, AtomClosed e /\ Deriv1 e.
  Proof.
    induction e as [ | | ch | a (Aa & Da) b (Ab & Db)
                   | a (Aa & Da) b (Ab & Db) | r (Ar & Dr) ].
    - split; [apply AtomClosed_EmptySet | apply Deriv1_EmptySet].
    - split; [apply AtomClosed_EmptyStr | apply Deriv1_EmptyStr].
    - split; [apply AtomClosed_Char | apply Deriv1_Char].
    - split; [apply AtomClosed_App | apply Deriv1_App]; assumption.
    - split; [apply AtomClosed_Union | apply Deriv1_Union]; assumption.
    - split; [apply AtomClosed_Star | apply Deriv1_Star]; assumption.
  Qed.

  Theorem AtomClosed_all : forall e, AtomClosed e.
  Proof. intros e. apply AtomClosed_and_Deriv1. Qed.

  (** ** [Superset e] is closed, unconditionally

      The same induction over an iterated union as [unions_deriv_closed], but
      run against [AllAtoms e] itself rather than a subterm's pool -- so the
      per-atom step is [AtomClosed_all] directly. *)
  Lemma AllAtoms_deriv_closed : forall e c s,
      incl s (AllAtoms e) ->
      incl (atoms (derivative c (IterUnion s))) (AllAtoms e).
  Proof.
    intros e c s. induction s as [| y s' IH]; intros Hincl.
    - apply incl_atoms_EmptySet.
    - destruct s' as [| w s''].
      + apply (AtomClosed_all e). apply Hincl. left. reflexivity.
      + rewrite IterUnion_cons by discriminate.
        simpl derivative.
        eapply incl_tran; [apply atoms_incl_smart_union |].
        apply incl_app.
        * apply (AtomClosed_all e). apply Hincl. left. reflexivity.
        * apply IH. intros t Ht. apply Hincl. right. exact Ht.
  Qed.

  (** The start state is in its own superset. *)
  Theorem start_in_Superset : forall e, In (canon e) (Superset e).
  Proof.
    intros e. apply canon_in_Superset. intros x Hx.
    apply In_AllAtoms. right. left. exact Hx.
  Qed.

  (** ...and the superset is closed under [fun s a => canon (derivative a s)],
      which is the DFA's transition function. This is what makes
      [length (Superset e)] a legitimate fuel bound for the table fill. *)
  Theorem Superset_closed : forall e c u,
      In u (Superset e) -> In (canon (derivative c u)) (Superset e).
  Proof.
    intros e c u Hu. unfold Superset, unions in Hu.
    apply in_map_iff in Hu as (s & <- & Hs).
    apply canon_in_Superset.
    apply AllAtoms_deriv_closed, sublists_incl, Hs.
  Qed.

  (** * The superset route, closed

      [AtomClosed_all] is the theorem this file was built for:

        [forall e a x, In x (AllAtoms e) -> incl (atoms (derivative a x)) (AllAtoms e)]

      Together with [AtomClosed_state_step] and [canon_in_Superset] it makes
      [Superset e] a computable finite universe for the DFA's state set, so
      the interned builder can saturate a worklist against a real termination
      measure rather than against a fuel bound that may or may not suffice.

      The obvious route to it is blocked, and that is worth recording since
      the shape of the proof above is a detour around the obstacle. Both the
      [App] and the [Star] case would like

        [canon (derivative a (canon x)) = canon (derivative a x)]

      -- the derivative of an atom taken through a subterm [canon] has
      already rewritten -- and that equation is FALSE. Smallest
      counterexample found (two-letter alphabet, [x] of size 6):

        [x = App (App (Union EmptyStr (Char a)) (Char a)) (Char a)],  [a = a]
          LHS = [Union (Char a) (App (Char a) (Char a))]
          RHS = [App (Union EmptyStr (Char a)) (Char a)]

      Exhaustive search over regexes up to size 6 found 36148 such pairs out
      of 16394480 checked: [canon] re-associates [App] but does not
      distribute [App] over [Union], while the derivative of a nullable [App]
      does distribute.

      What replaces it is [deriv_appcat_chain]: a residual left factor stays
      whole under a right context, and the recursion runs down the [App]
      factor spine ([LeftRes]). [LeftRes_atoms] then shows each residual is a
      union of atoms of a *single* derivative step, so the plain
      [AtomClosed] hypothesis on a subterm already controls every residual
      the chain rule can produce, with no strengthened induction hypothesis.
      The one place a genuinely raw derivative still appears is the body of a
      [Star], which [canon] never rewrites; [Deriv1] is the extra invariant
      that covers it, and it is proved in the same induction.

      [models/atoms2.py] mirrors [Atoms]/[AllAtoms] and checks both
      properties exhaustively; [models/check_superset.py] does the same for
      the reachable states only. *)

End CanonNFFn.
