(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Nat.
From Stdlib Require Import Program.Wf.
From Stdlib Require Import Lia.
From Stdlib Require Import FSets FSets.FMapAVL FSets.FMapFacts.
From Stdlib Require Import Ascii.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Utils Require Import Orders.
From Crane Require Import Extraction.

(** Module type specifying an alphabet: a finite, decidable, comparable type [Sigma]. *)
Module Type Sigma.
  Parameter Sigma : Type.
  Parameter SigmaEnum : list Sigma.
  Parameter Sigma_finite : forall a, In a SigmaEnum.
  Parameter Sigma_dec : forall(a a' : Sigma), {a = a'} + {a <> a'}.

  Parameter compareT : Sigma -> Sigma -> comparison.
  Parameter compareT_eq : forall x y : Sigma,
      compareT x y = Eq <-> x = y.

  Parameter compareT_trans : forall c x y z,
      compareT x y = c -> compareT y z = c -> compareT x z = c.

  (* This is a bit superfluous and probably needs some validation unless its identity *)
  Parameter ascii2Sigma : ascii -> Sigma.

End Sigma.

(** Functor instantiating regex definitions, string utilities, and match semantics over a given alphabet [Ty]. *)
Module DefsFn (Ty : Sigma).

  Import Ty.

  (** Wraps [Sigma] as a [UsualComparableType] for use with ordered-set functors. *)
  Module T_as_UCT <: UsualComparableType.
    Definition t             := Sigma.
    Definition compare       := compareT.
    Definition compare_eq    := compareT_eq.
    Definition compare_trans := compareT_trans.
  End T_as_UCT.

  (** Lifts [T_as_UCT] to a [UsualOrderedType]. *)
  Module T_as_UOT <: UsualOrderedType := UOT_from_UCT T_as_UCT.

  (** AVL-backed finite set over [Sigma]. *)
  Module SigFS := FSetAVL.Make T_as_UOT.
  (** Facts module for [SigFS]. *)
  Module SigFSF := FSetFacts.Facts SigFS.
  (* Bisecting global-arena hang: persistent AVL-tree internals grow via
     path-copying and get heavily aliased across incremental use, unlike
     build-once-read-only values. See project_crane_arena_ambient memory. *)
  Crane NoArena SigFS.MSet.Raw.tree.

  (** AVL-backed finite map keyed by [Sigma]. *)
  Module SigFM := FMapAVL.Make T_as_UOT.
  (** Facts module for [SigFM]. *)
  Module SigFMF := FMapFacts.Facts SigFM.
  Crane NoArena SigFM.Raw.tree.


  (** String type and basic list-of-[Sigma] lemmas. *)
  Module Export Strings.

    Set Warnings "-implicit-core-hint-db,-deprecated".
    Hint Resolve Sigma_dec.

    (** Strings are lists of alphabet symbols. *)
    Definition String : Type := list Sigma.

    (** Decidable equality on [String]. *)
    Lemma String_dec : forall s s' : String, {s = s'} + {s <> s'}.
    Proof. decide equality. Qed.

    (** Removes all empty strings from a list of strings. *)
    Definition rm_empty (yss : list String) :=
      filter (fun l => match l with | [] => false | _ => true end) yss.

    (** Removing empty strings does not change the concatenation; by induction on [yss]. *)
    Lemma rm_empty_mute : forall(yss : list String),
        concat (rm_empty yss) = concat yss.
    Proof.
      intros yss. induction yss.
      - simpl. reflexivity.
      - simpl. destruct a.
        + simpl. apply IHyss.
        + simpl. rewrite IHyss. reflexivity.
    Qed.

    (** Every string in [rm_empty yss] is non-empty; by membership in the filter. *)
    Lemma rm_empty_no_empty : forall(ys : String) (yss : list String),
        In ys (rm_empty yss) -> ys <> [].
    Proof.
      intros ys yss H C. rewrite C in H.
      unfold rm_empty in H. induction yss.
      - simpl in H. contradiction.
      - simpl in H. destruct a.
        + apply IHyss in H. contradiction.
        + simpl in H. destruct H.
          * discriminate.
          * apply IHyss in H. contradiction.
    Qed.

  End Strings.


  (** Regular expressions and their structural operations. *)
  Module Export Regexes.

    (** Inductive type of regular expressions over [Sigma]. *)
    Inductive regex : Type :=
    | EmptySet
    | EmptyStr
    | Char (t : Sigma)
    | App (r1 r2 : regex)
    | Union (r1 r2 : regex)
    | Star (r : regex).

    (** Decidable structural equality on [regex]. *)
    Lemma regex_dec : forall r r' : regex, {r = r'} + {r <> r'}.
    Proof. decide equality. Qed.

    (** * *Should rename to re_equal *)
    (** Boolean structural equality test on [regex]. *)
    Fixpoint regex_eq (r1 r2 : regex) : bool :=
      match r1, r2 with
      | EmptyStr, EmptyStr => true
      | EmptySet, EmptySet => true
      | Char a, Char b => if (Ty.Sigma_dec a b) then true else false
      | App x1 y1, App x2 y2 => andb (regex_eq x1 x2) (regex_eq y1 y2)
      | Union x1 y1, Union x2 y2 => andb (regex_eq x1 x2) (regex_eq y1 y2)
      | Star a, Star b => regex_eq a b
      | _, _ => false
      end.

    (** [regex_eq r1 r2 = true] iff [r1 = r2]; by structural induction. *)
    Lemma regex_eq_correct : forall r1 r2,
        r1 = r2 <-> regex_eq r1 r2 = true.
    Proof.
      induction r1; intros r2; split; intros H; subst; try(auto);
        try(unfold regex_eq in H; repeat dmh; subst; auto; discriminate).
      - simpl. dmg; [reflexivity | contradiction].
      - assert(A1 : regex_eq r1_1 r1_1 = true). apply IHr1_1; reflexivity.
        assert(A2 : regex_eq r1_2 r1_2 = true). apply IHr1_2; reflexivity.
        simpl. rewrite A1. rewrite A2. auto.
      - destruct r2; simpl in H; try(discriminate).
        destruct (regex_eq r1_1 r2_1) eqn:E1; destruct (regex_eq r1_2 r2_2) eqn:E2; try(discriminate).
        apply IHr1_1 in E1. apply IHr1_2 in E2. subst. reflexivity.
      - assert(A1 : regex_eq r1_1 r1_1 = true). apply IHr1_1; reflexivity.
        assert(A2 : regex_eq r1_2 r1_2 = true). apply IHr1_2; reflexivity.
        simpl. rewrite A1. rewrite A2. auto.
      - destruct r2; simpl in H; try(discriminate).
        destruct (regex_eq r1_1 r2_1) eqn:E1; destruct (regex_eq r1_2 r2_2) eqn:E2; try(discriminate).
        apply IHr1_1 in E1. apply IHr1_2 in E2. subst. reflexivity.
      - assert(A : regex_eq r1 r1 = true). apply IHr1; reflexivity.
        simpl. apply A.
      - destruct r2; simpl in H; try(discriminate). apply IHr1 in H. subst; reflexivity.
    Qed.

    (** [regex_eq e e = true] for all [e]; by induction using [regex_eq_correct]. *)
    Lemma regex_eq_refl : forall e, regex_eq e e = true.
      intros. induction e; auto.
      - simpl. dm.
      - simpl. apply Bool.andb_true_iff. split; auto.
      - simpl. apply Bool.andb_true_iff. split; auto.
    Qed.

    (** Decides whether a regex accepts the empty string (unoptimized traversal). *)
    Fixpoint nullable' (r : regex) : bool:=
      match r with
      | EmptySet => false
      | EmptyStr => true
      | Char _ => false
      | App r1 r2 => andb (nullable' r1) (nullable' r2)
      | Union r1 r2 => orb (nullable' r1) (nullable' r2)
      | Star _ => true
      end.

    (** Decides whether a regex accepts the empty string, with short-circuit evaluation. *)
    Fixpoint nullable (r : regex) : bool:=
      match r with
      | EmptySet => false
      | EmptyStr => true
      | Char _ => false
      | App r1 r2 => if negb (nullable r2) (* short circuit and *)
                    then false
                    else (nullable r1)
      | Union r1 r2 => if (nullable r2)    (* short circuit or *)
                      then true
                      else (nullable r1)
      | Star _ => true
      end.

    (** Smart App constructor: simplifies via EmptySet absorber and EmptyStr identity laws. *)
    Definition smart_app (r1 r2 : regex) : regex :=
      match r1, r2 with
      | EmptySet, _  => EmptySet
      | _, EmptySet  => EmptySet
      | EmptyStr, r  => r
      | r, EmptyStr  => r
      | _, _         => App r1 r2
      end.

    (** Smart Union constructor: simplifies via EmptySet identity law. *)
    Definition smart_union (r1 r2 : regex) : regex :=
      match r1, r2 with
      | EmptySet, r  => r
      | r, EmptySet  => r
      | _, _         => Union r1 r2
      end.

    (** Brzozowski derivative of [r] with respect to character [a], using smart constructors. *)
    Fixpoint derivative (a : Sigma) (r : regex) :=
      match r with
      | EmptySet => EmptySet
      | EmptyStr => EmptySet
      | Char x => if Ty.Sigma_dec x a then EmptyStr else EmptySet
      | App r1 r2 => if (nullable r1)
                    then smart_union (smart_app (derivative a r1) r2) (derivative a r2)
                    else smart_app (derivative a r1) r2
      | Union r1 r2 => smart_union (derivative a r1) (derivative a r2)
      | Star r => smart_app (derivative a r) (Star r)
      end.

    (** Iterated derivative of [e] with respect to the string [bs]. *)
    Fixpoint derivative_list (bs : list Sigma) (e : regex) :=
      match bs with
      | [] => e
      | c :: cs => derivative_list cs (derivative c e)
      end.

    (** Lexicographic comparison on [regex] compatible with structural equality. *)
    Fixpoint re_compare (e1 e2 : regex) : comparison :=
      match e1, e2 with
      | EmptyStr, EmptyStr => Eq
      | EmptyStr, _ => Lt
      | _, EmptyStr => Gt
      | EmptySet, EmptySet => Eq
      | EmptySet, _ => Lt
      | _, EmptySet => Gt
      | Char a, Char b => compareT a b
      | Char _, _ => Lt
      | _, Char _ => Gt
      | App e1 e2, App e3 e4 =>
        match re_compare e1 e3 with
        | Eq => re_compare e2 e4
        | comp => comp
        end
      | App _ _, _ => Lt
      | _, App _ _ => Gt
      | Star e1, Star e2 => re_compare e1 e2
      | Star _, _ => Lt
      | _, Star _ => Gt
      | Union e1 e2, Union e3 e4 =>
        match re_compare e1 e3 with
        | Eq => re_compare e2 e4
        | comp => comp
        end
      end.

    (** [re_compare x y = Eq] iff [x = y]; proven by mutual induction on [x] and [y]. *)
    Lemma re_compare_eq : forall x y : regex, re_compare x y = Eq <-> x = y.
    Proof.
      induction x; destruct y; split;
        try(reflexivity);
        try(simpl; intros; discriminate).
      - simpl. intros. apply compareT_eq in H. subst. auto.
      - simpl. intros. injection H; intros; subst. apply compareT_eq. auto.
      - intros. specialize (IHx1 y1). specialize (IHx2 y2). simpl in H.
        destruct (re_compare x1 y1) eqn:E; try(discriminate).
        destruct IHx1. destruct H0. auto. destruct (re_compare x2 y2); try(discriminate).
        destruct IHx2. destruct H0; auto.
      - intros. injection H. intros; subst. simpl.
        destruct (regex_eq y1 y1) eqn:E.
        + apply regex_eq_correct in E. apply IHx1 in E. rewrite E.
          destruct (regex_eq y2 y2) eqn:E1.
          * apply regex_eq_correct in E1. apply IHx2 in E1. auto.
          * apply false_not_true in E1. destruct E1. apply regex_eq_correct. auto.
        + apply false_not_true in E. destruct E. apply regex_eq_correct. auto.
      - intros. specialize (IHx1 y1). specialize (IHx2 y2). simpl in H.
        destruct (re_compare x1 y1) eqn:E; try(discriminate).
        destruct IHx1. destruct H0. auto. destruct (re_compare x2 y2); try(discriminate).
        destruct IHx2. destruct H0; auto.
      - intros. injection H. intros; subst. simpl.
        destruct (regex_eq y1 y1) eqn:E.
        + apply regex_eq_correct in E. apply IHx1 in E. rewrite E.
          destruct (regex_eq y2 y2) eqn:E1.
          * apply regex_eq_correct in E1. apply IHx2 in E1. auto.
          * apply false_not_true in E1. destruct E1. apply regex_eq_correct. auto.
        + apply false_not_true in E. destruct E. apply regex_eq_correct. auto.
      - intros. specialize (IHx y). simpl in H. apply IHx in H. subst. auto.
      - intros. injection H. intros. subst. simpl. apply IHx. auto.
    Qed.

    (** [re_compare x x = Eq] for all [x]; immediate from [re_compare_eq]. *)
    Lemma re_compare_eq' : forall x,
        re_compare x x = Eq.
    Proof.
      intros. apply re_compare_eq. auto.
    Qed.

    (** [re_compare] is transitive: same comparison result is preserved across three regexes. *)
    Lemma re_compare_trans : forall c x y z,
        re_compare x y = c -> re_compare y z = c -> re_compare x z = c.
    Proof.
      induction x; destruct y; destruct z; intros; auto;
        try(simpl in *; subst; discriminate).
      - simpl in *. eapply compareT_trans; eauto.
      - simpl in *.
        destruct(re_compare x1 y1) eqn:E; destruct(re_compare x2 y2) eqn:E0;
          destruct(re_compare y1 z1) eqn:E1; destruct(re_compare y2 z2) eqn:E2;
            try(rewrite re_compare_eq in *; subst; repeat rewrite re_compare_eq' in *; auto);
            try(discriminate);
            try(specialize (IHx2 y2 z2); apply IHx2; auto);
            try(rewrite E0; rewrite E1; auto);
            try(rewrite E1; auto);
            try(rewrite E; auto);
            try(specialize (IHx1 y1 z1); rewrite IHx1; [reflexivity|auto|auto]);
            try(subst; specialize (IHx1 y1 z1); specialize (IHx2 y2 z2);
                rewrite IHx1; [reflexivity|auto|auto]); try(discriminate).
      - simpl in *.
        destruct(re_compare x1 y1) eqn:E; destruct(re_compare x2 y2) eqn:E0;
          destruct(re_compare y1 z1) eqn:E1; destruct(re_compare y2 z2) eqn:E2;
            try(rewrite re_compare_eq in *; subst; repeat rewrite re_compare_eq' in *; auto);
            try(discriminate);
            try(specialize (IHx2 y2 z2); apply IHx2; auto);
            try(rewrite E0; rewrite E1; auto);
            try(rewrite E1; auto);
            try(rewrite E; auto);
            try(specialize (IHx1 y1 z1); rewrite IHx1; [reflexivity|auto|auto]);
            try(subst; specialize (IHx1 y1 z1); specialize (IHx2 y2 z2);
                rewrite IHx1; [reflexivity|auto|auto]); try(discriminate).
      - simpl in *. eapply IHx; eauto.
    Qed.

  End Regexes.

  (** Wraps [regex] as a [UsualComparableType] using [re_compare]. *)
  Module regex_as_UCT <: UsualComparableType.
    Definition t := regex.
    Definition compare := re_compare.
    Definition compare_eq := re_compare_eq.
    Definition compare_trans := re_compare_trans.
  End regex_as_UCT.


  (** Lifts [regex_as_UCT] to a [UsualOrderedType]. *)
  Module regex_as_UOT <: UsualOrderedType := UOT_from_UCT regex_as_UCT.

  (** AVL-backed finite set over [regex]. *)
  Module reFS := FSetAVL.Make regex_as_UOT.
  (** Facts module for [reFS]. *)
  Module reFSF := FSetFacts.Facts reFS.
  Crane NoArena reFS.MSet.Raw.tree.

  (** AVL-backed finite map keyed by [regex]. *)
  Module reFM := FMapAVL.Make regex_as_UOT.
  (** Facts module for [reFM]. *)
  Module reFMF := FMapFacts.Facts reFM.
  Crane NoArena reFM.Raw.tree.

  (** Inductive match relation and regex language equivalence. *)
  Module Export MatchSpec.

    (** Inductive proposition capturing the language semantics of [regex]. *)
    Inductive exp_match : String -> regex -> Prop :=
    | MEmpty : exp_match [] EmptyStr
    | MChar x : exp_match [x] (Char x)
    | MApp s1 re1 s2 re2
           (H1 : exp_match s1 re1)
           (H2 : exp_match s2 re2) :
        exp_match (s1 ++ s2) (App re1 re2)
    | MUnionL s1 re1 re2
              (H1 : exp_match s1 re1) :
        exp_match s1 (Union re1 re2)
    | MUnionR re1 s2 re2
              (H2 : exp_match s2 re2) :
        exp_match s2 (Union re1 re2)
    | MStar0 re : exp_match [] (Star re)
    | MStarApp s1 s2 re
               (H1 : exp_match s1 re)
               (H2 : exp_match s2 (Star re)) :
        exp_match (s1 ++ s2) (Star re).

    (** Two regexes are equivalent when they accept exactly the same strings. *)
    Definition re_equiv (e1 e2 : regex) : Prop :=
      forall z, exp_match z e1 <-> exp_match z e2.

  End MatchSpec.

  (** Lemmas connecting [nullable], [derivative], and [exp_match]. *)
  Module Export MatchSpecLemmas.

    (** [nullable r = true] iff [r] matches the empty string; by induction on [r]. *)
    Theorem nullable_bridge : forall(r : regex),
      true = nullable r <-> exp_match [] r.
    Proof.
      intros r. split; intros H.
      - induction r; try(simpl in H; discriminate).
        + apply MEmpty.
        + simpl in H. destruct (nullable r1); destruct (nullable r2); try(simpl in H; discriminate).
          rewrite <- (app_nil_l []). apply MApp.
          * apply IHr1. reflexivity.
          * apply IHr2. reflexivity.
        + simpl in H.  destruct (nullable r1); destruct (nullable r2).
          * apply MUnionL. apply IHr1. reflexivity.
          * apply MUnionL. apply IHr1. reflexivity.
          * apply MUnionR. apply IHr2. reflexivity.
          * simpl in H. discriminate.
        + apply MStar0.
      - induction r.
        + inversion H.
        + simpl. reflexivity.
        + inversion H.
        + simpl. inversion H. apply app_eq_nil in H1. destruct H1.
          rewrite H1 in H3. rewrite H5 in H4.
          apply IHr1 in H3. apply IHr2 in H4.
          rewrite <- H3. rewrite <- H4. simpl. reflexivity.
        + simpl. inversion H.
          * apply IHr1 in H2. rewrite <- H2. destruct (nullable r2); simpl; reflexivity.
          * apply IHr2 in H1. rewrite <- H1. destruct (nullable r1); simpl; reflexivity.
        + simpl. reflexivity.
    Qed.

    (** [nullable r = true] iff [r] matches [[]]; variant with equality orientation swapped. *)
    Theorem nullable_bridge' : forall(r : regex),
        nullable r = true <-> exp_match [] r.
    Proof.
      split; intros.
      - symmetry in H. apply nullable_bridge; auto.
      - symmetry. apply nullable_bridge; auto.
    Qed.



    (** [App EmptySet r] and [App r EmptySet] never match any string. *)
    Local Lemma app_emptySet_l : forall s r, ~ exp_match s (App EmptySet r).
    Proof. intros s r H. inv H. inv H3. Qed.
    Local Lemma app_emptySet_r : forall s r, ~ exp_match s (App r EmptySet).
    Proof. intros s r H. inv H. inv H4. Qed.

    (** [App EmptyStr r] matches [s] iff [r] does (EmptyStr is the identity for App). *)
    Local Lemma app_emptyStr_l : forall s r,
        exp_match s (App EmptyStr r) <-> exp_match s r.
    Proof.
      split; intro H.
      - inv H. inv H3. exact H4.
      - replace s with ([] ++ s) by auto. apply MApp. apply MEmpty. exact H.
    Qed.

    (** [App r EmptyStr] matches [s] iff [r] does. *)
    Local Lemma app_emptyStr_r : forall s r,
        exp_match s (App r EmptyStr) <-> exp_match s r.
    Proof.
      split; intro H.
      - inv H. inv H4. rewrite app_nil_r. exact H3.
      - replace s with (s ++ []) by (rewrite app_nil_r; auto). apply MApp. exact H. apply MEmpty.
    Qed.

    (** [smart_app r1 r2] matches [s] iff [App r1 r2] does; by case analysis on [r1] and [r2]. *)
    Lemma smart_app_correct : forall s r1 r2,
        exp_match s (smart_app r1 r2) <-> exp_match s (App r1 r2).
    Proof.
      intros s r1 r2.
      split; intro H;
        unfold smart_app in *;
        destruct r1; destruct r2; simpl in *;
        first [ exact H
              | exact (proj2 (app_emptyStr_l _ _) H)
              | exact (proj2 (app_emptyStr_r _ _) H)
              | exact (proj1 (app_emptyStr_l _ _) H)
              | exact (proj1 (app_emptyStr_r _ _) H)
              | exfalso; eapply app_emptySet_l; exact H
              | exfalso; eapply app_emptySet_r; exact H
              | exfalso; inv H ].
    Qed.

    (** [smart_union r1 r2] matches [s] iff [Union r1 r2] does; by case analysis on [r1] and [r2]. *)
    Lemma smart_union_correct : forall s r1 r2,
        exp_match s (smart_union r1 r2) <-> exp_match s (Union r1 r2).
    Proof.
      intros s r1 r2.
      split; intro H;
        unfold smart_union in *;
        destruct r1; destruct r2; simpl in *;
        first [ exact H
              | apply MUnionL; exact H
              | apply MUnionR; exact H
              | inv H; [inv H2 | exact H1]
              | inv H; [exact H2 | inv H1] ].
    Qed.

    (* star_concat upto concat_star necessary for hard star case of der_match *)
    (** A string matched by [Star r'] is a concatenation of strings each matched by [r']. *)
    Lemma star_concat :
      forall s r',
        exp_match s (Star r')
        -> (exists xss : list (list Sigma),
              s = concat xss
              /\ (forall xs,
                    In xs xss
                    -> exp_match xs r')).
    Proof.
      intros s r' hm.
      remember (Star r') as r. generalize dependent r'.
      induction hm; intros r' heq; inv heq.
      - exists []; split; auto.
        intros xs hi; inv hi.
      - destruct (IHhm2 r') as (xss' & heq & hall); subst; auto.
        exists (s1 :: xss'); split; auto.
        intros xs hi.
        destruct hi as [hh| ht]; subst; auto.
    Qed.

    (** A non-empty string matched by [Star r'] decomposes into non-empty pieces each matched by [r']. *)
    Lemma star_concat_no_empt : forall(s : String) (r' : regex),
        s <> []
        -> exp_match s (Star r')
        -> (exists xss : list (list Sigma),
              s = concat xss
              /\ (forall xs,
                    In xs xss
                    -> exp_match xs r' /\ xs <> [])).
    Proof.
      intros s r' Hempty Hstar. apply star_concat in Hstar.
      destruct Hstar as (yss & heq & hall).
      exists(rm_empty yss). split.
      - rewrite rm_empty_mute. apply heq.
      - intros xs H. split.
        + apply hall. apply filter_In in H. exact (proj1 H).
        + apply rm_empty_no_empty in H. apply H.
    Qed.

    (** The concatenation of a list of strings each matched by [r] is matched by [Star r]. *)
    Lemma concat_star : forall(xss : list String) (r : regex),
        (forall xs : list Sigma, In xs xss -> exp_match xs r) -> exp_match (concat xss) (Star r).
    Proof.
      intros xss r H. induction xss.
      - simpl. apply MStar0.
      - replace (concat (a :: xss)) with (a ++ (concat xss)).
        + apply MStarApp.
          * apply H. simpl. left. reflexivity.
          * apply IHxss. intros xs H1. apply H. simpl. right. apply H1.
        + simpl. reflexivity.
    Qed.

    (** [a::s] matches [r] iff [s] matches the derivative of [r] by [a]; the Brzozowski correctness theorem. *)
    Theorem der_match : forall(a : Sigma) (s : String) (r : regex),
        exp_match (a::s) r <-> exp_match s (derivative a r).
    Proof.
      intros a s r.
      split.
      {
        generalize dependent s. induction r; intros s H.
        - inv H.
        - inv H.
        - destruct s.
          + simpl. destruct (Sigma_dec t a).
            * apply MEmpty.
            * inv H. contradiction.
          + inv H.
        - simpl. destruct(nullable r1) eqn:E.
          + inv H. destruct s1.
            * apply smart_union_correct. apply MUnionR.
              apply IHr2. rewrite <- H1. simpl. apply H4.
            * apply smart_union_correct. apply MUnionL.
              apply smart_app_correct.
              simpl in H1. injection H1. intros Happ Hchar.
              rewrite <- Happ. rewrite Hchar in H3. apply IHr1 in H3.
              apply MApp.
              -- apply H3.
              -- apply H4.
          + inv H. destruct s1.
            * apply nullable_bridge in H3. rewrite E in H3. discriminate.
            * apply smart_app_correct.
              simpl in H1. injection H1. intros Happ Hchar.
              rewrite <- Happ. rewrite Hchar in H3. apply IHr1 in H3.
              apply MApp.
              -- apply H3.
              -- apply H4.
        - simpl. inv H.
          + apply IHr1 in H2. apply smart_union_correct. apply MUnionL. apply H2.
          + apply IHr2 in H1. apply smart_union_correct. apply MUnionR. apply H1.
        (* hard_star: This case was the hard one *)
        - apply star_concat_no_empt in H. destruct H as (xss & heq & hall).
          + assert (H : exists(s1 : String) (yss : list String),
                       ((a :: s1) :: yss) = xss).
            {
              destruct xss.
              - simpl in heq. discriminate.
              - simpl in heq. destruct l eqn:E.
                + apply hall in E.
                  * contradiction.
                  * rewrite E. simpl. left. reflexivity.
                + exists(l0). exists(xss). simpl in heq.
                  injection heq. intros I1 I2. rewrite I2. reflexivity.
            }
            destruct H as [s1]. destruct H as [yss].
            rewrite <- H in hall.
            assert (A : In (a :: s1) ((a :: s1) :: yss)).
            { simpl. left. reflexivity. }
            simpl. replace s with (s1 ++ (concat yss)).
            * apply smart_app_correct. apply MApp.
              -- apply IHr. apply hall in A. destruct A. apply H0.
              -- rewrite H in hall.
                 assert (A1 : forall xs : list Sigma, In xs xss -> exp_match xs r).
                 { intros xs. intros HA1. apply hall in HA1. destruct HA1. apply H0. }
                 apply concat_star. intros xs H1. apply A1.
                 rewrite <- H. simpl. right. apply H1.
            * assert (A1 : concat ((a :: s1) :: yss) = concat xss).
              { rewrite H. reflexivity. }
              assert (A2 : concat ((a :: s1) :: yss) = a :: (s1 ++ (concat yss))).
              { simpl. reflexivity. }
              rewrite <- A1 in heq. rewrite A2 in heq. injection heq.
              intros I. symmetry. apply I.
          + intro; discriminate.
      }
      {
        generalize dependent s. induction r; intros s H.
        - inv H.
        - inv H.
        - simpl in H. destruct (Sigma_dec t a); inv H. apply MChar.
        - simpl in H. destruct (nullable r1) eqn:E.
          + apply smart_union_correct in H. inv H.
            * apply smart_app_correct in H2. inv H2.
              replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
              apply MApp.
              -- apply IHr1. apply H3.
              -- apply H4.
              -- reflexivity.
            * symmetry in E. apply nullable_bridge in E. rewrite <- (app_nil_l (a :: s)).
              apply MApp.
              -- apply E.
              -- apply IHr2. apply H1.
          + apply smart_app_correct in H. inv H.
            * replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
              apply MApp.
              -- apply IHr1. apply H3.
              -- apply H4.
              -- reflexivity.
        - simpl in H. apply smart_union_correct in H. inv H.
          + apply MUnionL. apply IHr1. apply H2.
          + apply MUnionR. apply IHr2. apply H1.
        - simpl in H. apply smart_app_correct in H. inv H.
          replace (a :: s1 ++ s2) with ((a :: s1) ++ s2).
          + apply MStarApp.
            * apply IHr. apply H3.
            * apply H4.
          + reflexivity.
      }
    Qed.

    (** [derivative_list (b::bs) e] unfolds to iterating the derivative; by [auto]. *)
    Lemma derivative_list_cons : forall bs b e,
        derivative_list (b :: bs) e = derivative_list bs (derivative b e).
    Proof.
      auto.
    Qed.

    (** [[] matches derivative_list bs e] iff [bs] matches [e]; by induction using [der_match]. *)
    Lemma derivative_list_str : forall bs e,
        exp_match [] (derivative_list bs e) <-> exp_match bs e.
    Proof.
      induction bs; intros; auto.
      - simpl. split; auto.
      - simpl. rewrite IHbs. split; apply der_match.
    Qed.

  End MatchSpecLemmas.

  (** Convenient notation aliases for regex operators and derivative. *)
  Module Notations.

    Notation "e1 = e2 " := (regex_eq e1 e2) (at level 70).
    Notation "a ∂ r" := (derivative a r) (at level 75, right associativity).
    Notation ε := EmptyStr.
    Notation "e1 @ e2" := (App e1 e2) (at level 75).
    Notation "e1 # e2" := (Union e1 e2) (at level 75).

  End Notations.



  (** Derived regex combinators built from the core constructors. *)
  Module Helpers.

    (** One-or-more repetitions: [r+] defined as [r · r*]. *)
    Definition Plus (r : regex) : regex := App r (Star r).

    (** Iterated union of a list of regexes, collapsing to [EmptySet] for [[]]. *)
    Fixpoint IterUnion (rs : list regex) :=
      match rs with
      | [] => EmptySet
      | [e] => e
      | h::t => Union h (IterUnion t)
      end.

    (** Iterated concatenation of a list of regexes, collapsing to [EmptyStr] for [[]]. *)
    Fixpoint IterApp (rs : list regex) :=
      match rs with
      | [] => EmptyStr
      | [e] => e
      | h::t => App h (IterApp t)
      end.

    (** Optional regex [r?] as [EmptyStr | r]. *)
    (* r? *)
    Definition Optional (r : regex) := Union EmptyStr r.

    (** Regex that matches exactly the string [z], character by character. *)
    Definition REString (z : String) := IterApp (map Char z).

  End Helpers.

End DefsFn.


(** Module type alias exposing [DefsFn Ty]. *)
Module Type DefsT (Ty : Sigma).
  Include DefsFn Ty.
End DefsT.

(** Bundled module type grouping an alphabet [Ty] with its derived [Defs]. *)
Module Type T.
  Declare Module Ty : Sigma.
  Declare Module Defs  : DefsT Ty.
  Export Defs.
End T.

(** Functor implementing [T] from a concrete alphabet module [Ty']. *)
Module regexTFn (Ty' : Sigma) <: T.

  Module Export Ty := Ty'.
  Module Export Defs := DefsFn Ty.

End regexTFn.
