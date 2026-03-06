(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Standalone intrinsic merge sort with uniqueness theorem. *)

From Stdlib Require Import Arith List Sorted Permutation Lia.
Import ListNotations.
Open Scope list_scope.

Module MergesortFuel.

(** * Split *)

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest => let '(l1, l2) := split rest in (x :: l1, y :: l2)
  end.

Lemma split_length_le_fst : forall l,
  length (fst (split l)) <= length l.
Proof.
  fix IH 1.
  intros [|x [|y rest]]; simpl; auto.
  destruct (split rest) as [l1 l2] eqn:Hs; simpl.
  specialize (IH rest). rewrite Hs in IH. simpl in IH. lia.
Qed.

Lemma split_length_le_snd : forall l,
  length (snd (split l)) <= length l.
Proof.
  fix IH 1.
  intros [|x [|y rest]]; simpl; auto.
  destruct (split rest) as [l1 l2] eqn:Hs; simpl.
  specialize (IH rest). rewrite Hs in IH. simpl in IH. lia.
Qed.

Lemma split_length_lt_fst : forall l,
  2 <= length l -> length (fst (split l)) < length l.
Proof.
  intros [|x [|y rest]] Hlen; simpl in *; try lia.
  destruct (split rest) as [l1 l2] eqn:Hs; simpl.
  pose proof (split_length_le_fst rest) as H.
  rewrite Hs in H; simpl in H. lia.
Qed.

Lemma split_length_lt_snd : forall l,
  2 <= length l -> length (snd (split l)) < length l.
Proof.
  intros [|x [|y rest]] Hlen; simpl in *; try lia.
  destruct (split rest) as [l1 l2] eqn:Hs; simpl.
  pose proof (split_length_le_snd rest) as H.
  rewrite Hs in H; simpl in H. lia.
Qed.

Lemma split_perm : forall l,
  Permutation (fst (split l) ++ snd (split l)) l.
Proof.
  fix IH 1.
  intros [|x [|y rest]].
  - simpl. constructor.
  - simpl. constructor. constructor.
  - simpl. destruct (split rest) as [l1 l2] eqn:Hs. simpl.
    constructor.
    apply Permutation_sym, Permutation_cons_app, Permutation_sym.
    specialize (IH rest). rewrite Hs in IH. simpl in IH.
    exact IH.
Qed.

(** * Merge *)

Fixpoint merge (l1 l2 : list nat) : list nat :=
  let fix merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | a1 :: l1', a2 :: l2' =>
        if le_lt_dec a1 a2
        then a1 :: merge l1' l2
        else a2 :: merge_aux l2'
    end
  in merge_aux l2.

Lemma merge_sorted : forall l1 l2,
  Sorted le l1 -> Sorted le l2 -> Sorted le (merge l1 l2).
Proof.
  induction l1; induction l2; intros; simpl; auto.
  destruct (le_lt_dec a a0).
  - constructor. apply IHl1; inversion H; auto.
    destruct l1; destruct l2; simpl; auto; destruct (le_lt_dec n a0); auto;
    constructor; inversion H; inversion H4; auto.
  - constructor. inversion H0; apply IHl2; auto.
    destruct l2. constructor; apply Nat.lt_le_incl; auto.
    destruct (le_lt_dec a n); constructor; inversion H0; inversion H4; auto;
    apply Nat.lt_le_incl; auto.
Defined.

Lemma merge_perm : forall l1 l2,
  Permutation (merge l1 l2) (l1 ++ l2).
Proof.
  induction l1; simpl merge.
  - destruct l2; apply Permutation_refl.
  - induction l2.
    + rewrite app_nil_r; apply Permutation_refl.
    + destruct (le_lt_dec a a0).
      * constructor; apply IHl1.
      * apply Permutation_cons_app, IHl2.
Defined.

(** * Fuel-based merge sort *)

Fixpoint msort_go (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => l
  | S fuel' =>
      match l with
      | [] => []
      | [x] => [x]
      | _ => let '(l1, l2) := split l in
             merge (msort_go fuel' l1) (msort_go fuel' l2)
      end
  end.

Lemma msort_go_sorted : forall fuel l,
  length l <= fuel -> Sorted le (msort_go fuel l).
Proof.
  induction fuel; intros l Hlen.
  - assert (length l = 0) by lia.
    destruct l; simpl in *; [constructor | lia].
  - simpl. destruct l as [|x [|y rest]].
    + constructor.
    + repeat constructor.
    + destruct (split (x :: y :: rest)) as [l1 l2] eqn:Hs.
      apply merge_sorted.
      * apply IHfuel.
        assert (Hlt : length l1 < length (x :: y :: rest)).
        { change l1 with (fst (l1, l2)). rewrite <- Hs.
          apply split_length_lt_fst. simpl. lia. }
        simpl in Hlen, Hlt. lia.
      * apply IHfuel.
        assert (Hlt : length l2 < length (x :: y :: rest)).
        { change l2 with (snd (l1, l2)). rewrite <- Hs.
          apply split_length_lt_snd. simpl. lia. }
        simpl in Hlen, Hlt. lia.
Defined.

Lemma msort_go_perm : forall fuel l,
  length l <= fuel -> Permutation (msort_go fuel l) l.
Proof.
  induction fuel; intros l Hlen.
  - assert (length l = 0) by lia.
    destruct l; simpl in *; [constructor | lia].
  - simpl. destruct l as [|x [|y rest]].
    + constructor.
    + repeat constructor.
    + destruct (split (x :: y :: rest)) as [l1 l2] eqn:Hs.
      assert (Hlt1 : length l1 < length (x :: y :: rest)).
      { change l1 with (fst (l1, l2)). rewrite <- Hs.
        apply split_length_lt_fst. simpl. lia. }
      assert (Hlt2 : length l2 < length (x :: y :: rest)).
      { change l2 with (snd (l1, l2)). rewrite <- Hs.
        apply split_length_lt_snd. simpl. lia. }
      assert (Hsp : Permutation (l1 ++ l2) (x :: y :: rest)).
      { pose proof (split_perm (x :: y :: rest)) as Hp.
        rewrite Hs in Hp. simpl in Hp. exact Hp. }
      eapply Permutation_trans.
      * apply merge_perm.
      * eapply Permutation_trans.
        -- apply Permutation_app; apply IHfuel; simpl in Hlen, Hlt1, Hlt2; lia.
        -- exact Hsp.
Defined.

(** * Top-level sort and correctness *)

Definition msort (l : list nat) : list nat :=
  msort_go (length l) l.

Theorem msort_sorted : forall l, Sorted le (msort l).
Proof. intro l. unfold msort. apply msort_go_sorted. lia. Qed.

Theorem msort_perm : forall l, Permutation (msort l) l.
Proof. intro l. unfold msort. apply msort_go_perm. lia. Qed.

(** * Uniqueness *)

Lemma Sorted_inv_le : forall a l,
  Sorted le (a :: l) -> Forall (le a) l.
Proof.
  intros a l Hs.
  apply Sorted_extends in Hs.
  - exact Hs.
  - unfold Relations_1.Transitive. apply Nat.le_trans.
Qed.

Theorem sorted_perm_unique : forall l1 l2,
  Sorted le l1 -> Sorted le l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|a1 l1 IH]; intros l2 Hs1 Hs2 Hp.
  - apply Permutation_nil in Hp. auto.
  - destruct l2 as [|a2 l2].
    + apply Permutation_sym, Permutation_nil in Hp. discriminate.
    + assert (a1 = a2).
      { assert (Ha12 : le a1 a2).
        { assert (Hf : Forall (le a1) (a2 :: l2)).
          { eapply Permutation_Forall; [exact Hp|].
            constructor; [lia | apply Sorted_inv_le; auto]. }
          inversion Hf; auto. }
        assert (Ha21 : le a2 a1).
        { assert (Hf : Forall (le a2) (a1 :: l1)).
          { eapply Permutation_Forall; [apply Permutation_sym; exact Hp|].
            constructor; [lia | apply Sorted_inv_le; auto]. }
          inversion Hf; auto. }
        lia. }
      subst a2. f_equal.
      apply IH.
      * inversion Hs1; auto.
      * inversion Hs2; auto.
      * apply Permutation_cons_inv with (a := a1). exact Hp.
Defined.

(** * Extraction *)

End MergesortFuel.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "mergesort_fuel" MergesortFuel.
