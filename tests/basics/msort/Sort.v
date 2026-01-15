(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* from https://github.com/jinxinglim/coq-formalized-divide-and-conquer
   updated to work with Rocq 9.0.0. The original source has no license. *)

(* We will be formalizing different variations of the algorithm
 * paradigm, divide-and-conquer, for lists. Some parts of the codes are
 * referenced and modified from http://adam.chlipala.net/cpdt/html/GeneralRec.html
 * All the variations are derivable from the type, well_founded_induction_type,
 * found in https://rocq-prover.org/doc/V9.0.0/corelib/Corelib.Init.Wf.html
 *)

From Stdlib Require Import Arith List Sorted Permutation.
Import ListNotations.
Open Scope list_scope.

Section DivConq.

Variable A : Type.
Implicit Type l : list A.


(* (Ordering) lengthOrder ls1 ls2 :=
 * length ls1 < length ls2
 *)

Definition lengthOrder (ls1 ls2 : list A) := length ls1 < length ls2.

Lemma lengthOrder_wf' : forall len, forall ls,
  length ls <= len -> Acc lengthOrder ls.
Proof.
  unfold lengthOrder; induction len.
  - intros; rewrite Nat.le_0_r,length_zero_iff_nil in H; rewrite H; constructor;
    intros; inversion H0.
  - destruct ls; constructor; simpl; intros.
    + inversion H0.
    + simpl in H; apply le_S_n in H; apply PeanoNat.lt_n_Sm_le in H0; apply IHlen;
      eapply Nat.le_trans; eassumption.
Defined.


(* lengthOrder_wf:
 * states that the ordering, lengthOrder, is well founded.
 *)

Lemma lengthOrder_wf : well_founded lengthOrder.
Proof. red; intro; eapply lengthOrder_wf'; eauto. Defined.


(* div_conq:
 * Suppose for some arbitrary split function, splitF, with the condition that
 * for any list l, if the length of l is at least 2, then both the sublists
 * generated have length less than the input list. To prove some proposition P
 * holds for all lists ls, one needs to prove the following:
 * 1. P holds for empty list, nil.
 * 2. P holds for one-element list, (a :: nil).
 * 3. If P hold fst(splitF ls) and snd(splitF ls), then P must also hold for ls.
 *)

Lemma div_conq :
  forall (P : list A -> Type)
  (splitF : list A -> list A * list A)
  (splitF_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (splitF ls)) ls)
  (splitF_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (splitF ls)) ls),
    P nil -> (forall a, P (a :: nil))
    -> (forall ls, (P (fst (splitF ls)) -> P (snd (splitF ls)) -> P ls))
    -> forall ls, P ls.
Proof.
  intros; apply (well_founded_induction_type lengthOrder_wf); intros.
  destruct (le_lt_dec 2 (length x)).
  - apply X1; apply X2.
    + apply splitF_wf1; auto.
    + apply splitF_wf2; auto.
  - destruct x; auto. simpl in l;
    apply le_S_n, le_S_n, Nat.le_0_r,length_zero_iff_nil  in l; rewrite l; auto.
Defined.


(* split:=
 * split an input list ls into two sublists where the first sublist contains all
 * the odd indexed element/s and the second sublist contains all the even
 * indexed element/s.
 *)

Fixpoint split (ls : list A) : list A * list A :=
  match ls with
  | nil => (nil, nil)
  | h :: nil => (h :: nil, nil)
  | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in (h1 :: ls1, h2 :: ls2)
  end.


(* split_wf:
 * states that for any list ls of length at least 2, each of the two sublists
 * generated has length less than its original list's.
 *)

Lemma split_wf : forall len ls, 2 <= length ls <= len
  -> let (ls1, ls2) := split ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.
Proof.
  unfold lengthOrder; induction len; intros.
  - inversion H; inversion H1; rewrite H1 in H0; inversion H0.
  - destruct ls; inversion H.
    + inversion H0.
    + destruct ls; simpl; auto.
      destruct (le_lt_dec 2 (length ls)).
      * specialize (IHlen ls); destruct (split ls); destruct IHlen; simpl.
        simpl in H1; apply le_S_n in H1; split; auto. apply le_S_n; auto.
        split; rewrite <- Nat.succ_lt_mono; auto.
      * inversion l.
        -- destruct ls; inversion H3; apply length_zero_iff_nil in H4; rewrite H4;
          simpl; auto.
        -- apply le_S_n in H3. inversion H3.
          apply length_zero_iff_nil in H5; rewrite H5; simpl; auto.
Defined.

Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
  destruct (split ls); destruct 1; auto.

Lemma split_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (split ls)) ls.
Proof. split_wf. Defined.

Lemma split_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (split ls)) ls.
Proof. split_wf. Defined.


(* div_conq_split:
 * - an instance of div_conq where the arbitrary splitF function
 *   is replaced by the split function defined above.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
     following:
 *   1. P holds for empty list, nil.
 *   2. P holds for one-element list, (a :: nil).
 *   3. If P hold fst(split ls) and snd(split ls), then P must also hold for ls.
 *)

Definition div_conq_split P := div_conq P split split_wf1 split_wf2.


(* div_conq_pair:
 * - works similar to induction (i.e. list_rect), but instead of cutting just
 *   head of the list in each recursive step, this induction principle cut two
 *   heads of the list in each recursive step.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
 *   following:
 *   1. P holds for empty list, nil.
 *   2. P holds for one-element list, (a :: nil).
 *   3. P holds for two-elements list, (a1 :: a2 :: nil).
 *   4. If P hold (a1 :: a2 :: nil) and l, then P must also hold for
 *      (a1 :: a2 :: l).
 *)

Lemma div_conq_pair : forall (P : list A -> Type),
    P nil -> (forall (a : A), P (a :: nil))
    -> (forall (a1 a2 : A), P (a1 :: a2 :: nil))
    -> (forall (a1 a2 : A) (l : list A), P (a1 :: a2 :: nil) -> P l
       -> P (a1 :: a2 :: l))
    -> forall (l : list A), P l.
Proof.
  intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
  destruct x; auto; destruct x; auto. intros; apply X2; auto.
  apply X3; unfold lengthOrder; simpl; auto.
Defined.


Variable le : A -> A -> Prop.
Variable le_dec : forall (x y: A), {le x y} + {~le x y}.


(* split_pivot:=
 * takes an input term as pivot and list l and split into two sublists where the
 * first sublist contains all element/s that is/are le_dec _ pivot and the
 * second sublist contains the rest of the element/s.
 *)

Fixpoint split_pivot (pivot : A) l : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' => let (l1, l2) := split_pivot pivot l' in
    if le_dec a pivot
    then (a :: l1, l2) else (l1, a :: l2)
  end.


(* split_pivot_wf:
 * states that for any list ls, each of the sublists generated has length less
 * than or equal to its original list's.
 *)

Lemma split_pivot_wf1 : forall a l, length (fst (split_pivot a l)) <= length l.
Proof.
  induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l);
  simpl in *; auto; apply le_n_S; auto.
Defined.

Lemma split_pivot_wf2 : forall a l, length (snd (split_pivot a l)) <= length l.
Proof.
  induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l);
  simpl in *; auto; apply le_n_S; auto.
Defined.


(* div_conq_pivot:
 * - another variation of div_conq_split, just that for this, it will use
 *   split_pivot instead.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
 *   following:
 *   1. P holds for empty list, nil.
 *   2. If P hold fst(split_pivot a l) and snd(split_pivot a l), then P must
 *      also hold for (a :: l).
 *)

Theorem div_conq_pivot :
  forall (P : list A -> Type),
    P nil
    -> (forall a l, P (fst (split_pivot a l)) -> P (snd (split_pivot a l))
      -> P (a :: l))
    -> forall l, P l.
Proof.
  intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
  destruct x; intros; auto; apply X0; apply X1; apply PeanoNat.le_lt_n_Sm.
  apply split_pivot_wf1. apply split_pivot_wf2.
Defined.

Hypothesis notle_le: forall x y, ~ le x y -> le y x.

(* Forall_snd_split_pivot:
 * le a x for every element, x, in snd(split_pivot a l).
 *)

Lemma Forall_snd_split_pivot : forall a l, Forall (le a) (snd(split_pivot a l)).
Proof.
  induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l);
  simpl in *; auto.
Defined.

End DivConq.

Definition sorted := Sorted le.
Definition permutation := @Permutation nat.

(* Insertion sort *)
Section ISort.

(* This part does not use any new induction principle proven in DivConq.
 * However, for completeness' sake, we will demonstrate how we can prove of the
 * specification of a sorting algorithm via induction, which the extracted proof
 * will be an insertion sort. Note that the proof of the inductive step,
 * sort_cons_prog, can be extracted as an insert function as well.
 *)

Lemma inserted_sorted : forall (a0 a : nat) (l' x : list nat),
  sorted (a0 :: l') -> sorted x -> permutation x (a :: l') -> a0 < a ->
  sorted (a0 :: x).
Proof.
  intros. constructor.
  - trivial.
  - apply Sorted_extends in H.
    + assert (H3 : List.Forall (le a0) (a :: l')).
      constructor. apply Nat.lt_le_incl; assumption. assumption.
      assert (H4 : List.Forall (le a0) x).
      eapply Permutation_Forall. apply Permutation_sym; exact H1. trivial.
      destruct x; auto. constructor. apply Forall_inv in H4; auto.
    + unfold Relations_1.Transitive; apply Nat.le_trans.
Defined.

Lemma sort_cons_prog : forall (a : nat) (l l' : list nat),
  sorted l' -> permutation l' l ->
  {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof.
  intros.
  revert l H H0. induction l'.
  - intros; exists [a]; split.
    + constructor; auto.
    + apply Permutation_nil in H0; rewrite H0; apply Permutation_refl.
  - intros. destruct (IHl' l'); clear IHl'.
    + apply Sorted_inv in H; destruct H; auto.
    + apply Permutation_refl.
    + destruct a1; destruct (le_lt_dec a a0).
      * exists (a :: a0 :: l'); split; constructor; auto.
      * exists (a0 :: x). split.
        -- eapply inserted_sorted; eassumption.
        -- clear H H1 l0; rewrite H2; rewrite <- H0; constructor.
Defined.

Lemma isort :
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
  induction l.
  - exists []; split; constructor.
  - destruct IHl; destruct a0; eapply sort_cons_prog; eassumption.
Defined.

End ISort.

(* Merge sort *)
Section MSort.

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
    match l1 , l2 with
    | [] , _ => l2
    | _ , [] => l1
    | a1 :: l1' , a2 :: l2' =>
        if le_lt_dec a1 a2
        then a1 :: merge l1' l2
        else a2 :: merge_aux l2'
    end
  in merge_aux l2.

Lemma merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
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

Lemma permutation_merge_concat : forall (l1 l2 : list nat),
  permutation (merge l1 l2) (l1 ++ l2).
Proof.
  induction l1; simpl merge.
  - destruct l2; apply Permutation_refl.
  - induction l2.
    + rewrite app_nil_r; apply Permutation_refl.
    + destruct (le_lt_dec a a0).
      * constructor; apply IHl1.
      * apply Permutation_cons_app, IHl2.
Defined.

Lemma permutation_split : forall (l : list nat),
  permutation (fst (split nat l) ++ snd (split nat l)) l.
Proof.
  apply div_conq_pair; intros; simpl.
  - constructor.
  - repeat constructor.
  - repeat constructor.
  - destruct (split nat l); simpl in *; constructor;
    apply Permutation_sym, Permutation_cons_app, Permutation_sym; auto.
Defined.

Lemma merge_prog : forall (l l1 l2 : list nat),
  sorted l1 -> permutation l1 (fst (split nat l)) ->
  sorted l2 -> permutation l2 (snd (split nat l)) ->
  {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
  intros; exists (merge l1 l2); split.
  + apply merge_sorted; eassumption.
  + rewrite permutation_merge_concat, H0, H2; apply permutation_split.
Defined.

Lemma msort : forall (l : list nat),
  {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
  apply div_conq_split.
  - exists []; split; constructor.
  - intros; exists [a]; split; constructor; constructor.
  - intros; destruct H; destruct a; destruct H0; destruct a;
    eapply merge_prog. apply H. trivial. apply H0. trivial.
Defined.

End MSort.

(* Pair sort
  (similar to insertion sort,
   but instead of cutting 1 element at a time,
   cuts two elements at a time) *)
Section PSort.

Lemma pair_merge_prog : forall (a1 a2 : nat) (l l' l'0 : list nat),
  sorted l' -> permutation l' l ->
  sorted l'0 -> permutation l'0 [a1; a2] ->
  {l'1 : list nat | sorted l'1 /\ permutation l'1 (a1 :: a2 :: l)}.
Proof.
  intros; exists (merge l'0 l'); split.
  - apply merge_sorted; auto.
  - rewrite permutation_merge_concat, H0, H2; simpl; repeat constructor; auto.
Defined.

Lemma psort :
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
  apply div_conq_pair.
  - exists []; split; constructor.
  - intros; exists [a]; split; constructor; constructor.
  - intros; destruct (le_lt_dec a1 a2).
    + exists [a1; a2]; split; repeat constructor; auto.
    + exists [a2; a1]; split; repeat constructor; apply Nat.lt_le_incl; auto.
  - intros; destruct H,H0,a,a0;
    eapply pair_merge_prog. apply H1. auto. apply H. auto.
Defined.

End PSort.

(* Quick sort *)
Section QSort.

Section PermSplitPivot.

Variable A : Type.
Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.
Implicit Type l : list A.

Lemma Permutation_split_pivot: forall (a : A) l,
  Permutation (fst (split_pivot A le le_dec a l)
    ++ snd (split_pivot A le le_dec a l)) l.
Proof.
  induction l; simpl; auto.
  destruct (split_pivot A le le_dec a l); simpl in *.
  destruct (le_dec a0 a); simpl; auto;
  rewrite <- Permutation_middle; constructor; auto.
Defined.

End PermSplitPivot.

Lemma qsort :
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
  unshelve eapply div_conq_pivot. exact le. exact le_dec.
  - exists []; split; constructor.
  - intros; destruct H,H0,a0,a1; exists (merge x (a :: x0)); split.
    + apply merge_sorted; auto; constructor; auto.
      assert (Forall (le a) x0).
      eapply Permutation_Forall. apply Permutation_sym; apply H2.
      apply Forall_snd_split_pivot; intros.
      apply not_le, Arith_base.gt_le_S_stt in H3.
      destruct x1; [inversion H3 | constructor; apply le_S_n; auto].
      inversion H3; auto.
    + rewrite permutation_merge_concat, <- Permutation_middle; constructor;
      rewrite H0, H2; apply Permutation_split_pivot.
Defined.

End QSort.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction TestCompile "msort" msort.
