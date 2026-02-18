(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Copyright (c) 2019 Joomy Korkut. MIT license. *)
(* Intrinsically proven sound Levenshtein distance implementation *)
From Stdlib Require Import String Ascii Nat Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Arith.Wf_nat.

Open Scope string_scope.
Infix "::" := String (at level 60, right associativity) : string_scope.
Notation "[ x ]" := (String x EmptyString) : string_scope.
Notation "[ x ; y ; .. ; z ]" := (String x (String y .. (String z EmptyString) ..)) : string_scope.

Inductive edit : string -> string -> Type :=
| insertion (a : ascii) {s : string} : edit s (a :: s)
| deletion (a : ascii) {s : string} : edit (a :: s) s
| update (a' : ascii) (a : ascii)
         {neq : a' <> a} {s : string} : edit (a' :: s) (a :: s).

Inductive chain : string -> string -> nat -> Type :=
| empty : chain "" "" 0
| skip {a : ascii} {s t : string} {n : nat} :
    chain s t n -> chain (a :: s) (a :: t) n
| change {s t u : string} {n : nat} :
    edit s t -> chain t u n -> chain s u (S n).

Lemma chain_length_bounds :
  forall s t n (c : chain s t n),
    length t <= length s + n /\ length s <= length t + n.
Proof.
  intros s t n c.
  induction c as [|a s t n c IH|s t u n e c IH].
  - simpl. split; lia.
  - destruct IH as [IH1 IH2].
    simpl in *.
    split; lia.
  - destruct IH as [IH1 IH2].
    destruct e.
    + simpl in *.
      split; lia.
    + simpl in *.
      split; lia.
    + simpl in *.
      split; lia.
Qed.

Lemma same_chain : forall s, chain s s 0.
Proof.
  intros s. induction s; constructor; auto.
Defined.

Lemma chain_is_same : forall s t, chain s t 0 -> s = t.
Proof.
  intros s t c. dependent induction c.
  auto. f_equal. auto.
Qed.

Lemma insert_chain : forall c s1 s2 n, chain s1 s2 n -> chain s1 (c :: s2) (S n).
Proof.
  intros c s1 s2 n C.
  apply (@change _ (c :: s1)); constructor. auto.
Defined.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2) (length s1).
Proof.
  intros.
  induction s1; simpl.
  induction s2; constructor; auto.
  apply insert_chain; auto.
Defined.

(* transparent string version of app_nil_r *)
Lemma tr_app_empty_r : forall {A : Type} (l : string), l ++ "" = l.
Proof.
  intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.

Lemma inserts_chain_empty : forall s, chain "" s (length s).
Proof.
  intros s.
  induction s; simpl.
  constructor.
  apply insert_chain. auto.
Defined.

Lemma delete_chain : forall c s1 s2 n, chain s1 s2 n -> chain (c :: s1) s2 (S n).
Proof.
  intros c s1 s2 n C.
  apply (@change _ s1). constructor. auto.
Defined.

Lemma deletes_chain : forall s1 s2, chain (s1 ++ s2) s2 (length s1).
Proof.
  intros.
  induction s1; simpl.
  apply same_chain.
  apply delete_chain.
  auto.
Defined.

Lemma deletes_chain_empty : forall s, chain s "" (length s).
Proof.
  intros s.
  induction s; simpl.
  constructor. apply delete_chain. auto.
Defined.

Lemma update_chain : forall c c' s1 s2 n,
    c <> c' -> chain s1 s2 n -> chain (c :: s1) (c' :: s2) (S n).
Proof.
  intros c c' s1 s2 n neq C.
  apply (@change _ (c' :: s1)). constructor. auto. apply skip. auto.
Defined.

(* These aux lemmas are needed because Coq wants to use the fixpoint
   we are defining as a higher order function otherwise. *)
Lemma aux_insert : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain s ys n -> chain s t (S n).
Proof.
  intros s t x xs y ys n eq1 eq2 r1.
  subst.
  apply (insert_chain y (x :: xs) ys n r1).
Defined.

Lemma aux_delete : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain xs (y :: ys) n -> chain s t (S n).
Proof.
  intros s t x xs y ys n eq1 eq2 r2.
  subst.
  apply (delete_chain x xs (y :: ys) n r2).
Defined.

Lemma aux_update : forall s t x xs y ys n,
    x <> y -> s = x :: xs -> t = y :: ys -> chain xs ys n -> chain s t (S n).
Proof.
  intros s t x xs y ys n neq eq1 eq2 r3.
  subst.
  apply (update_chain x y xs ys n neq r3).
Defined.

Lemma aux_eq_char : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys n -> chain s t n.
Proof.
  intros s t x xs y ys n eq1 eq2 ceq C.
  subst. apply skip. auto.
Defined.

Lemma aux_both_empty : forall s t, s = "" -> t = "" -> chain s t 0.
Proof.
  intros s t eq1 eq2. subst. constructor.
Defined.

Lemma leb_false : forall (n m : nat), (n <=? m)%nat = false -> (m <? n)%nat = true.
Proof.
  intros n m H.
  rewrite PeanoNat.Nat.leb_antisym in *.
  assert (eq : forall b, negb b = false -> b = true).
    intros; destruct b; auto.
  exact (eq _ H).
Qed.

Definition min3_app {t : Type} (x y z : t) (f : t -> nat) : t :=
  let n1 := f x in let n2 := f y in let n3 := f z in
  match (Nat.leb n1 n2) with
  | true => match (Nat.leb n1 n3) with | true => x | false => z end
  | false => match (Nat.leb n2 n3) with | true => y | false => z end
  end.

Lemma min3_app_pf {t : Type} (x y z : t) (f : t -> nat) :
    (f (min3_app x y z f) <= f x
  /\ f (min3_app x y z f) <= f y
  /\ f (min3_app x y z f) <= f z)%nat.
Proof.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)) eqn:leb1.
  * destruct (Nat.leb (f x) (f z)) eqn:leb2.
    - rewrite (PeanoNat.Nat.leb_le (f x) (f y)) in *.
      rewrite (PeanoNat.Nat.leb_le (f x) (f z)) in *.
      auto.
    - rewrite (PeanoNat.Nat.leb_le (f x) (f y)) in *.
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f z) (f x))) (leb_false _ _ leb2)).
      lia.
  * destruct (Nat.leb (f y) (f z)) eqn:leb3.
    - rewrite (PeanoNat.Nat.leb_le (f y) (f z)) in *.
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
      lia.
    - pose ((proj1 (PeanoNat.Nat.ltb_lt (f z) (f y))) (leb_false _ _ leb3)).
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
      lia.
Qed.

Lemma min3_app_cases {t : Type} (x y z : t) (f : t -> nat) (P : t -> Prop) :
  P x -> P y -> P z -> P (min3_app x y z f).
Proof.
  intros Hx Hy Hz.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)); destruct (Nat.leb _ _); auto.
Qed.

Lemma min3_app_value {t : Type} (x y z : t) (f : t -> nat) :
  f (min3_app x y z f) = Nat.min (f x) (Nat.min (f y) (f z)).
Proof.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)) eqn:Hxy.
  - destruct (Nat.leb (f x) (f z)) eqn:Hxz.
    + apply Nat.leb_le in Hxy.
      apply Nat.leb_le in Hxz.
      rewrite Nat.min_l by lia.
      rewrite Nat.min_l by lia.
      reflexivity.
    + apply Nat.leb_le in Hxy.
      apply Nat.leb_gt in Hxz.
      rewrite Nat.min_l by lia.
      rewrite Nat.min_r by lia.
      reflexivity.
  - destruct (Nat.leb (f y) (f z)) eqn:Hyz.
    + apply Nat.leb_gt in Hxy.
      apply Nat.leb_le in Hyz.
      rewrite Nat.min_r by lia.
      rewrite Nat.min_l by lia.
      reflexivity.
    + apply Nat.leb_gt in Hxy.
      apply Nat.leb_gt in Hyz.
      rewrite Nat.min_r by lia.
      rewrite Nat.min_r by lia.
      reflexivity.
Qed.

Lemma min3_comm12 : forall a b c : nat,
  Nat.min a (Nat.min b c) = Nat.min b (Nat.min a c).
Proof.
  intros a b c.
  lia.
Qed.

Fixpoint levenshtein_chain (s : string)  :=
  fix levenshtein_chain1 (t : string) : {n : nat & chain s t n} :=
    (match s as s', t as t' return s = s' -> t = t' -> {n : nat & chain s t n} with
    | "" , "" =>
        fun eq1 eq2 => existT _ 0 (aux_both_empty s t eq1 eq2)
    | "" , _ =>
        fun eq1 eq2 =>
          existT _ (length t)
            ltac:(rewrite eq1; apply (inserts_chain_empty t))
    | y :: ys , "" =>
        fun eq1 eq2 =>
          existT _ (length s)
            ltac:(rewrite eq1, eq2; apply (deletes_chain_empty (y :: ys)))
    | x :: xs, y :: ys =>
      fun eq1 eq2 =>
        match ascii_dec x y with
        | left ceq =>
          let (n, c) := levenshtein_chain xs ys in
          existT _ n (aux_eq_char s t x xs y ys n eq1 eq2 ceq c)
        | right neq =>
          let (n1, r1) := levenshtein_chain1 ys in
          let (n2, r2) := levenshtein_chain xs (y :: ys) in
          let (n3, r3) := levenshtein_chain xs ys in
          let r1' : chain s t (S n1) :=
              aux_insert s t x xs y ys n1 eq1 eq2 r1 in
          let r2' : chain s t (S n2) :=
              aux_delete s t x xs y ys n2 eq1 eq2 r2 in
          let r3' : chain s t (S n3) :=
              aux_update s t x xs y ys n3 neq eq1 eq2 r3 in
          min3_app (existT (fun (n : nat) => chain s t n) (S n1) r1')
                   (existT _ (S n2) r2')
                   (existT _ (S n3) r3')
                   (fun p => projT1 p)
        end
    end) (eq_refl s) (eq_refl t).

Definition levenshtein_computed (s t : string) : nat :=
  projT1 (levenshtein_chain s t).

Definition levenshtein (s t : string) : nat :=
  levenshtein_computed s t.

Lemma levenshtein_computed_length_bounds :
  forall s t,
    length t <= length s + levenshtein_computed s t
    /\ length s <= length t + levenshtein_computed s t.
Proof.
  intros s t.
  unfold levenshtein_computed.
  destruct (levenshtein_chain s t) as [n c].
  simpl.
  exact (chain_length_bounds s t n c).
Qed.

Lemma levenshtein_le_computed : forall s t, levenshtein s t <= projT1 (levenshtein_chain s t).
Proof.
  intros s t.
  unfold levenshtein, levenshtein_computed.
  lia.
Qed.

Lemma levenshtein_computed_skip_eq : forall a s t,
    levenshtein_computed (a :: s) (a :: t) = levenshtein_computed s t.
Proof.
  intros a s t.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec a a) as [Haa|Haa].
  - dependent destruction Haa.
    destruct (levenshtein_chain s t) as [n c].
    cbn.
    reflexivity.
  - exfalso.
    apply Haa.
    reflexivity.
Qed.

Lemma levenshtein_computed_mismatch_upper_insert : forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) <= S (levenshtein_computed (a :: s) t).
Proof.
  intros a b s t Hneq.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec a b) as [Heq|Hneqab].
  - exfalso.
    apply Hneq.
    exact Heq.
  - match goal with
    | |- context [let (n1, r1) := ?p in _] => remember p as p1
    end.
    remember (levenshtein_chain s (b :: t)) as p2.
    remember (levenshtein_chain s t) as p3.
    destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
    cbn.
    pose proof (min3_app_pf
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n1)
              (insert_chain b (a :: s) t n1 r1))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n2)
              (delete_chain a s (b :: t) n2 r2))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n3)
              (update_chain a b s t n3 Hneqab r3))
      (fun p => projT1 p)) as [H _].
    cbn in H.
    exact H.
Qed.

Lemma levenshtein_computed_mismatch_upper_delete : forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) <= S (levenshtein_computed s (b :: t)).
Proof.
  intros a b s t Hneq.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec a b) as [Heq|Hneqab].
  - exfalso.
    apply Hneq.
    exact Heq.
  - match goal with
    | |- context [let (n1, r1) := ?p in _] => remember p as p1
    end.
    remember (levenshtein_chain s (b :: t)) as p2.
    remember (levenshtein_chain s t) as p3.
    destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
    cbn.
    pose proof (min3_app_pf
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n1)
              (insert_chain b (a :: s) t n1 r1))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n2)
              (delete_chain a s (b :: t) n2 r2))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n3)
              (update_chain a b s t n3 Hneqab r3))
      (fun p => projT1 p)) as [_ [H _]].
    cbn in H.
    exact H.
Qed.

Lemma levenshtein_computed_mismatch_upper_update : forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) <= S (levenshtein_computed s t).
Proof.
  intros a b s t Hneq.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec a b) as [Heq|Hneqab].
  - exfalso.
    apply Hneq.
    exact Heq.
  - match goal with
    | |- context [let (n1, r1) := ?p in _] => remember p as p1
    end.
    remember (levenshtein_chain s (b :: t)) as p2.
    remember (levenshtein_chain s t) as p3.
    destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
    cbn.
    pose proof (min3_app_pf
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n1)
              (insert_chain b (a :: s) t n1 r1))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n2)
              (delete_chain a s (b :: t) n2 r2))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n3)
              (update_chain a b s t n3 Hneqab r3))
      (fun p => projT1 p)) as [_ [_ H]].
    cbn in H.
    exact H.
Qed.

Lemma levenshtein_computed_insert_lower :
  forall a s t,
    levenshtein_computed s t <= S (levenshtein_computed (a :: s) t).
Proof.
  intros a0 s0 t0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall a s t, length s + length t = m ->
           levenshtein_computed s t <= S (levenshtein_computed (a :: s) t))
      _
      (length s0 + length t0)
      a0 s0 t0 eq_refl).
  intros m IH a s t Hm.
  destruct s as [|x xs], t as [|y ys].
  - simpl. lia.
  - assert (Hlen :
        length ys <= levenshtein_computed (a :: "") (y :: ys)).
    {
      pose proof (levenshtein_computed_length_bounds (a :: "") (y :: ys)) as [H1 _].
      simpl in H1.
      lia.
    }
    simpl.
    lia.
  - simpl. lia.
  - destruct (ascii_dec x y) as [Hxy|Hxy].
    + subst y.
      rewrite levenshtein_computed_skip_eq.
      destruct (ascii_dec a x) as [Hax|Hax].
      * subst a.
        rewrite levenshtein_computed_skip_eq.
        assert (Hrec :
          levenshtein_computed xs ys <=
          S (levenshtein_computed (x :: xs) ys)).
        {
          apply (IH (length xs + length ys)).
          - simpl in Hm. lia.
          - reflexivity.
        }
        exact Hrec.
      * unfold levenshtein_computed.
        cbn.
        destruct (ascii_dec a x) as [Hcontra|Hnax].
        { exfalso. apply Hax. exact Hcontra. }
        remember (levenshtein_chain (a :: x :: xs) ys) as p1.
        remember (levenshtein_chain (x :: xs) (x :: ys)) as p2.
        remember (levenshtein_chain (x :: xs) ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (H3 :
          levenshtein_computed xs ys <= S n3).
        {
          assert (Hrec :
            levenshtein_computed xs ys <=
            S (levenshtein_computed (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          rewrite Heqp3 in Hrec.
          cbn in Hrec.
          exact Hrec.
        }
        assert (H1 :
          levenshtein_computed xs ys <= S (S n1)).
        {
          assert (Hxys :
            levenshtein_computed (x :: xs) ys <= S n1).
          {
            apply (IH (S (length xs) + length ys)).
            - simpl in Hm. lia.
            - rewrite Heqp1. reflexivity.
          }
          assert (Hrec :
            levenshtein_computed xs ys <=
            S (levenshtein_computed (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          lia.
        }
        assert (H2 :
          levenshtein_computed xs ys <= S (S n2)).
        {
          rewrite Heqp2.
          cbn.
          rewrite levenshtein_computed_skip_eq.
          lia.
        }
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n1)
                  (insert_chain x (a :: x :: xs) ys n1 r1))
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n2)
                  (delete_chain a (x :: xs) (x :: ys) n2 r2))
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n3)
                  (update_chain a x (x :: xs) ys n3 Hnax r3))
          (fun p => projT1 p)
          (fun p => levenshtein_computed xs ys <= S (projT1 p))).
        -- exact H1.
        -- exact H2.
        -- exact H3.
    + unfold levenshtein_computed.
      cbn.
      remember (levenshtein_chain (x :: xs) ys) as q1.
      remember (levenshtein_chain xs (y :: ys)) as q2.
      remember (levenshtein_chain xs ys) as q3.
      destruct q1 as [l1 c1], q2 as [l2 c2], q3 as [l3 c3].
      cbn.
      pose proof (min3_app_pf
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                (insert_chain y (x :: xs) ys l1 c1))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                (delete_chain x xs (y :: ys) l2 c2))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                (update_chain x y xs ys l3 Hxy c3))
        (fun p => projT1 p)) as [HL1 [HL2 HL3]].
      destruct (ascii_dec a y) as [Hay|Hay].
      * subst a.
        rewrite levenshtein_computed_skip_eq.
        assert (Hq1 :
          levenshtein_computed (x :: xs) ys = l1).
        { rewrite Heqq1. reflexivity. }
        lia.
      * unfold levenshtein_computed.
        cbn.
        destruct (ascii_dec a y) as [Hcontra|Hnay].
        { exfalso. apply Hay. exact Hcontra. }
        remember (levenshtein_chain (a :: x :: xs) ys) as p1.
        remember (levenshtein_chain (x :: xs) (y :: ys)) as p2.
        remember (levenshtein_chain (x :: xs) ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (Hc1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S l1).
        {
          exact HL1.
        }
        assert (H1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n1)).
        {
          assert (Hrec :
            levenshtein_computed (x :: xs) ys <=
            S (levenshtein_computed (a :: x :: xs) ys)).
          {
            apply (IH (S (length xs) + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          rewrite Heqq1 in Hc1.
          rewrite Heqp1 in Hrec.
          cbn in Hc1, Hrec.
          lia.
        }
        assert (H2 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n2)).
        { lia. }
        assert (H3 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n3)).
        { lia. }
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n1)
                  (insert_chain y (a :: x :: xs) ys n1 r1))
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n2)
                  (delete_chain a (x :: xs) (y :: ys) n2 r2))
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n3)
                  (update_chain a y (x :: xs) ys n3 Hnay r3))
          (fun p => projT1 p)
          (fun p =>
             projT1 (min3_app
               (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                       (insert_chain y (x :: xs) ys l1 c1))
               (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                       (delete_chain x xs (y :: ys) l2 c2))
               (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                       (update_chain x y xs ys l3 Hxy c3))
               (fun p0 => projT1 p0))
             <= S (projT1 p))).
        -- exact H1.
        -- exact H2.
        -- exact H3.
Qed.

Lemma levenshtein_computed_sym :
  forall s t, levenshtein_computed s t = levenshtein_computed t s.
Proof.
  intros s0 t0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall s t, length s + length t = m ->
           levenshtein_computed s t = levenshtein_computed t s)
      _
      (length s0 + length t0)
      s0 t0 eq_refl).
  intros m IH s t Hm.
  destruct s as [|x xs], t as [|y ys].
  - reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - destruct (ascii_dec x y) as [Hxy|Hxy].
    + subst y.
      rewrite levenshtein_computed_skip_eq.
      rewrite (levenshtein_computed_skip_eq x ys xs).
      apply (IH (length xs + length ys)).
      simpl in Hm.
      lia.
    + unfold levenshtein_computed.
      cbn.
      destruct (ascii_dec x y) as [Hcontra|Hnxy].
      { exfalso. apply Hxy. exact Hcontra. }
      destruct (ascii_dec y x) as [Hyx|Hnyx].
      { exfalso. apply Hxy. symmetry. exact Hyx. }
      remember (levenshtein_chain (x :: xs) ys) as p1.
      remember (levenshtein_chain xs (y :: ys)) as p2.
      remember (levenshtein_chain xs ys) as p3.
      remember (levenshtein_chain (y :: ys) xs) as q1.
      remember (levenshtein_chain ys (x :: xs)) as q2.
      remember (levenshtein_chain ys xs) as q3.
      destruct p1 as [n1 c1], p2 as [n2 c2], p3 as [n3 c3].
      destruct q1 as [m1 c4], q2 as [m2 c5], q3 as [m3 c6].
      cbn.
      assert (H12 : n1 = m2).
      {
        assert (Hrec :
          levenshtein_computed (x :: xs) ys =
          levenshtein_computed ys (x :: xs)).
        {
          apply (IH (S (length xs) + length ys)).
          simpl in Hm.
          lia.
        }
        rewrite Heqp1 in Hrec.
        rewrite Heqq2 in Hrec.
        cbn in Hrec.
        exact Hrec.
      }
      assert (H21 : n2 = m1).
      {
        assert (Hrec :
          levenshtein_computed xs (y :: ys) =
          levenshtein_computed (y :: ys) xs).
        {
          apply (IH (length xs + S (length ys))).
          simpl in Hm.
          lia.
        }
        rewrite Heqp2 in Hrec.
        rewrite Heqq1 in Hrec.
        cbn in Hrec.
        exact Hrec.
      }
      assert (H33 : n3 = m3).
      {
        assert (Hrec :
          levenshtein_computed xs ys =
          levenshtein_computed ys xs).
        {
          apply (IH (length xs + length ys)).
          simpl in Hm.
          lia.
        }
        rewrite Heqp3 in Hrec.
        rewrite Heqq3 in Hrec.
        cbn in Hrec.
        exact Hrec.
      }
      rewrite (min3_app_value
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n1)
                (insert_chain y (x :: xs) ys n1 c1))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n2)
                (delete_chain x xs (y :: ys) n2 c2))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                (update_chain x y xs ys n3 Hnxy c3))
        (fun p => projT1 p)).
      rewrite (min3_app_value
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m1)
                (insert_chain x (y :: ys) xs m1 c4))
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m2)
                (delete_chain y ys (x :: xs) m2 c5))
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m3)
                (update_chain y x ys xs m3 Hnyx c6))
        (fun p => projT1 p)).
      cbn.
      rewrite <- H12, <- H21, <- H33.
      apply min3_comm12.
Qed.

Lemma levenshtein_computed_insert_lower_r :
  forall a s t,
    levenshtein_computed s t <= S (levenshtein_computed s (a :: t)).
Proof.
  intros a s t.
  rewrite (levenshtein_computed_sym s t).
  rewrite (levenshtein_computed_sym s (a :: t)).
  apply levenshtein_computed_insert_lower.
Qed.

Lemma levenshtein_computed_delete_upper :
  forall a s t,
    levenshtein_computed (a :: s) t <= S (levenshtein_computed s t).
Proof.
  intros a s t.
  destruct t as [|b ys].
  - simpl. lia.
  - destruct (ascii_dec a b) as [Hab|Hab].
    + subst b.
      rewrite levenshtein_computed_skip_eq.
      apply levenshtein_computed_insert_lower_r.
    + apply levenshtein_computed_mismatch_upper_delete.
      exact Hab.
Qed.

Lemma levenshtein_computed_update_upper :
  forall a a' s t,
    a' <> a ->
    levenshtein_computed (a' :: s) t <= S (levenshtein_computed (a :: s) t).
Proof.
  intros a0 a'0 s0 t0 Hneq0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall a a' s t, a' <> a ->
           length s + length t = m ->
           levenshtein_computed (a' :: s) t <=
           S (levenshtein_computed (a :: s) t))
      _
      (length s0 + length t0)
      a0 a'0 s0 t0 Hneq0 eq_refl).
  intros m IH a a' s t Hneq Hm.
  destruct t as [|b ys].
  - simpl. lia.
  - destruct (ascii_dec a' b) as [Ha'b|Ha'b].
    + subst b.
      rewrite levenshtein_computed_skip_eq.
      unfold levenshtein_computed.
      cbn.
      destruct (ascii_dec a a') as [Hcontra|Hna].
      { exfalso. apply Hneq. symmetry. exact Hcontra. }
      remember (levenshtein_chain (a :: s) ys) as p1.
      remember (levenshtein_chain s (a' :: ys)) as p2.
      remember (levenshtein_chain s ys) as p3.
      destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
      cbn.
      assert (H1 : levenshtein_computed s ys <= S (S n1)).
      {
        assert (Hrec : levenshtein_computed s ys <= S (levenshtein_computed (a :: s) ys)).
        { apply levenshtein_computed_insert_lower. }
        rewrite Heqp1 in Hrec.
        cbn in Hrec.
        lia.
      }
      assert (H2 : levenshtein_computed s ys <= S (S n2)).
      {
        assert (Hrec : levenshtein_computed s ys <= S (levenshtein_computed s (a' :: ys))).
        { apply levenshtein_computed_insert_lower_r. }
        rewrite Heqp2 in Hrec.
        cbn in Hrec.
        lia.
      }
      assert (H3 : levenshtein_computed s ys <= S (S n3)).
      { lia. }
      eapply (min3_app_cases
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n1)
                (insert_chain a' (a :: s) ys n1 r1))
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n2)
                (delete_chain a s (a' :: ys) n2 r2))
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n3)
                (update_chain a a' s ys n3 Hna r3))
        (fun p => projT1 p)
        (fun p => levenshtein_computed s ys <= S (projT1 p))).
      * exact H1.
      * exact H2.
      * exact H3.
    + unfold levenshtein_computed.
      cbn.
      destruct (ascii_dec a' b) as [Hcontra|Hna'b].
      { exfalso. apply Ha'b. exact Hcontra. }
      remember (levenshtein_chain (a' :: s) ys) as q1.
      remember (levenshtein_chain s (b :: ys)) as q2.
      remember (levenshtein_chain s ys) as q3.
      destruct q1 as [l1 c1], q2 as [l2 c2], q3 as [l3 c3].
      cbn.
      pose proof (min3_app_pf
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                (insert_chain b (a' :: s) ys l1 c1))
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                (delete_chain a' s (b :: ys) l2 c2))
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                (update_chain a' b s ys l3 Hna'b c3))
        (fun p => projT1 p)) as [HL1 [HL2 HL3]].
      destruct (ascii_dec a b) as [Hab|Hab].
      * subst b.
        rewrite levenshtein_computed_skip_eq.
        assert (Hq3 : levenshtein_computed s ys = l3).
        { rewrite Heqq3. reflexivity. }
        lia.
      * unfold levenshtein_computed.
        cbn.
        destruct (ascii_dec a b) as [Hcontra2|Hnab].
        { exfalso. apply Hab. exact Hcontra2. }
        remember (levenshtein_chain (a :: s) ys) as p1.
        remember (levenshtein_chain s (b :: ys)) as p2.
        remember (levenshtein_chain s ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (H1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n1)).
        {
          assert (Hrec :
            levenshtein_computed (a' :: s) ys <=
            S (levenshtein_computed (a :: s) ys)).
          {
            apply (IH (length s + length ys)).
            - simpl in Hm. lia.
            - exact Hneq.
            - reflexivity.
          }
          rewrite Heqq1 in HL1.
          rewrite Heqp1 in Hrec.
          cbn in HL1, Hrec.
          lia.
        }
        assert (H2 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n2)).
        { lia. }
        assert (H3 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n3)).
        { lia. }
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S n1)
                  (insert_chain b (a :: s) ys n1 r1))
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S n2)
                  (delete_chain a s (b :: ys) n2 r2))
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S n3)
                  (update_chain a b s ys n3 Hnab r3))
          (fun p => projT1 p)
          (fun p =>
             projT1 (min3_app
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                       (insert_chain b (a' :: s) ys l1 c1))
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                       (delete_chain a' s (b :: ys) l2 c2))
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                       (update_chain a' b s ys l3 Hna'b c3))
               (fun p0 => projT1 p0))
             <= S (projT1 p))).
        -- exact H1.
        -- exact H2.
        -- exact H3.
Qed.

Theorem levenshtein_computed_is_minimal :
  forall s t n (c : chain s t n),
    levenshtein_computed s t <= n.
Proof.
  intros s t n c.
  induction c.
  - reflexivity.
  - rewrite levenshtein_computed_skip_eq.
    exact IHc.
  - destruct e.
    + eapply Nat.le_trans.
      * apply levenshtein_computed_insert_lower.
      * lia.
    + eapply Nat.le_trans.
      * apply levenshtein_computed_delete_upper.
      * lia.
    + eapply Nat.le_trans.
      * apply levenshtein_computed_update_upper.
        exact neq.
      * lia.
Qed.

Theorem levenshtein_eq_computed : forall s t, levenshtein s t = projT1 (levenshtein_chain s t).
Proof.
  intros s t.
  reflexivity.
Qed.

Theorem levensthein_is_minimal (s t : string) :
  forall (n : nat) (c : chain s t n), levenshtein s t <= n.
Proof.
  intros n c.
  unfold levenshtein.
  apply (levenshtein_computed_is_minimal s t n c).
Qed.

(* Eval compute in (levenshtein_chain "pascal" "haskell"). *)

Require Crane.Extraction.
Crane Extraction "levenshtein" levenshtein_chain.
