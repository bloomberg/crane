(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Copyright (c) 2019 Joomy Korkut. MIT license. *)
(* Intrinsically proven sound Levenshtein distance implementation *)
From Stdlib Require Import String Ascii Nat Lia.
From Stdlib Require Import Program.Equality.

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

(* Eval compute in (levenshtein_chain "pascal" "haskell"). *)

Require Crane.Extraction.
Crane Extraction "levenshtein" levenshtein_chain.
