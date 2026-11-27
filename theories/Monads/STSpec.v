(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Total-correctness specifications for ST programs.

    [spec t m Q] says that [t], interpreted from store [m] by
    [ST.interp], terminates without raising, in a store and with a result
    satisfying [Q].  It composes through [bind] ([spec_bind]), with one
    rule per operation and a loop rule for [ST.for_each_with]; [run]
    turns a specification of a whole program into an equation on [ST.run].

    A program is specified in the model, [ST.model_refs], where a reference is
    a location and an array its first location and size.  The store holds a
    value of type [A] at a location and [A]'s code: [read_at] and [write_at]
    read and write it there, through [code_ok]. *)

From Stdlib Require Import
  Arith.PeanoNat
  Classes.EquivDec
  Lia
  List
.

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.MonadFacts
  Monads.ST
  Monads.STFacts
  Utils.HAList
  Utils.HMap
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section Store.

  Context {V : nat -> Type}.

  (** The key is written as a pair, so that its code gives the value's type
      [V c]. *)
  Lemma lookup_add_eq (l c : nat) (v : V c) (m : mem V) :
    lookup (l, c) (add (l, c) v m) = Some v.
  Proof. exact (hmap_lookup_add_eq (hmap := ST.hmap V) (l, c) v m). Qed.

  Lemma lookup_add_ne (l c l' c' : nat) (v : V c') (m : mem V) :
    (l, c) <> (l', c') -> lookup (l, c) (add (l', c') v m) = lookup (l, c) m.
  Proof. exact (hmap_lookup_add_ne (hmap := ST.hmap V) (l, c) (l', c') v m). Qed.

  (** The value of type [A] at location [l]. *)
  Definition read_at {A : Type} `{Code V A} (l : nat) (m : mem V) : option A :=
    match code_ok V A in _ = X return option X with
    | eq_refl => lookup (l, code V A) m
    end.

  Definition write_at {A : Type} `{Code V A} (l : nat) (a : A) (m : mem V) : mem V :=
    match code_ok V A in _ = X return X -> mem V with
    | eq_refl => fun a => add (l, code V A) a m
    end a.

  Lemma read_at_write_at_eq {A} `{Code V A} l a m : read_at l (write_at l a m) = Some a.
  Proof.
    destruct H as [c e]. subst A. cbn [read_at write_at code code_ok].
    apply lookup_add_eq.
  Qed.

  Lemma read_at_write_at_ne {A} `{Code V A} l l' a m : l <> l' -> read_at l (write_at l' a m) = read_at l m.
  Proof.
    destruct H as [c e]. subst A. cbn [read_at write_at code code_ok]. intros Hne.
    apply lookup_add_ne. intros [=]. contradiction.
  Qed.

  Lemma fresh_step_ge (l : mem V) :
    forall acc, acc <= fold_halist (nat * nat) (key_type V) (fun k _ acc => Nat.max (fst k) acc) acc l.
  Proof.
    induction l as [|[[n' j'] v'] l IH]; intros acc; cbn; [ lia |].
    etransitivity; [| apply IH ]. lia.
  Qed.

  Lemma fresh_gt (m : mem V) : forall k j w, lookup (k, j) m = Some w -> k < ST.fresh m.
  Proof.
    unfold ST.fresh.
    enough (Hgen : forall acc k j w, lookup (k, j) m = Some w ->
              k <= fold_halist (nat * nat) (key_type V) (fun k _ acc => Nat.max (fst k) acc) acc m)
      by (intros k j w Hlk; apply Nat.lt_succ_r; eapply Hgen; exact Hlk).
    induction m as [|[[n' j'] v'] m IH]; intros acc k j w Hlk; cbn -[equiv_dec] in Hlk |- *;
      [ discriminate |].
    match type of Hlk with context [match ?d with left _ => _ | right _ => _ end] =>
      destruct d as [e | ne]
    end.
    - injection e as -> ->. etransitivity; [| apply fresh_step_ge ]. lia.
    - eapply IH. exact Hlk.
  Qed.

  (** Nothing is stored at or past the fresh location. *)
  Lemma read_at_fresh {A} `{Code V A} m k : ST.fresh m <= k -> read_at k m = None.
  Proof.
    destruct H as [c e]. subst A. cbn [read_at code code_ok]. intros Hk.
    destruct (lookup (k, c) m) as [w |] eqn:Hlk; [| reflexivity ].
    apply fresh_gt in Hlk. lia.
  Qed.

End Store.

Section Spec.

  Context {E : Type -> Type} `{exceptE Err -< E} {V : nat -> Type}.
  Notation E' := (ST.Event ST.model_refs V +' E).

  Definition spec {A} (t : itree E' A) (m : mem V) (Q : mem V -> A -> Prop) : Prop :=
    exists m' v, ST.interp _ t m ≈ Ret (m', v) /\ Q m' v.

  Lemma spec_ret {A} (v : A) m (Q : mem V -> A -> Prop) :
    Q m v -> spec (Ret v) m Q.
  Proof. intros HQ. exists m, v. split; [ apply interp_ret_eutt | exact HQ ]. Qed.

  Lemma spec_bind {A B} (t : itree E' A) (k : A -> itree E' B) m Q :
    spec t m (fun m' v => spec (k v) m' Q) ->
    spec (ITree.bind t k) m Q.
  Proof.
    intros (m1 & v1 & Ht & m2 & v2 & Hk & HQ).
    exists m2, v2. split; [ eapply interp_bind_ret_l; eassumption | exact HQ ].
  Qed.

  Lemma spec_weaken {A} (t : itree E' A) m (Q Q' : mem V -> A -> Prop) :
    (forall m' v, Q m' v -> Q' m' v) -> spec t m Q -> spec t m Q'.
  Proof. intros HQ (m' & v & Ht & Hv). exists m', v. auto. Qed.

  (** An operation whose handler returns [Ret (m', v)]. *)
  Local Ltac run_op HQ :=
    eexists _, _; split; [| exact HQ ];
    unfold ST.new_ref, ST.write_ref; cbn [code code_ok];
    rewrite interp_trigger; cbn; reflexivity.

  Lemma new_ref {A} `{Code V A} (v : A) m (Q : mem V -> nat -> Prop) :
    Q (write_at (ST.fresh m) v m) (ST.fresh m) ->
    spec (ST.new_ref (R := ST.model_refs) v) m Q.
  Proof. destruct H0 as [c e]. subst A. intros HQ. run_op HQ. Qed.

  Lemma read_ref {A} `{Code V A} (ref : nat) m v (Q : mem V -> A -> Prop) :
    read_at ref m = Some v -> Q m v ->
    spec (ST.read_ref (R := ST.model_refs) ref) m Q.
  Proof.
    destruct H0 as [c e]. subst A. cbn [read_at write_at code code_ok]. intros Hlk HQ. exists m, v. split; [| exact HQ ].
    unfold ST.read_ref. cbn [code code_ok]. rewrite interp_trigger. cbn -[lookup]. rewrite Hlk.
    reflexivity.
  Qed.

  Lemma write_ref {A} `{Code V A} (ref : nat) (a : A) m (Q : mem V -> unit -> Prop) :
    Q (write_at ref a m) tt ->
    spec (ST.write_ref (R := ST.model_refs) ref a) m Q.
  Proof. destruct H0 as [c e]. subst A. intros HQ. run_op HQ. Qed.

  (** The handler's array loops leave the cells below their start alone,
      and put their values from it on. *)
  Lemma fill_below c (v : V c) n : forall key m j c', j < key ->
    lookup (j, c') (fill c v key n m) = lookup (j, c') m.
  Proof.
    induction n as [|n IH]; intros key m j c' Hj; [ reflexivity |]. cbn [fill].
    rewrite IH by lia. apply lookup_add_ne. intros [=]; lia.
  Qed.

  Lemma fill_at c (v : V c) n : forall key m k, k < n -> lookup (key + k, c) (fill c v key n m) = Some v.
  Proof.
    induction n as [|n IH]; intros key m k Hk; [ lia |]. cbn [fill]. destruct k as [|k].
    - rewrite Nat.add_0_r, fill_below by lia. apply lookup_add_eq.
    - replace (key + S k) with (S key + k) by lia. apply IH. lia.
  Qed.

  Lemma fill_list_below c (xs : list (V c)) : forall key m j c', j < key ->
    lookup (j, c') (fill_list c key xs m) = lookup (j, c') m.
  Proof.
    induction xs as [|x xs IH]; intros key m j c' Hj; [ reflexivity |]. cbn [fill_list].
    rewrite IH by lia. apply lookup_add_ne. intros [=]; lia.
  Qed.

  Lemma fill_list_at c (xs : list (V c)) : forall key m k, k < length xs ->
    lookup (key + k, c) (fill_list c key xs m) = nth_error xs k.
  Proof.
    induction xs as [|x xs IH]; intros key m k Hk; cbn [length] in Hk; [ lia |]. cbn [fill_list].
    destruct k as [|k].
    - rewrite Nat.add_0_r, fill_list_below by lia. apply lookup_add_eq.
    - replace (key + S k) with (S key + k) by lia. apply IH. lia.
  Qed.

  Lemma read_cells_spec c b (m : mem V) : forall len s (vs : list (V c)),
    length vs = len ->
    (forall k, k < len -> lookup (b + (s + k), c) m = nth_error vs k) ->
    read_cells c b (seq s len) m = Some vs.
  Proof.
    induction len as [|len IH]; intros s vs Hlen Hcells; destruct vs as [|v vs]; cbn in Hlen;
      try lia; [ reflexivity |]. cbn [seq read_cells].
    pose proof (Hcells 0 ltac:(lia)) as H0. rewrite Nat.add_0_r in H0. cbn [nth_error] in H0.
    rewrite H0.
    rewrite (IH (S s) vs) by (try lia; intros k Hk; replace (S s + k) with (s + S k) by lia;
                              apply (Hcells (S k)); lia).
    reflexivity.
  Qed.

  (** A new array of [n] elements occupies [n] locations from some base, each
      holding [def]. *)
  Lemma new_array {A} `{Code V A} n (def : A) m (Q : mem V -> ST.ArrayLoc A -> Prop) :
    (forall base m', (forall k, k < n -> read_at (base + k) m' = Some def) -> Q m' (ST.MkArrayLoc base n)) ->
    spec (ST.new_array (R := ST.model_refs) n def) m Q.
  Proof.
    destruct H0 as [c e]. subst A. intros HQ. eexists _, _. split.
    - unfold ST.new_array. cbn [code code_ok]. rewrite interp_trigger. cbn. reflexivity.
    - apply HQ. intros k Hk. cbn [read_at code code_ok]. apply fill_at. exact Hk.
  Qed.

  Lemma array_of_list {A} `{Code V A} (xs : list A) m (Q : mem V -> ST.ArrayLoc A -> Prop) :
    (forall base m', (forall k, k < length xs -> read_at (base + k) m' = nth_error xs k) ->
       Q m' (ST.MkArrayLoc base (length xs))) ->
    spec (ST.array_of_list (R := ST.model_refs) xs) m Q.
  Proof.
    destruct H0 as [c e]. subst A. intros HQ. eexists _, _. split.
    - unfold ST.array_of_list. cbn [code code_ok]. rewrite interp_trigger. cbn. reflexivity.
    - apply HQ. intros k Hk. cbn [read_at code code_ok]. apply fill_list_at. exact Hk.
  Qed.

  Lemma read_array {A} `{Code V A} base n i m v (Q : mem V -> A -> Prop) :
    i < n -> read_at (base + i) m = Some v -> Q m v ->
    spec (ST.read_array (R := ST.model_refs) (ST.MkArrayLoc base n) i) m Q.
  Proof.
    destruct H0 as [c e]. subst A. cbn [read_at write_at code code_ok]. intros Hi Hlk HQ. exists m, v. split; [| exact HQ ].
    unfold ST.read_array. cbn [code code_ok]. rewrite interp_trigger. cbn -[Nat.ltb lookup].
    rewrite (proj2 (Nat.ltb_lt i n) Hi), Hlk. reflexivity.
  Qed.

  Lemma write_array {A} `{Code V A} base n i (v : A) m (Q : mem V -> unit -> Prop) :
    i < n -> Q (write_at (base + i) v m) tt ->
    spec (ST.write_array (R := ST.model_refs) (ST.MkArrayLoc base n) i v) m Q.
  Proof.
    destruct H0 as [c e]. subst A. cbn [read_at write_at code code_ok]. intros Hi HQ. eexists _, tt. split; [| exact HQ ].
    unfold ST.write_array. cbn [code code_ok]. rewrite interp_trigger. cbn -[Nat.ltb add].
    rewrite (proj2 (Nat.ltb_lt i n) Hi). reflexivity.
  Qed.

  Lemma array_to_list {A} `{Code V A} base n (vs : list A) m (Q : mem V -> list A -> Prop) :
    length vs = n -> (forall k, k < n -> read_at (base + k) m = nth_error vs k) -> Q m vs ->
    spec (ST.array_to_list (R := ST.model_refs) (ST.MkArrayLoc base n)) m Q.
  Proof.
    destruct H0 as [c e]. subst A. cbn [read_at write_at code code_ok]. intros Hlen Hcells HQ. exists m, vs. split; [| exact HQ ].
    unfold ST.array_to_list. cbn [code code_ok]. rewrite interp_trigger. cbn -[read_cells seq].
    rewrite (read_cells_spec c base m n 0 vs Hlen) by (intros k Hk; apply Hcells; exact Hk).
    reflexivity.
  Qed.

  (** Loop rule, with an invariant [I] on the elements still to visit, the
      accumulator and the store. *)
  Lemma for_each_with {X B} (I : list X -> B -> mem V -> Prop)
    (f : B -> X -> itree E' B) :
    (forall x xs v m, I (x :: xs) v m -> spec (f v x) m (fun m' v' => I xs v' m')) ->
    forall xs v m, I xs v m -> spec (ST.for_each_with xs v f) m (fun m' v' => I [] v' m').
  Proof.
    intros Hf. induction xs as [|x xs IH]; intros v m HI; cbn [ST.for_each_with].
    - apply spec_ret. exact HI.
    - apply spec_bind. eapply spec_weaken; [| apply Hf, HI ]. intros m' v' HI'.
      apply IH, HI'.
  Qed.

End Spec.

Section Run.

  Context {E : Type -> Type} `{exceptE Err -< E} {V : nat -> Type}.

  (** A program specified in the model from the empty store computes,
      under [ST.run], a result its specification describes. *)
  Lemma run {A} (f : forall R : ST.Refs, itree (ST.Event R V +' E) A) (Q : A -> Prop) :
    spec (f ST.model_refs) (@HMap.empty _ _ _ (ST.hmap V)) (fun _ v => Q v) ->
    exists v, ST.run f ≈ Ret v /\ Q v.
  Proof.
    intros (m' & v & Hrun & HQ). exists v. split; [ eapply run_ret, Hrun | exact HQ ].
  Qed.

End Run.
