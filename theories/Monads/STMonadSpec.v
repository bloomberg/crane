(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Total-correctness specifications for ST programs over arrays indexed by
    [nat] that hold values of any type.

    [st_spec t m Q] says that [t], interpreted from store [m] by [interp_st],
    terminates without raising, in a store and with a result satisfying [Q].
    It composes through [bind] ([st_spec_bind]), with one rule per array
    operation and a loop rule for [for_each_with]; [st_spec_runST] turns a
    specification of a whole program into an equation on [runST]. Unlike the
    [interp_st_*] equations of [STMonadArrayFacts], which fix the value type
    to [nat], these rules work for arrays of records, pairs and so on. *)

From Stdlib Require Import
  Arith.PeanoNat
  Lia
  List
.

From ExtLib Require Import
  Structures.Monad
.

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.MonadFacts
  Monads.STMonad
  Monads.STMonadFacts
  Utils.HMap
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** Lookup and update on the store, at the key type and instance with which
    [handle_STEvent] uses them, so that rewriting with them matches the
    handler's terms. *)
Notation st_lookup V :=
  (@lookup (nat * nat) (idx_key_type V) (@mem nat V) (hmap_from_idx (V := idx_key_type V))).
Notation st_add V :=
  (@add (nat * nat) (idx_key_type V) (@mem nat V) (hmap_from_idx (V := idx_key_type V))).

Section STSpec.

  Context {E : Type -> Type} `{exceptE Err -< E}.
  Context {S : Type} {V : nat -> Type}.

  Notation mem := (@mem nat V).
  Notation E' := (STEvent nat S V +' E).
  Notation add := (st_add V).
  Notation lookup := (st_lookup V).

  Definition st_spec {A} (t : itree E' A) (m : mem) (Q : mem -> A -> Prop) : Prop :=
    exists m' v, interp_st Nat.le A t m ≈ Ret (m', v) /\ Q m' v.

  Lemma st_spec_ret {A} (v : A) m (Q : mem -> A -> Prop) :
    Q m v -> st_spec (Ret v) m Q.
  Proof. intros HQ. exists m, v. split; [ apply interp_st_Ret_eutt | exact HQ ]. Qed.

  Lemma st_spec_bind {A B} (t : itree E' A) (k : A -> itree E' B) m Q :
    st_spec t m (fun m' v => st_spec (k v) m' Q) ->
    st_spec (ITree.bind t k) m Q.
  Proof.
    intros (m1 & v1 & Ht & m2 & v2 & Hk & HQ).
    exists m2, v2. split; [ eapply interp_st_bind_Ret_l; eassumption | exact HQ ].
  Qed.

  Lemma st_spec_weaken {A} (t : itree E' A) m (Q Q' : mem -> A -> Prop) :
    (forall m' v, Q m' v -> Q' m' v) -> st_spec t m Q -> st_spec t m Q'.
  Proof. intros HQ (m' & v & Ht & Hv). exists m', v. auto. Qed.

  (** Cell [i] of an array over [lo .. hi] lives at key [base + (i - lo)]. *)
  Lemma arr_key_nat idx base lo hi i :
    lo <= i <= hi ->
    @arr_key nat S Nat.le nat_ix V idx (MkSTArray nat S (V idx) base lo hi) i
    = Some (base + (i - lo)).
  Proof.
    intros [Hlo Hhi]. unfold arr_key. cbn -[Nat.sub].
    rewrite (proj2 (Nat.leb_le lo i) Hlo), (proj2 (Nat.leb_le i hi) Hhi).
    cbn -[Nat.sub]. f_equal. induction (i - lo); cbn; lia.
  Qed.

  Lemma st_spec_readArray idx base lo hi i m (Q : mem -> V idx -> Prop) v :
    lo <= i <= hi ->
    lookup (base + (i - lo), idx) m = Some v ->
    Q m v ->
    st_spec (readArray (E := E') (idx := idx) (MkSTArray nat S (V idx) base lo hi) i) m Q.
  Proof.
    intros Hi Hlk HQ. exists m, v. split; [| exact HQ].
    unfold readArray. rewrite interp_st_trigger. cbn -[arr_lookup lookup].
    unfold arr_lookup. rewrite arr_key_nat by exact Hi. rewrite Hlk. reflexivity.
  Qed.

  Lemma st_spec_writeArray idx base lo hi i (v : V idx) m (Q : mem -> unit -> Prop) :
    lo <= i <= hi ->
    Q (add (base + (i - lo), idx) v m) tt ->
    st_spec (writeArray (E := E') (MkSTArray nat S (V idx) base lo hi) i v) m Q.
  Proof.
    intros Hi HQ. eexists _, tt. split; [| exact HQ].
    unfold writeArray. rewrite interp_st_trigger. cbn -[arr_key lookup add].
    rewrite arr_key_nat by exact Hi. reflexivity.
  Qed.

  Section Fill.

    Context (idx : nat) (def : V idx).

    (** The handler's fill loop for [newArray], as a top-level function. *)
    Fixpoint fill_def (ps : list nat) (m : mem) (key : nat) : mem * nat :=
      match ps with
      | nil => (m, key)
      | _ :: rest => fill_def rest (add (key, idx) def m) (Datatypes.S key)
      end.

    Lemma fill_def_below ps : forall m key j,
      j < key -> lookup (j, idx) (fst (fill_def ps m key)) = lookup (j, idx) m.
    Proof.
      induction ps as [|p ps IH]; intros m key j Hj; [ reflexivity |].
      cbn [fill_def]. rewrite IH by lia. apply hmap_lookup_add_ne. intros [=]; lia.
    Qed.

    Lemma fill_def_at ps : forall m key k,
      k < length ps -> lookup (key + k, idx) (fst (fill_def ps m key)) = Some def.
    Proof.
      induction ps as [|p ps IH]; intros m key k Hk; cbn [length] in Hk; [ lia |].
      cbn [fill_def]. destruct k as [|k].
      - rewrite Nat.add_0_r, fill_def_below by lia.
        exact (hmap_lookup_add_eq (V := idx_key_type V) _ _ _).
      - replace (key + Datatypes.S k) with (Datatypes.S key + k) by lia. apply IH. lia.
    Qed.

  End Fill.

  (** A new array over [lo .. hi] occupies [Datatypes.S hi - lo] consecutive
      keys from some base, each holding the default. *)
  Lemma st_spec_newArray idx lo hi (def : V idx) m
    (Q : mem -> STArray nat S (V idx) -> Prop) :
    (forall base m',
        (forall k, k < Datatypes.S hi - lo -> lookup (base + k, idx) m' = Some def) ->
        Q m' (MkSTArray nat S (V idx) base lo hi)) ->
    st_spec (newArray (E := E') idx lo hi def) m Q.
  Proof.
    intros HQ. unfold st_spec, newArray. setoid_rewrite interp_st_trigger.
    cbn -[lookup add Nat.sub].
    match goal with |- context[?F (seq lo (Datatypes.S hi - lo)) m ?b] =>
      change F with (fill_def idx def);
      pose proof (fill_def_at idx def (seq lo (Datatypes.S hi - lo)) m b) as Hfill;
      destruct (fill_def idx def (seq lo (Datatypes.S hi - lo)) m b) as [m' key]
    end.
    eexists _, _. split; [ reflexivity |]. apply HQ. intros k Hk.
    apply Hfill. rewrite length_seq. exact Hk.
  Qed.

  (** Loop rule, with an invariant [I] on the elements still to visit, the
      accumulator and the store. *)
  Lemma st_spec_for_each_with {X B} (I : list X -> B -> mem -> Prop)
    (f : B -> X -> itree E' B) :
    (forall x xs v m, I (x :: xs) v m -> st_spec (f v x) m (fun m' v' => I xs v' m')) ->
    forall xs v m, I xs v m -> st_spec (for_each_with xs v f) m (fun m' v' => I [] v' m').
  Proof.
    intros Hf. induction xs as [|x xs IH]; intros v m HI; cbn [for_each_with].
    - apply st_spec_ret. exact HI.
    - apply st_spec_bind. eapply st_spec_weaken; [| apply Hf, HI ]. intros m' v' HI'.
      apply IH, HI'.
  Qed.

End STSpec.

Section RunST.

  Context {E : Type -> Type} `{exceptE Err -< E} {V : nat -> Type} {S : Type}.

  (** A program specified from the empty store computes, under [runST], a
      result its specification describes. *)
  Lemma st_spec_runST {A} (f : forall S', itree (STEvent nat S' V +' E) A) (Q : A -> Prop) :
    st_spec (S := unit) (V := V) (f unit) HMap.empty (fun _ v => Q v) ->
    exists v, runST (S := S) f ≈ Ret v /\ Q v.
  Proof.
    intros (m' & v & Hrun & HQ). exists v. split; [ eapply runST_Ret, Hrun | exact HQ ].
  Qed.

End RunST.
