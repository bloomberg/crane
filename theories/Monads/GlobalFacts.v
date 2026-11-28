(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Equational laws for [Global.interp]: how it unfolds on [Ret], [Tau],
    [Vis], [trigger] and [bind], under strong and weak bisimulation.  Also
    [hstep], [Global.handle] as a function on stores, with read-after-write
    laws for stores, [Global.fill] and [Global.fresh]. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Classes.EquivDec
  Init.Peano
  Lia
  List
  Morphisms
  RelationClasses
  Relation_Definitions
  Setoid
  Strings.String
.

From Crane Require Import
  Extraction
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.Global
  Monads.MonadFacts
  Utils.HAList
  Utils.HMap
.

From ExtLib Require Import
  Data.Bool
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Structures.Functor
  Structures.Traversable
  Structures.Reducible
.

(* NOTE: *must* import this before the ITree Eq.Paco2 import.*)
From Paco Require Import paco.

From ITree Require Import
  Basics.HeterogeneousRelations
  Eq.Paco2
  Events.Exception
  Events.FailFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.

Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.


Section InterpTheorems.

  Context {E : Type -> Type}.
  Context {T S : Type}.
  Variable (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{Global.RefClass T}.
  Context {V : T -> Type}.
  Context `{Global.Event T V -< E}.
  Context `{exceptE Err -< E}.


  (** The store [Global.run] starts from: an association list. *)
  Definition mem := halist (@idx_key T T) (idx_key_type V).


  Context `{HMap (@idx_key T T) (idx_key_type V) mem}.



  (** One step of [Global.interp], on an observed tree. *)
  Definition interp_ {R}
    (ot : itree' (Global.Event T V +' E) R)
    (l : mem)
    : itree E (mem * R) :=
    match ot with
    | RetF r => ret (l, r)
    | TauF t => Tau (Global.interp ltu _ t l)
    | @VisF _ _ _ X e k =>
        x <- Global.handle_leave_rest ltu X e l;;
        Tau (Global.interp _ _ (k (snd x)) (fst x))
    end.

  (** [Global.interp] is its one-step unfolding [interp_], up to [eq_itree]. *)
  Lemma unfold_interp {R}
    (t : itree (Global.Event T V +' E) R)
    (l : mem) :
    eq_itree eq
    (Global.interp _ _ t l)
    (interp_ (observe t) l).
  Proof using Type.
    unfold Global.interp, ITree.Interp.Interp.interp, Basics.iter, MonadIter_stateT0, Basics.iter.
    cbn.
    setoid_rewrite unfold_iter; cbn.
    destruct observe; cbn.
    - rewrite 2 bind_ret_l. reflexivity.
    - rewrite 2 bind_ret_l. cbn. reflexivity.
    - unfold ITree.map. repeat rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.
      unfold snd at 1.
      unfold fst at 5.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros x ? <-].
      reflexivity.
  Qed.

  (** Interpreting [ret] returns the store unchanged. *)
  Lemma interp_monad_ret:  forall {R : Type} (val: R) (l : mem),
      Global.interp (E := E) _ _ (ret val) l ≅ ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp. reflexivity.
    Qed.

  (** Interpreting [Ret] returns the store unchanged. *)
  Lemma interp_ret: forall {R : Type} (val: R) (l : mem),
      Global.interp (E := E) _ _ (Ret val) l ≅ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp. reflexivity.
    Qed.

  (** [interp_ret] up to weak bisimulation. *)
  Lemma interp_ret_eutt: forall {R : Type} (val: R) (l : mem),
      Global.interp (E := E) _ _ (Ret val) l ≈ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp. reflexivity.
    Qed.

  (** A visible event is handled, then the continuation runs on the new store. *)
  Lemma interp_vis
    {R U}
    (e : (Global.Event T V +' E) R)
    (k : R -> itree (Global.Event T V +' E) U)
    (l : mem)
    : Global.interp ltu _ (Vis e k) l
    ≅ x <- Global.handle_leave_rest ltu _ e l;;
      Tau (Global.interp ltu _ (k (snd x)) (fst x)).
    Proof using Type.
      intros. rewrite unfold_interp. reflexivity.
    Qed.


  (** A silent step stays a silent step. *)
  Lemma interp_tau {R : Type}
      (t : itree (Global.Event T V +' E) R)
      (l : mem)
      : Global.interp ltu _ (Tau t) l ≅ Tau (Global.interp ltu _ t l).
    Proof using Type.
      intros. rewrite unfold_interp. reflexivity.
    Qed.


  (** [Ret] and the monad's [ret] are the same tree. *)
  Lemma Ret_is_ret {R : Type} (x : R) : ((Ret x) : itree E R)  = ret x.
    Proof using Type. reflexivity. Qed.

  (** A triggered event is just its handler, up to weak bisimulation. *)
  Lemma interp_trigger
    {R : Type}
    (e : (Global.Event T V +' E) R)
    (l : mem) :
    Global.interp ltu _ (ITree.trigger e) l ≈ Global.handle_leave_rest ltu _ e l.
    Proof using Type.
      unfold ITree.trigger.
      rewrite interp_vis.
      match goal with
        |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst
      end.
      eapply eqit_bind; try reflexivity.
      intros [].
      - setoid_rewrite tau_eutt.
        unfold snd, fst.
        apply interp_ret_eutt.
    Qed.


(** Strong bisimulation of interpreted trees, with equal stores and results. *)
Definition eq_itree_eqv_global {R E} (x1 x2 : itree (E) (mem * R)) : Prop :=
  @eq_itree (E) _ _ eq x1 x2.


(** [Global.interp] respects strong bisimulation of the tree. *)
Global Instance eq_itree_interp {R : Type} :
Proper (@eq_itree (Global.Event T V +' E) R R eq ==> eq ==> eq_itree_eqv_global)
        (Global.interp ltu R).
Proof.
  repeat red.
  ginit. pcofix CIH. intros x y Heq s1 s2 Hseq.
  rewrite !unfold_interp. punfold Heq. red in Heq.
    destruct Heq; subst; pclearbot; try discriminate; cbn.
    - gstep; constructor; auto.
    - gstep; constructor; auto with paco.
    - guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros [] ? <-. gstep.
        constructor; auto with paco itree.
  Qed.


(** Interpreting a [bind] threads the store from the first part to the
    continuation. *)
Lemma interp_bind {U R}
  (t : itree (Global.Event T V +' E) R)
  (k : R -> itree (Global.Event T V +' E) U)
  (mem : mem)
  : Global.interp ltu U (ITree.bind t k) mem
      ≅ '(new_mem, new_val) <- Global.interp ltu R t mem;;
    Global.interp ltu U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : Global.interp ltu U (ITree.bind t k) mem
                        ≅ Global.interp ltu U (bind_ t k) mem).
  { apply eq_itree_interp. apply unfold_bind. reflexivity.  }
  rewrite unfold_bind'.
  rewrite (unfold_interp t mem).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn. apply reflexivity.
  - rewrite interp_tau. cbn. rewrite bind_tau.
    gstep. econstructor; eauto with paco.
  - rewrite interp_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. destruct u2 eqn:Equ2.
      rewrite bind_tau.
      gstep. constructor.
      auto with paco.
Qed.

(** [interp_bind] up to weak bisimulation. *)
Lemma interp_bind_eutt {U R}
  (t : itree (Global.Event T V +' E) R)
  (k : R -> itree (Global.Event T V +' E) U)
  (mem : mem)
  : Global.interp ltu U (ITree.bind t k) mem
      ≈ '(new_mem, new_val) <- Global.interp ltu R t mem;;
    Global.interp ltu U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : Global.interp ltu U (ITree.bind t k) mem
                        ≅ Global.interp ltu U (bind_ t k) mem).
  { apply eq_itree_interp. apply unfold_bind. reflexivity.  }
  rewrite unfold_bind'.
  rewrite (unfold_interp t mem).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn. apply reflexivity.
  - rewrite interp_tau. cbn. rewrite bind_tau.
    gstep. econstructor; eauto with paco.
  - rewrite interp_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. destruct u2 eqn:Equ2.
      rewrite bind_tau.
      gstep. constructor.
      auto with paco.
Qed.

(** The same statement as [interp_bind_eutt], kept for existing callers. *)
Lemma interp_bind_eutt' {U R}
  (t : itree (Global.Event T V +' E) R)
  (k : R -> itree (Global.Event T V +' E) U)
  (mem : mem)
  : (Global.interp ltu U (ITree.bind t k) mem)
      ≈ '(new_mem, new_val) <- Global.interp ltu R t mem;;
    Global.interp ltu U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : Global.interp ltu U (ITree.bind t k) mem
                        ≅ Global.interp ltu U (bind_ t k) mem).
  { apply eq_itree_interp. apply unfold_bind. reflexivity.  }
  rewrite unfold_bind'.
  rewrite (unfold_interp t mem).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn. apply reflexivity.
  - rewrite interp_tau. cbn. rewrite bind_tau.
    gstep. econstructor; eauto with paco.
  - rewrite interp_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. destruct u2 eqn:Equ2.
      rewrite bind_tau.
      gstep. constructor.
      auto with paco.
Qed.


(** If the first part interprets to [t2] and every continuation to [k2],
    the bind interprets to their bind. *)
Lemma eutt_eq_bind_interp {U R}
  (k2 : (mem * R) -> itree E (mem * U))
  (lmem : mem)
  (t1 : itree (Global.Event T V +' E) R)
  (t2 : itree E (mem * R))
  (k1: R -> itree (Global.Event T V +' E) U)
  :
  Global.interp ltu R t1 lmem ≈ t2 ->
  (forall u lmem', Global.interp ltu U (k1 u) lmem' ≈ (k2 (lmem', u))) ->
  Global.interp ltu U (ITree.bind t1 k1) lmem
  ≈
  ITree.bind t2 k2.
Proof.
  intros t1_eq keq.
  rewrite (interp_bind_eutt t1 k1).
  apply eutt_eq_bind'; [assumption | intuition].
Qed.

End InterpTheorems.

(** A [nat] reference remembers the location it was made at. *)
Lemma idx_ref_same_idx : forall (n : nat) A,
  Global.ref_index A (Global.make_ref A n) = n.
Proof. reflexivity. Qed.

(** [Global.handle] as a function, without the tree: the new store and the
    answer, or [None] exactly where [Global.handle] fails. *)
Section HStep.

  Context {T : Type} (ltu : T -> T -> Prop) `{Ix T ltu} `{Global.RefClass T}.
  Context {V : T -> Type} {M : Type}.
  Context `{HMap (@idx_key T T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (@idx_key_type T T V))}.

  (** One event against the store, as [Global.handle] performs it. *)
  Definition hstep {A : Type} (e : Global.Event T V A) (mem : M) : option (M * A) :=
    match e in Global.Event _ _ X return option (M * X) with
    | NewRef _ _ idx v =>
        let n := Global.fresh ltu mem in
        Some (add (n, idx) v mem, Global.make_ref (V idx) n)
    | ReadRef _ _ idx s =>
        match lookup (Global.ref_index (V idx) s, idx) mem with
        | Some v => Some (mem, v)
        | None => None
        end
    | WriteRef _ _ idx s v => Some (add (Global.ref_index (V idx) s, idx) v mem, tt)
    | NewArray _ _ idx n def =>
        let b := Global.fresh ltu mem in
        Some (Global.fill ltu idx def b n mem, MkArray b n)
    | ArrayOfList _ _ idx elems =>
        let b := Global.fresh ltu mem in
        Some (Global.fill_list ltu idx b elems mem, MkArray b (List.length elems))
    | ReadArray _ _ idx a i =>
        let '(MkArray b n) := a in
        if Nat.ltb i n then
          match lookup (Global.shift ltu b i, idx) mem with
          | Some v => Some (mem, v)
          | None => None
          end
        else None
    | WriteArray _ _ idx a i v =>
        let '(MkArray b n) := a in
        if Nat.ltb i n then Some (add (Global.shift ltu b i, idx) v mem, tt)
        else None
    | ArrayToList _ _ idx a =>
        let '(MkArray b n) := a in
        match Global.read_cells ltu idx b (seq 0 n) mem with
        | Some vs => Some (mem, vs)
        | None => None
        end
    end.

  Context {E : Type -> Type} `{exceptE Err -< E} {EQD : EqDec T eq}.

  (** Where [hstep] answers, [Global.handle] returns that answer at once. *)
  Lemma handle_hstep_some {A} (e : Global.Event T V A) (m : M) (p : M * A) :
    hstep e m = Some p -> Global.handle (E := E) ltu A e m = Ret p.
  Proof.
    destruct e; cbn;
      repeat match goal with
             | |- context [match ?x with _ => _ end] => destruct x
             end;
      intros Hs; try discriminate; injection Hs as <-; reflexivity.
  Qed.

  (** Where [hstep] has no answer, [Global.handle] fails. *)
  Lemma handle_hstep_none {A} (e : Global.Event T V A) (m : M) :
    hstep e m = None -> exists s, Global.handle (E := E) ltu A e m = failwith s.
  Proof.
    destruct e; cbn;
      repeat match goal with
             | |- context [match ?x with _ => _ end] => destruct x
             end;
      intros Hs; try discriminate; eexists; reflexivity.
  Qed.

End HStep.

(** Read-after-write for any store meeting the [HMap] laws. *)
Section StoreLaws.

  Context {K : Type} {V : K -> Type} {M : Type}.
  Context {HM : HMap K V M} {HMO : HMapOk HM}.

  (** Reading back the key just written. *)
  Lemma lookup_add_eq (k : K) (v : V k) (m : M) : lookup k (add k v m) = Some v.
  Proof. apply (proj2 (mapsto_lookup _ _ _ _ _ _)), (mapsto_add_eq _ _ _). Qed.

  (** A write leaves every other key alone. *)
  Lemma lookup_add_neq (k k' : K) (v : V k) (m : M) :
    k <> k' -> lookup k' (add k v m) = lookup k' m.
  Proof.
    intros Hk. destruct (lookup k' m) as [v'|] eqn:E1.
    - apply (proj2 (mapsto_lookup _ _ _ _ _ _)), (mapsto_add_neq _ _ _ m k v k' Hk).
      apply (proj1 (mapsto_lookup _ _ _ _ _ _)), E1.
    - destruct (lookup k' (add k v m)) as [v'|] eqn:E2; [|reflexivity].
      apply (proj1 (mapsto_lookup _ _ _ _ _ _)), (mapsto_add_neq _ _ _ m k v k' Hk) in E2.
      apply (proj2 (mapsto_lookup _ _ _ _ _ _)) in E2. congruence.
  Qed.

End StoreLaws.

(** [Global.fill] and [Global.shift] over [nat] locations. *)
Section NatStore.

  Context {V : nat -> Type} {M : Type}.
  Context {HM : HMap (@idx_key nat nat) (idx_key_type V) M} {HMO : HMapOk HM}.

  (** Element [i] of an array at [b] lives at location [b + i]. *)
  Lemma shift_nat (b i : nat) : Global.shift Nat.le b i = b + i.
  Proof. induction i as [|i IH]; cbn; [lia | rewrite IH; lia]. Qed.

  (** Outside the filled cells the store is unchanged. *)
  Lemma lookup_fill_out idx (v : V idx) (b n : nat) (m : M) (l j : nat) :
    ~ (b <= l < b + n /\ j = idx) ->
    lookup (l, j) (Global.fill Nat.le idx v b n m) = lookup (l, j) m.
  Proof.
    revert b m. induction n as [|n IH]; intros b m Hn; cbn; [reflexivity|].
    rewrite IH by lia. apply lookup_add_neq. intros Hk. injection Hk as -> ->. lia.
  Qed.

  (** Every filled cell holds the fill value. *)
  Lemma lookup_fill_in idx (v : V idx) (b n : nat) (m : M) (l : nat) :
    b <= l < b + n -> lookup (l, idx) (Global.fill Nat.le idx v b n m) = Some v.
  Proof.
    revert b m. induction n as [|n IH]; intros b m Hn; cbn; [lia|].
    destruct (Nat.eq_dec l b) as [->|Hne].
    - rewrite lookup_fill_out by lia. exact (lookup_add_eq (b, idx) v _).
    - apply IH. lia.
  Qed.

End NatStore.

(** [Global.fresh] over the association-list store with [nat] locations
    that [Global.run] uses. *)
Section Fresh.

  Context {V : nat -> Type} {EQD : EqDec (@idx_key nat nat) eq}.

  (** The location [fresh] computes is beyond every bound key's. *)
  Lemma lookup_lt_fresh (m : halist (@idx_key nat nat) (idx_key_type V))
    (k : @idx_key nat nat) (v : idx_key_type V k) :
    lookup k m = Some v -> fst k < Global.fresh Nat.le m.
  Proof.
    unfold Global.fresh, Reducible.fold, Foldable_halist. cbn. intros Hk.
    apply Nat.lt_succ_r.
    assert (Hacc : forall m0 acc, acc <= fold_halist (@idx_key nat nat)
      (fun k0 : @idx_key nat nat => V (snd k0))
      (fun k0 _ => let '(n, _) := k0 in fun acc0 => Nat.max n acc0) acc m0).
    { induction m0 as [|[[n i] w] m0 IH]; intros acc; cbn; [lia|].
      etransitivity; [|apply IH]. lia. }
    generalize 0.
    induction m as [|[[n i] w] m IH]; intros acc; cbn in Hk |- *; [discriminate|].
    revert Hk; destruct (_ == k) as [Heq|Hne]; intros Hk.
    - rewrite <- Heq. cbn. etransitivity; [|apply Hacc]. lia.
    - apply IH, Hk.
  Qed.

  (** So every cell from [fresh] on is unbound. *)
  Lemma lookup_fresh_none (m : halist (@idx_key nat nat) (idx_key_type V)) (l j : nat) :
    Global.fresh Nat.le m <= l -> lookup (l, j) m = None.
  Proof.
    intros Hl. destruct (lookup (l, j) m) as [v|] eqn:E1; [|reflexivity].
    apply lookup_lt_fresh in E1. cbn [fst] in E1. lia.
  Qed.

End Fresh.

(** [Global.interp] over any store: its unfolding on [Ret], [Tau] and the
    two kinds of visible event. *)
Section InterpAnyStore.

  Context {E : Type -> Type} {T : Type} (ltu : T -> T -> Prop) `{Ix T ltu}.
  Context {EQD : EqDec T eq} `{Global.RefClass T} {V : T -> Type}.
  Context `{exceptE Err -< E}.
  Context {M : Type} `{HMap (@idx_key T T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (@idx_key_type T T V))}.

  (** One step of [Global.interp] over any store, up to [eq_itree]. *)
  Lemma interp_unfold_any {R} (t : itree (Global.Event T V +' E) R) (m : M) :
    Global.interp ltu R t m
    ≅ match observe t with
      | RetF r => Ret (m, r)
      | TauF t' => Tau (Global.interp ltu R t' m)
      | VisF e k =>
          x <- Global.handle_leave_rest ltu _ e m;;
          Tau (Global.interp ltu R (k (snd x)) (fst x))
      end.
  Proof.
    unfold Global.interp, ITree.Interp.Interp.interp, Basics.iter, MonadIter_stateT0, Basics.iter.
    cbn. setoid_rewrite unfold_iter; cbn.
    destruct observe; cbn.
    - rewrite 2 bind_ret_l. reflexivity.
    - rewrite 2 bind_ret_l. reflexivity.
    - unfold ITree.map. repeat rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros x ? <-].
      reflexivity.
  Qed.

  (** A finished tree returns the store it is given. *)
  Lemma interp_ret_any {R} (r : R) (m : M) :
    Global.interp (E := E) ltu R (Ret r) m ≅ Ret (m, r).
  Proof. rewrite interp_unfold_any. reflexivity. Qed.

  (** A silent step stays a silent step. *)
  Lemma interp_tau_any {R} (t : itree (Global.Event T V +' E) R) (m : M) :
    Global.interp ltu R (Tau t) m ≅ Tau (Global.interp ltu R t m).
  Proof. rewrite interp_unfold_any. reflexivity. Qed.

  (** A global-state event [hstep] answers becomes a silent step into the
      continuation, on the new store. *)
  Lemma interp_vis_inl {X R} (e : Global.Event T V X)
    (k : X -> itree (Global.Event T V +' E) R) (m m' : M) (x : X) :
    hstep ltu e m = Some (m', x) ->
    Global.interp ltu R (Vis (inl1 e) k) m ≅ Tau (Global.interp ltu R (k x) m').
  Proof.
    intros Hs. rewrite interp_unfold_any. cbn.
    rewrite (handle_hstep_some ltu e m (m', x) Hs), bind_ret_l. reflexivity.
  Qed.

  (** Any other event is passed through, the store unchanged. *)
  Lemma interp_vis_inr {X R} (f : E X)
    (k : X -> itree (Global.Event T V +' E) R) (m : M) :
    Global.interp ltu R (Vis (inr1 f) k) m
    ≅ Vis f (fun x => Tau (Global.interp ltu R (k x) m)).
  Proof.
    rewrite interp_unfold_any. cbn. rewrite bind_bind, bind_trigger.
    apply eqit_Vis. intros x. apply (bind_ret_l (m, x)).
  Qed.

End InterpAnyStore.


