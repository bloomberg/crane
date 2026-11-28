(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Equational laws for [Global.interp]: how it unfolds on [Ret], [Tau],
    [Vis], [trigger] and [bind], under strong and weak bisimulation. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Init.Peano
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


