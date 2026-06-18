(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

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

From Crane Require Import Monads.ITree Utils.HMap Utils.HAList Extraction Monads.STMonad.
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


(* TODO: refactor for new world of generalized indices. *)
Section InterpSTTheorems.

  Context {E : Type -> Type}.
  Context {T S : Type}.
  Variable (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{STRefClass T}.
  Context {V : T -> Type}.
  Context `{STEvent T S V -< E}. 
  Context `{exceptE Err -< E}.


  Definition mem := halist (@idx_key T T) (idx_key_type V).

  
  Context `{HMap (@idx_key T T) (idx_key_type V) mem}.



  Definition _interp_st {R}
    (ot : itree' (STEvent T S V +' E) R)
    (l : mem)
    : itree E (mem * R) :=
    match ot with
    | RetF r => ret (l, r)
    | TauF t => Tau (interp_st ltu _ t l)
    | @VisF _ _ _ X e k =>
        x <- handle_STEvent_leave_rest ltu X e l;;
        Tau (interp_st _ _ (k (snd x)) (fst x))
    end.

  Lemma unfold_interp_st {R}
    (t : itree (STEvent T S V +' E) R)
    (l : mem) :
    eq_itree eq
    (interp_st _ _ t l)
    (_interp_st (observe t) l).
  Proof using Type.
    unfold interp_st, interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter.
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

  (* TODO: cleanup following 3 to remove @. *)
  Lemma interp_st_ret:  forall {R : Type} (val: R) (l : mem),
      @interp_st E T S ltu _ _ _ _ _ _ _ _ _ (ret val) l ≅ ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret: forall {R : Type} (val: R) (l : mem),
      @interp_st E T S ltu _ _ _ _ _ _ _ _ _ (Ret val) l ≅ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret_eutt: forall {R : Type} (val: R) (l : mem),
      @interp_st E T S ltu _ _ _ _ _ _ _ _ _ (Ret val) l ≈ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_vis
    {R U} 
    (e : (STEvent T S V +' E) R)
    (k : R -> itree (STEvent T S V +' E) U)
    (l : mem)
    : interp_st ltu _ (Vis e k) l
    ≅ x <- handle_STEvent_leave_rest ltu _ e l;;
      Tau (interp_st ltu _ (k (snd x)) (fst x)).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

    
  Lemma interp_st_tau {R : Type}
      (t : itree (STEvent T S V +' E) R)
      (l : mem)
      : interp_st ltu _ (Tau t) l ≅ Tau (interp_st ltu _ t l).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.


  Lemma Ret_is_ret {R : Type} (x : R) : ((Ret x) : itree E R)  = ret x.
    Proof using Type. reflexivity. Qed.
    
  Lemma interp_st_trigger
    {R : Type} 
    (e : (STEvent T S V +' E) R)
    (l : mem) :
    interp_st ltu _ (ITree.trigger e) l ≈ handle_STEvent_leave_rest ltu _ e l.
    Proof using Type.
      unfold ITree.trigger.
      rewrite interp_st_vis.
      match goal with
        |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst
      end.
      eapply eqit_bind; try reflexivity.
      intros [].
      - setoid_rewrite tau_eutt.
        unfold snd, fst.
        apply interp_st_Ret_eutt.
    Qed.

    
Definition eq_itree_eqv_global {R E} (x1 x2 : itree (E) (mem * R)) : Prop :=
  @eq_itree (E) _ _ eq x1 x2.


Global Instance eq_itree_interp_st {R : Type} :
Proper (@eq_itree (STEvent T S V +' E) R R eq ==> eq ==> eq_itree_eqv_global)
        (interp_st ltu R).
Proof.
  repeat red.
  ginit. pcofix CIH. intros x y Heq s1 s2 Hseq.
  rewrite !unfold_interp_st. punfold Heq. red in Heq.
    destruct Heq; subst; pclearbot; try discriminate; cbn.
    - gstep; constructor; auto.
    - gstep; constructor; auto with paco.
    - guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros [] ? <-. gstep.
        constructor; auto with paco itree.
  Qed.

    
Lemma interp_st_bind {U R} 
  (t : itree (STEvent T S V +' E) R)
  (k : R -> itree (STEvent T S V +' E) U)
  (mem : mem)
  : interp_st ltu U (ITree.bind t k) mem
      ≅ '(new_mem, new_val) <- interp_st ltu R t mem;;
    interp_st ltu U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : interp_st ltu U (ITree.bind t k) mem
                        ≅ interp_st ltu U (bind_ t k) mem).
  { apply eq_itree_interp_st. apply unfold_bind. reflexivity.  }
  rewrite unfold_bind'.
  rewrite (unfold_interp_st t mem).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn. apply reflexivity.
  - rewrite interp_st_tau. cbn. rewrite bind_tau.
    gstep. econstructor; eauto with paco.
  - rewrite interp_st_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. destruct u2 eqn:Equ2.
      rewrite bind_tau.
      gstep. constructor.
      auto with paco.
Qed.

Lemma interp_st_bind_eutt {U R} 
  (t : itree (STEvent T S V +' E) R)
  (k : R -> itree (STEvent T S V +' E) U)
  (mem : mem)
  : interp_st ltu U (ITree.bind t k) mem
      ≈ '(new_mem, new_val) <- interp_st ltu R t mem;;
    interp_st ltu U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : interp_st ltu U (ITree.bind t k) mem
                        ≅ interp_st ltu U (bind_ t k) mem).
  { apply eq_itree_interp_st. apply unfold_bind. reflexivity.  }
  rewrite unfold_bind'.
  rewrite (unfold_interp_st t mem).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn. apply reflexivity.
  - rewrite interp_st_tau. cbn. rewrite bind_tau.
    gstep. econstructor; eauto with paco.
  - rewrite interp_st_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. destruct u2 eqn:Equ2.
      rewrite bind_tau.
      gstep. constructor.
      auto with paco.
Qed.

Lemma interp_st_bind_eutt' {U R} 
  (t : itree (STEvent T S V +' E) R)
  (k : R -> itree (STEvent T S V +' E) U)
  (mem : mem)
  : (interp_st ltu U (ITree.bind t k) mem)
      ≈ '(new_mem, new_val) <- interp_st ltu R t mem;;
    interp_st ltu U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : interp_st ltu U (ITree.bind t k) mem
                        ≅ interp_st ltu U (bind_ t k) mem).
  { apply eq_itree_interp_st. apply unfold_bind. reflexivity.  }
  rewrite unfold_bind'.
  rewrite (unfold_interp_st t mem).
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn. apply reflexivity.
  - rewrite interp_st_tau. cbn. rewrite bind_tau.
    gstep. econstructor; eauto with paco.
  - rewrite interp_st_vis. cbn. rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros u2 ? []. destruct u2 eqn:Equ2.
      rewrite bind_tau.
      gstep. constructor.
      auto with paco.
Qed.


Lemma eutt_eq_bind_interp_st {U R}
  (k2 : (mem * R) -> itree E (mem * U))
  (lmem : mem)
  (t1 : itree (STEvent T S V +' E) R)
  (t2 : itree E (mem * R))
  (k1: R -> itree (STEvent T S V +' E) U)
  :
  interp_st ltu R t1 lmem ≈ t2 ->
  (forall u lmem', interp_st ltu U (k1 u) lmem' ≈ (k2 (lmem', u))) ->
  interp_st ltu U (ITree.bind t1 k1) lmem
  ≈
  ITree.bind t2 k2.
Proof.
  intros t1_eq keq.
  rewrite (interp_st_bind_eutt t1 k1).                                                                                
  apply eutt_eq_bind'; [assumption | intuition].
Qed.

End InterpSTTheorems.

Lemma IdxRefSameIdx : forall (n : nat) S A,
  STRefToIx S A (mkSTRef S A n) = n.
Proof. reflexivity. Qed.

Section STLookupErr.

  Context {E : Type -> Type}.
  Context {S T : Type}.
  Context `{exceptE Err -< E}.
  Context {R : Type}.
  Context {map : Type}.
  Context {V : T -> Type}.

  Context {hmap : HMap T V map}.
  Context {MOK : HMapOk hmap}.


  (* TODO: generalize, move to utils/HMap. *)
  Lemma st_lookup_add_eq : forall k v s, lookup k (add k v s) = Some v.
    Proof.
    intros.
    rewrite mapsto_lookup; apply mapsto_add_eq. 
    Unshelve. assumption.
    Qed.

  Lemma st_lookup_remove_eq :
    forall k s, lookup k (HMap.remove k s) = None.
  Proof using MOK.
    intros.
    destruct (lookup k (HMap.remove k s)) eqn:EQ.
    - inversion MOK. 
      rewrite mapsto_lookup in EQ.
      exfalso.
      eapply mapsto_remove_eq; eauto.
    - reflexivity.
    Qed.


End STLookupErr.


Section EquationalTheory.
  
  Context {E : Type -> Type}.

  Lemma eutt_fmap {R U : Type} {t1 t2 : itree E R} {f : R -> U} :
    t1 ≈ t2 ->
    fmap f t1 ≈ fmap f t2.
    Proof using Type.
      intros t_eq. apply eqit_map with (RR := eq).
      + intros.
        f_equal. assumption.
      + apply t_eq.
    Qed.

  Lemma eutt_eq_bind {U R} (t : itree E U) (k1 k2: U -> itree E R):
    (forall u, (k1 u) ≈ (k2 u)) ->
    (ITree.bind t k1) ≈ (ITree.bind t k2).
  Proof using Type. apply eutt_eq_bind. Qed.

  Lemma eutt_eq_bind' {U R}
    (k1 k2: U -> itree E R)
    (t1 t2: itree E U):
    t1 ≈ t2 ->
    (forall u, (k1 u) ≈ (k2 u)) ->
    (ITree.bind t1 k1) ≈ (ITree.bind t2 k2).
  Proof. apply eutt_eq_bind'. Qed.


Theorem bind_Ret_l : forall A B (f : A -> itree E B) (x : A), bind (Ret x) f ≈ f x.
  setoid_rewrite Ret_is_ret.
  setoid_rewrite Monad.bind_ret_l.
  reflexivity.
  Qed.
          

Theorem bind_Ret_r : forall A (x : itree E A), bind x (fun y => Ret y) ≈ x.
  intros A x. setoid_rewrite Monad.bind_ret_r. reflexivity. Qed.

End EquationalTheory.


Ltac refine_prod :=
  (refine (fun '(a,b) => _)).

Ltac refine_arg :=
  (refine (fun arg => _)).

Ltac refine_arg2 :=
  (refine (fun arg1 arg2 => _)).


Ltac monad_simpl_inner :=
  repeat (repeat setoid_rewrite Monad.bind_bind;
          repeat setoid_rewrite bind_Ret_l;
          repeat setoid_rewrite bind_Ret_r).



(* Useful for lifting ITree's back to a monad instance. *)
Ltac change_to_monad :=
  change (@ITree.bind ?E) with (@Monad.bind (itree E) _);
  try setoid_rewrite Ret_is_ret.

Ltac bind_split_refl_intros split_tactic :=
  split_tactic ;[ reflexivity | intros]
  ;cbv beta match.
