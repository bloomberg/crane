(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import
  Extraction
  Monads.Error
  Monads.ITree
  Monads.Indices
  Utils.HAList
  Utils.HMap
.

From ExtLib Require Import
  Data.Bool
  Structures.Functor
.

From ITree Require Import
  Events.Exception
  Events.MapDefault
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.

Import Monads.
Local Open Scope monad_scope.

Section HMapFacts.
  Context {K : Type} {V : K -> Type} {map : Type}.
  Context {hmap : HMap K V map}.
  Context {MOK : HMapOk hmap}.

  Lemma hmap_lookup_add_eq : forall k v s, lookup k (add k v s) = Some v.
  Proof. intros. rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. assumption. Qed.

  Lemma hmap_lookup_add_ne : forall k k' v s,
    k <> k' -> lookup k (add k' v s) = lookup k s.
  Proof using MOK.
    intros k k' v s Hne.
    set (Hne' := fun (H : k' = k) => Hne (eq_sym H)).
    destruct (lookup k (add k' v s)) eqn:EQ1;
    destruct (lookup k s) eqn:EQ2.
    - f_equal. rewrite mapsto_lookup in EQ1.
      eapply (@mapsto_add_neq _ _ _ _ MOK s k' v k Hne') in EQ1.
      apply (proj2 (@mapsto_lookup _ _ _ _ MOK k v0 s)) in EQ1. congruence.
    - exfalso. rewrite mapsto_lookup in EQ1.
      eapply (@mapsto_add_neq _ _ _ _ MOK s k' v k Hne') in EQ1.
      apply (proj2 (@mapsto_lookup _ _ _ _ MOK k v0 s)) in EQ1. congruence.
    - exfalso. rewrite mapsto_lookup in EQ2.
      eapply (@mapsto_add_neq _ _ _ _ MOK s k' v k Hne') in EQ2.
      apply (proj2 (@mapsto_lookup _ _ _ _ MOK k v0 (add k' v s))) in EQ2. congruence.
    - reflexivity.
  Qed.

  Lemma hmap_lookup_remove_eq :
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

End HMapFacts.

Section LookupErr.

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


End LookupErr.

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


Lemma Ret_is_ret {R : Type} (x : R) : ((Ret x) : itree E R)  = ret x.
  Proof using Type. reflexivity. Qed.

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
