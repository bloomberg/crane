(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Init.Peano
  Lia
  List
  Morphisms
  RelationClasses
  Relation_Definitions
  Setoid
  Strings.String
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

From Crane Require Import
  Extraction
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.STMonad
  Monads.MonadFacts
  Utils.HAList
  Utils.HMap
.


Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.


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

  Lemma interp_st_ret:  forall {R : Type} (val: R) (l : mem),
      interp_st (E := E) (S := S) _ _ (ret val) l ≅ ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret: forall {R : Type} (val: R) (l : mem),
      interp_st (E := E) (S := S) _ _ (Ret val) l ≅ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret_eutt: forall {R : Type} (val: R) (l : mem),
      interp_st (E := E) (S := S) _ _ (Ret val) l ≈ Ret (l, val).
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
  Proof using Type.
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

(* interp_st* theorems, specialized to nat indices *)
Section InterpSTTheoremsNat. 

  Context {E : Type -> Type}.
  Context {S : Type}.
  Let T := nat.
  Let ltu := Nat.le.
  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.


  (* only integer typed values here *)
  Let V : T -> Type := fun _ => nat.
  Context {HST : STEvent T S V -< E}. 
  Context {Hev : exceptE Err -< E}.
  

  (* Physical key of logical index [i] in an array with base/lo/hi. *)
  Lemma arr_key_val : forall (base lo hi i : T),
    lo <= i -> i <= hi ->
    @arr_key T S ltu nat_ix (fun _ : T => T) 0 (MkSTArray T S T base lo hi) i
    = Some (base + (i - lo)).
  Proof.
    intros base lo hi i Hlo Hhi. unfold arr_key. cbn -[Nat.sub].
    rewrite (proj2 (Nat.leb_le lo i) Hlo), (proj2 (Nat.leb_le i hi) Hhi).
    cbn -[Nat.sub]. f_equal.
    generalize (i - lo) as n; intro n.
    induction n as [|n' IH]; [ cbn; lia | ].
    cbn [suc_n suc nat_ix]. rewrite IH. lia.
  Qed.

  (* Representation: physical cells [base .. base+|full|-1] (idx 0) hold [full]. *)
  Definition arr_rep (m : @mem T V) (base : T) (full : list T) : Prop :=
    forall k, k < length full -> lookup (base + k, 0%nat) m = Some (nth k full 0).

  Lemma arr_key_val0 : forall (base hi i : T),
    i <= hi ->
    @arr_key nat S ltu nat_ix (fun _ : nat => nat) 0 (MkSTArray nat S nat base 0 hi) i
    = Some (base + i).
  Proof. intros. rewrite arr_key_val by lia. f_equal. lia. Qed.

  Lemma arr_lookup_rep : forall base hi full i m,
    arr_rep m base full -> i <= hi -> hi < length full ->
    @arr_lookup nat S ltu nat_ix (fun _ : nat => nat) mem _ 0
       (MkSTArray nat S nat base 0 hi) i m
    = Some (nth i full 0).
  Proof.
    intros base hi full i m Hrep Hih Hhl. unfold arr_lookup.
    rewrite arr_key_val by lia.
    replace (i - 0) with i by lia. apply Hrep. lia.
  Qed.

  (* Pure list update, for modelling in-place writes. *)
  Fixpoint upd (l : list nat) (i v : nat) : list nat :=
    match l, i with
    | nil, _ => nil
    | _ :: t, 0 => v :: t
    | h :: t, Datatypes.S i' => h :: upd t i' v
    end.

  Lemma upd_length : forall l i v, length (upd l i v) = length l.
  Proof. induction l; intros [|i] v; simpl; auto. Qed.

  Lemma nth_upd_eq : forall l i v, i < length l -> nth i (upd l i v) 0 = v.
  Proof. induction l; intros [|i] v Hb; simpl in *; try lia; auto. apply IHl; lia. Qed.

  Lemma nth_upd_neq : forall l i j v, i <> j -> nth j (upd l i v) 0 = nth j l 0.
  Proof.
    induction l as [|a l IHl]; intros i j v H.
    - destruct j; reflexivity.
    - destruct i as [|i]; destruct j as [|j]; simpl.
      + exfalso; lia.
      + reflexivity.
      + reflexivity.
      + apply IHl; lia.
  Qed.

  Lemma arr_rep_write : forall base full i v m,
    arr_rep m base full -> i < length full ->
    arr_rep (add (base + i, 0%nat) v m) base (upd full i v).
  Proof.
    intros base full i v m Hrep Hi k Hk. rewrite upd_length in Hk.
    destruct (Nat.eq_dec k i).
    - subst k. rewrite hmap_lookup_add_eq. rewrite nth_upd_eq by lia. reflexivity.
    - rewrite hmap_lookup_add_ne by (intros [=]; lia).
      rewrite nth_upd_neq by lia. apply Hrep. auto.
  Qed.

  Definition list_swap (l : list nat) (i j : nat) : list nat :=
    upd (upd l i (nth j l 0)) j (nth i l 0).

  Lemma list_swap_length : forall l i j, length (list_swap l i j) = length l.
  Proof. intros. unfold list_swap. rewrite !upd_length. reflexivity. Qed.

  Lemma arr_rep_swap : forall base full left right m,
    arr_rep m base full -> left < length full -> right < length full ->
    arr_rep (add (base + right, 0%nat) (nth left full 0)
              (add (base + left, 0%nat) (nth right full 0) m))
            base (list_swap full left right).
  Proof.
    intros base full left right m Hrep Hl Hr. unfold list_swap.
    apply arr_rep_write; [ apply arr_rep_write; auto | rewrite upd_length; auto ].
  Qed.

  (* Pointwise reads of a swapped list. *)
  Lemma nth_list_swap_left : forall l i j,
    i < length l -> nth i (list_swap l i j) 0 = nth j l 0.
  Proof.
    intros l i j Hi. unfold list_swap. destruct (Nat.eq_dec i j).
    - subst j. rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
    - rewrite nth_upd_neq by lia. rewrite nth_upd_eq by lia. reflexivity.
  Qed.

  Lemma nth_list_swap_right : forall l i j,
    j < length l -> nth j (list_swap l i j) 0 = nth i l 0.
  Proof.
    intros l i j Hj. unfold list_swap.
    rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
  Qed.

  Lemma nth_list_swap_other : forall l i j k,
    k <> i -> k <> j -> nth k (list_swap l i j) 0 = nth k l 0.
  Proof.
    intros l i j k Hi Hj. unfold list_swap.
    rewrite nth_upd_neq by lia. rewrite nth_upd_neq by lia. reflexivity.
  Qed.

End InterpSTTheoremsNat.


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
