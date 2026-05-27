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

From Crane Require Import Monads.ITree Utils.HMap Utils.HAList Extraction.
From ExtLib Require Import
  Data.Bool
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Structures.Functor
  Structures.Traversable
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


(* Used for runtime checks, though an ideal impl won't need these. *)

Variant Err : Type :=
| Error (x : string) : Err.

Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).


Module Type ST_SIG.

  Parameter Idx : forall (S : Type), Type.
  Parameter STRef : forall S A : Type, Type. 
  Parameter IdxDecEq : forall (S : Type) (i1 i2 : Idx S),  
      {i1 = i2} + {i1 <> i2}.
  Parameter mkSTRef : forall S A : Type, Idx S -> STRef S A.
  Parameter STRefToIdx : forall (S A : Type), STRef S A -> Idx S. 
  Parameter STEvent : forall S : Type, (Idx S -> Type) -> Type -> Type.
  Parameter newSTRef : forall {E : Type -> Type} {S : Type}
                         (V : (Idx S -> Type)) `{STEvent S V -< E}
                         (I : Idx S),
      V I -> itree E (STRef S (V I)).
  Parameter readSTRef : forall {E : Type -> Type} {S : Type} 
                        (V : Idx S -> Type) `{STEvent S V -< E}
                        (I : Idx S),
      STRef S (V I) -> itree E (V I).
  Parameter writeSTRef : forall {E : Type -> Type} {S : Type} 
                        (V : Idx S -> Type) `{STEvent S V -< E}
                        (I : Idx S),
      STRef S (V I) -> V I -> itree E unit.

  (* Used to generate fresh, unique indices.*)
  Parameter IdxGenE : Type -> Type.
  Parameter newIdx :
    forall {S : Type}
      {E : Type -> Type} `{IdxGenE -< E}
      , itree E (Idx S). 

  (* TODO: better naming... *)
  Parameter IdxRefSameIdx: forall (S A : Type) (idx : Idx S), (STRefToIdx S A (mkSTRef S A idx)) = idx.
  Parameter IdxRefSameRef: forall (S A : Type) (ref : STRef S A), (mkSTRef S A (STRefToIdx S A ref)) = ref.

  (* TODO: indices are ordered. *)
  (* TODO: indices are unique. *)

End ST_SIG.


Module ST_IMPL : ST_SIG.

  Variant STRef' : Type -> Type -> Type :=
    | MkStRef (S A : Type) (idx : nat) : STRef' S A.

  Definition STRef := STRef'. 

  Definition Idx (S : Type) := nat.


  Definition mkSTRef := MkStRef.

  Definition IdxDecEq (S : Type) (i1 i2 : Idx S)
    : {i1 = i2} + {i1 <> i2} := Nat.eq_dec i1 i2.

  Definition STRefToIdx (S A : Type) (ref : STRef' S A) : Idx S :=
   match ref with
   | MkStRef _ _ idx => idx
   end. 

  Inductive GenNum : Type -> Type :=
  | NewNat : GenNum nat.

  Definition IdxGenE := GenNum.

  Definition newIdx {S : Type}
    {E : Type -> Type} `{IdxGenE -< E} 
    : itree E (Idx S) := trigger NewNat.


  Lemma IdxRefSameIdx : forall (S A : Type) (idx : Idx S), (STRefToIdx S A (mkSTRef S A idx)) = idx.
  Proof. intros. cbn. reflexivity. Qed.
         
  Lemma IdxRefSameRef : forall (S A : Type) (ref : STRef S A), (mkSTRef S A (STRefToIdx S A ref)) = ref.
  Proof. intros. cbn. unfold STRefToIdx. destruct ref. reflexivity. Qed.
  



  Variant STEvent' (S : Type) {V : (Idx S) -> Type} : Type -> Type :=
    | NewSTRef (I : Idx S) (v : V I) : STEvent' S (STRef S (V I))
    | ReadSTRef (I : Idx S) : STRef S (V I) -> STEvent' S (V I)
    | WriteSTRef (I : Idx S) : STRef S (V I) -> (V I) -> STEvent' S unit
  .

  Definition STEvent := STEvent'.


  

Section Translation.

  Context {E : Type -> Type}.
  Context {S : Type}.
  Context {V : (Idx S) -> Type}.
  Context `{@STEvent S V -< E}. 
  Context `{exceptE Err -< E}.
  Context `{IdxGenE -< E}.

  
  Definition lookup_err
    {V : (Idx S) -> Type}
    {map} `{HMap (Idx S) V map}
    (k : (Idx S)) (mem : map) : itree E (V k) :=
    match lookup k mem with
      | None => throw (Error "Failed to find key in map")
      | Some v => Ret v
    end.

  
  Definition newSTRef {I : Idx S} (v : (V I)) : itree E (STRef' S (V I)) :=
    trigger (NewSTRef S I v). 

  Definition readSTRef {I : Idx S} (ref : STRef' S (V I)) : itree E (V I) :=
    trigger (ReadSTRef S I ref).

  Definition writeSTRef {I : Idx S} (ref : STRef' S (V I)) (a : (V I)) : itree E unit :=
    trigger (WriteSTRef S I ref a).


  (* TODO: cleanup! *)
  Definition handle_STEvent
    {map} `{HMap (Idx S) V map}
    : forall (T : Type), @STEvent S V T -> stateT map (itree E) T :=
    fun T e mem =>
      match e in (STEvent' _ T0) return (itree E (map * T0)) with
      | NewSTRef _ Id v =>
        idx <- @newIdx S E _;;
        Ret (add Id v mem, MkStRef S (V Id) idx)
      | ReadSTRef _ Id s =>
        v <- lookup_err Id mem;;
        Ret (mem, v)
      | WriteSTRef _ Id s v =>
        Ret (add Id v mem, tt)
      end.



(* Example Programs*)





(* Interpretation in Rocq *)



  (* TODO: better name perhaps *)
  Definition handle_STEvent_leave_rest
    {mem} `{HMap (Idx S) V mem}
    (T : Type) (e : (STEvent' S +' E) T)
    : stateT mem (itree (E)) T :=
    match e with
    | inl1 e0 => handle_STEvent T e0
    | inr1 e0 => fun st : mem => r <- trigger e0;; Ret (st, r)
    end.


  Global Instance reldec_idx {S : Type} : @RelDec.RelDec (Idx S) eq :=
    (RelDec.RelDec_from_dec eq (IdxDecEq S)).

  Global Instance hmap_from_idx :
    HMap (Idx S) V (halist (Idx S) V) :=
    @HMap_halist (Idx S) V eq_equivalence (IdxDecEq S).

  Global Instance reldec_idx_correct : @RelDec.RelDec_Correct (Idx S) eq reldec_idx.
  econstructor.
  intuition.
  destruct (IdxDecEq S x y) eqn:Hdec.
  - destruct IdxDecEq in Hdec; try assumption.
  - specialize (@reldec_idx S) as reldec.
    specialize (IdxDecEq S x y) as dec.
    destruct dec.
    + contradiction.
    + unfold RelDec.rel_dec in *. unfold reldec_idx in *. unfold RelDec.RelDec_from_dec in *.
      destruct (IdxDecEq S x y); try assumption.
      discriminate H2.
  - unfold RelDec.rel_dec in *. unfold reldec_idx in *. unfold RelDec.RelDec_from_dec in *.
    destruct (IdxDecEq S x y); try assumption.
    + reflexivity.
    + contradiction.
  Qed.


  Global Instance map_idx_correct :
    HMapOk hmap_from_idx := HMapOk_halist (Idx S) V.


  Definition interp_st
    {mem} `{HMap (Idx S) V mem}
    : itree (STEvent' S +' E) ~> stateT mem (itree (E)) :=
    interp_state handle_STEvent_leave_rest.

  
End Translation.

  Definition runSt {A : Type}
  {E : Type -> Type}
  {S : Type}
  {V : (Idx S) -> Type}
  `{@STEvent S V -< E} 
  `{exceptE Err -< E}
  `{IdxGenE -< E}
    (f : forall (S : Type), itree ((@STEvent S V) +' E) A)
    : itree E A :=
    fmap snd (interp_st _ (f unit) HMap.empty).
  

Section InterpSTTheorems.

  Context {E : Type -> Type}.
  Context {S : Type}.
  Context {V : (Idx S) -> Type}.
  Context `{@STEvent S V -< E}. 
  Context `{exceptE Err -< E}.
  Context `{IdxGenE -< E}.

  Definition mem := halist (Idx S) V.

  Global Instance mem_instance : 
    HMap (Idx S) V mem := @hmap_from_idx S V.

  Definition _interp_st {T : Type}
    (ot : itree' (STEvent' S +' E) T)
    (l : mem)
    : itree E (mem * T) :=
    match ot with
    | RetF r => ret (l, r)
    | TauF t => Tau (interp_st _ t l)
    | @VisF _ _ _ X e k =>
        x <- handle_STEvent_leave_rest X e l;;
        Tau (interp_st _ (k (snd x)) (fst x))
    end.

  Lemma unfold_interp_st {T : Type}
    (t : itree (STEvent' S +' E) T)
    (l : mem) :
    eq_itree eq
    (interp_st _ t l)
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
      @interp_st E S _ _ _ _ _ _ (ret val) l ≅ ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret: forall {R : Type} (val: R) (l : mem),
      @interp_st E S _ _ _ _ _ _ (Ret val) l ≅ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret_eutt: forall {T : Type} (val: T) (l : mem),
      @interp_st E S _ _ _ _ _ _ (Ret val) l ≈ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_vis
    {T U} 
    (e : (STEvent' S +' E) T)
    (k : T -> itree (STEvent' S +' E) U)
    (l : mem)
    : interp_st _ (Vis e k) l
    ≅ x <- handle_STEvent_leave_rest _ e l;;
      Tau (interp_st _ (k (snd x)) (fst x)).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

    
  Lemma interp_st_tau {T : Type}
      (t : itree (STEvent' S +' E) T)
      (l : mem)
      : interp_st _ (Tau t) l ≅ Tau (interp_st _ t l).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.


  Lemma Ret_is_ret {R : Type} (x : R) : ((Ret x) : itree E R)  = ret x.
    Proof using Type. reflexivity. Qed.
    
  Lemma interp_st_trigger
    {T : Type} 
    (e : (STEvent' S +' E) T)
    (l : mem) :
    interp_st _ (ITree.trigger e) l ≈ handle_STEvent_leave_rest _ e l.
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


Global Instance eq_itree_interp_st {T : Type} : 
Proper (@eq_itree (STEvent' S +' E) T T eq ==> eq ==> eq_itree_eqv_global)
        (interp_st T).
Proof using Type.
  repeat red.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_st. punfold H3. red in H3.
    destruct H3; subst; pclearbot; try discriminate; cbn.
    - gstep; constructor; auto.
    - gstep; constructor; auto with paco.
    - guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros. gstep. rewrite H2. destruct u2 eqn:Equ2.
        constructor; auto with paco itree.
  Qed.

    
Lemma interp_st_bind {U R} 
  (t : itree (STEvent' S +' E) R)
  (k : R -> itree (STEvent' S +' E) U)
  (mem : mem)
  : interp_st U (ITree.bind t k) mem
      ≅ '(new_mem, new_val) <- interp_st R t mem;;
    interp_st U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : interp_st U (ITree.bind t k) mem
                        ≅ interp_st U (bind_ t k) mem).
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
  (t : itree (STEvent' S +' E) R)
  (k : R -> itree (STEvent' S +' E) U)
  (mem : mem)
  : interp_st U (ITree.bind t k) mem
      ≈ '(new_mem, new_val) <- interp_st R t mem;;
    interp_st U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : interp_st U (ITree.bind t k) mem
                        ≅ interp_st U (bind_ t k) mem).
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
  (t : itree (STEvent' S +' E) R)
  (k : R -> itree (STEvent' S +' E) U)
  (mem : mem)
  : (interp_st U (ITree.bind t k) mem)
      ≈ '(new_mem, new_val) <- interp_st R t mem;;
    interp_st U (k new_val) new_mem.
  revert t k mem.
  ginit. pcofix CIH.
  intros t k mem.
  assert (unfold_bind' : interp_st U (ITree.bind t k) mem
                        ≅ interp_st U (bind_ t k) mem).
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
  (t1 : itree (STEvent' S +' E) R)
  (t2 : itree E (mem * R))
  (k1: R -> itree (STEvent' S +' E) U)
  :
  interp_st R t1 lmem ≈ t2 ->
  (forall u lmem', interp_st U (k1 u) lmem' ≈ (k2 (lmem', u))) ->
  interp_st U (ITree.bind t1 k1) lmem
  ≈
  ITree.bind t2 k2.
Proof.
  intros t1_eq keq.
  rewrite (interp_st_bind_eutt t1 k1).                                                                                
  apply eutt_eq_bind'; [assumption | intuition].
Qed.

End InterpSTTheorems.


Section STLookupErr.

  Context {E : Type -> Type}.
  Context {S : Type}.
  Context `{exceptE Err -< E}.
  Context {R : Type}.
  Context {map : Type}.
  Context {V : (Idx S) -> Type}.

  (* Context {E : Type -> Type}.
   * Context {S : Type}.
   * Context {V : (Idx S) -> Type}.
   * Context `{@STEvent S V -< E}. 
   * Context `{exceptE Err -< E}.
   * Context `{IdxGenE -< E}. *)

  Context {hmap : HMap (Idx S) V map}.
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


  
  Lemma st_lookup_err_add_eq : forall (s : map) (k : Idx S) (v : (V k)),
      lookup_err k (HMap.add k v s) = @ret (itree E) _ _ v.
  Proof using MOK.
    intros. unfold lookup_err.
    inversion MOK.
    rewrite st_lookup_add_eq.
    reflexivity.
  Qed.

  Lemma st_lookup_err_remove_eq : forall (k : Idx S) (s : map),
      lookup_err k (HMap.remove k s) = @throw Err E _ _ (Error "Failed to find key in map").
  Proof using MOK.
    intros. unfold lookup_err.
    rewrite st_lookup_remove_eq.
    reflexivity.
  Qed.

End STLookupErr.


(* CPP Bindings *)

Crane Extract Inlined Constant STRef => "%t1".
Crane Extract Inlined Constant newSTRef => "%result = %a0".
Crane Extract Inlined Constant readSTRef => "%a0". 
Crane Extract Inlined Constant writeSTRef => "%a0 = %a1".
Crane Extract Skip IdxRefSameIdx.
Crane Extract Skip IdxRefSameRef.
Crane Extract Skip newIdx.

End ST_IMPL.

Export ST_IMPL.
