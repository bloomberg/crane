(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Monads.ITree.
From ExtLib Require Import
  Structures.Maps
  Structures.Functor
  Data.Map.FMapAList
.

From ExtLib Require Import
     Structures.Maps
     Structures.Traversable
     Data.Monads.EitherMonad
     Data.List
     Data.Pair
     Data.Bool
     Data.Map.FMapAList
     Data.String
.

From ITree Require Import
  ITree
  ITreeFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.Exception
  Events.FailFacts
  Events.State
  Eq.Paco2
  Basics.HeterogeneousRelations
  HasPost
.
From Stdlib Require Import
  List
  Strings.String
.


(* TODO: nit; organize imports *)
From ITree Require Import
  ITree
  ITreeFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.Exception
  Events.FailFacts
  Events.State
.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Events.StateFacts
  Events.Exception
  Events.State
  Eq.Paco2
  Basics.HeterogeneousRelations
  HasPost
.

Import Monads.
Import ListNotations.
From Stdlib Require Import
  Morphisms
  Setoid
  Relation_Definitions
  RelationClasses
  Arith.PeanoNat
  Arith.Peano_dec
  Init.Peano
.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.



Module Type ST_SIG.

  Parameter Idx : forall (S : Type), Type.
  Parameter STRef : forall S A : Type, Type. 
  Parameter IdxDecEq : forall (S : Type) (i1 i2 : Idx S),  
      {i1 = i2} + {i1 <> i2}.
  (* TODO: can we tie the result index to the stref here? *)
  Parameter mkSTRef : forall S A : Type, Idx S -> STRef S A.
  Parameter STRefToIdx : forall (S A : Type), STRef S A -> Idx S. 


  (* Used to generate fresh, unique indices.*)
  Parameter IdxGenE : Type -> Type.
  Parameter newIdx :
    forall {S : Type}
      {E : Type -> Type} `{IdxGenE -< E}
      , itree E (Idx S). 

  (* TODO: better naming... *)
  Parameter IdxRefSameIdx: forall (S A : Type) (idx : Idx S), (STRefToIdx S A (mkSTRef S A idx)) = idx.
  Parameter IdxRefSameRef: forall (S A : Type) (ref : STRef S A), (mkSTRef S A (STRefToIdx S A ref)) = ref.


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
  

End ST_IMPL.

Import ST_IMPL.

(* TODO: Expand to cover more types than nat *)
Variant STEvent (S : Type) : Type -> Type :=
  | NewSTRef (v : nat) : STEvent S (STRef S nat)
  | ReadSTRef : STRef S nat -> STEvent S nat
  | WriteSTRef : STRef S nat -> nat -> STEvent S unit
.


(* Used for runtime checks, though an ideal impl won't need these. *)

Variant Err : Type :=
| Error (x : string) : Err.

Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).
  

Section Translation.

  Context {E : Type -> Type}.
  Context {S : Type}.
  Context `{STEvent S -< E}. 

  
  Definition lookup_err
    {E : Type -> Type} {R : Type}
    `{exceptE Err -< E}
    {map} `{Map (Idx S) R map}
    (k : (Idx S)) (mem : map) : itree E R :=
    match lookup k mem with
      | None => throw (Error "Failed to find key in map")
      | Some v => Ret v
    end.

  
  Definition newSTRef (v : nat) : itree E (STRef S nat) :=
    trigger (NewSTRef S v). 

  Definition readSTRef (ref : STRef S nat) : itree E nat :=
    trigger (ReadSTRef S ref). 

  Definition writeSTRef (ref : STRef S nat) (a : nat) : itree E unit :=
    trigger (WriteSTRef S ref a).


  Definition handle_STEvent
    {map} `{Map (Idx S) nat map}
    `{IdxGenE -< E} `{exceptE Err -< E}
    : forall (T : Type),  STEvent S T -> stateT map (itree E) T :=
    fun T e mem =>
    match e in (STEvent _ T0) return (itree E (map * T0)) with
    | NewSTRef _ v => idx <- newIdx;; Ret (add idx v mem, mkSTRef S nat idx)
    | ReadSTRef _ s =>
        let idx := STRefToIdx S nat s in v <- lookup_err idx mem;; Ret (mem, v)
    | WriteSTRef _ s n => let idx := STRefToIdx S nat s in Ret (add idx n mem, tt)
    end.

End Translation.

(* Example Programs*)
Section ExampleTrees.

  Context {S : Type}.
  Context {E : Type -> Type}.
  Context `{IdxGenE -< E}.
  Context `{exceptE Err -< E}.


  Definition E0 := STEvent S +' E.

  Definition newAndReadBoth : itree E0 (nat * nat) :=
    r1 <- newSTRef 5 ;;
    r2 <- newSTRef 6 ;;
    x1 <- readSTRef r1 ;;
    x2 <- readSTRef r2 ;;
    Ret (x1, x2).

  Definition tree_simp : itree E0 nat :=
    v <- newSTRef 5;;
    readSTRef v.

  (* NOTE: this failing definition is intentional, it should fail.
    The intent is to test that we don't allow reference indices to escape. *)
  Fail Definition tree_escape_example : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v (match v with mkSTRef _ _ idx => idx end);;
    readSTRef v.

  Definition tree_simp_another : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v 6;;
    val <- readSTRef v;;
    Ret val.


End ExampleTrees.




Section MemoryRep.

Inductive node : Type := (* TODO: More types! *)
  | NInt (x : nat) : node.


Fixpoint node_to_type (n : node) : Type :=
  match n with
  | NInt x => nat
  end.


Class Convertible t := {
    to_node : t -> node;
    from_node: node -> option t;
    node_convert_inverse: forall v : t, (from_node (to_node v)) = Some v
  }.


End MemoryRep.

(* Interpretation in Rocq *)


Section InterpST.



  (* TODO: better name perhaps *)
  Definition handle_STEvent_leave_rest
    {S : Type}
    {mem} `{Map (Idx S) nat mem}
    {E : Type -> Type} `{exceptE Err -< E} `{IdxGenE -< E}
    (T : Type) (e : (STEvent S +' E) T)
    : stateT mem (itree (E)) T :=
    match e with
    | inl1 e0 => handle_STEvent T e0
    | inr1 e0 => fun st : mem => r <- trigger e0;; ret (st, r)
    end.


  Global Instance reldec_idx {S : Type} : @RelDec.RelDec (Idx S) eq :=
    (RelDec.RelDec_from_dec eq (IdxDecEq S)).
    
  Global Instance map_from_idx {S : Type} {V : Type}  : 
    Map (Idx S) V (alist (Idx S) V) :=
    Map_alist (RelDec.RelDec_from_dec eq (IdxDecEq S)) V.

  Global Instance reldec_idx_correct {S : Type} : @RelDec.RelDec_Correct (Idx S) eq reldec_idx.
  econstructor.
  intuition.
  destruct (IdxDecEq S x y); try assumption.
  - unfold RelDec.rel_dec in H. cbn in H.
    destruct IdxDecEq in H.
    + contradiction.
    + discriminate H.
  - cbn.
    specialize (@reldec_idx S) as reldec.
    specialize (IdxDecEq S x y) as dec.
    destruct dec.
    + unfold RelDec.rel_dec. unfold reldec_idx. unfold RelDec.RelDec_from_dec.
      destruct (IdxDecEq S x y).
      * reflexivity.
      * contradiction.
    + contradiction.
    Qed.


  Global Instance map_idx_correct {S V : Type} :
    MapOk eq (@map_from_idx S V).
  unfold map_from_idx.
  eapply MapLaws_alist; typeclasses eauto.
  Qed.

  Definition interp_st
    {E : Type -> Type} {S : Type}
    `{exceptE Err -< E} `{IdxGenE -< E}
    {mem} `{Map (Idx S) nat mem}
    : itree (STEvent S +' E) ~> stateT mem (itree (E)) :=
    interp_state handle_STEvent_leave_rest.

  
  (* TODO: cleanup! *)
  (* TODO: refactor to use interp_map? *)
  Definition runSt {A : Type} {E : Type -> Type}
     `{exceptE Err -< E} `{IdxGenE -< E}
    (f : forall (S : Type), itree ((STEvent S) +' E) A)
    : itree E A :=
    fmap snd (interp_st _ (f unit) Maps.empty).

  
  

End InterpST.



Section InterpSTTheorems.

  (* TODO: refactor to above. *)
  Context {E : Type -> Type}. (* other events *)
  Context {S : Type}. (* state thread *)
  Context `{exceptE Err -< E}. (* runtime checks  *)
  Context `{IdxGenE -< E}. (* index generating event *)
  Context {R : Type}. (* values contained in the map,  TODO: expand from one value type. *)

  Definition mem := alist (Idx S) nat. 
  Global Instance mem_instance {V : Type} : 
    Map (Idx S) V (alist (Idx S) V) :=
    Map_alist (RelDec.RelDec_from_dec eq (IdxDecEq S)) V.


  Definition _interp_st {T : Type}
    (ot : itree' (STEvent S +' E) T)
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
    (t : itree (STEvent S +' E) T)
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

  Lemma interp_st_ret: forall (val: R) (l : mem),
      @interp_st E S _ _ _ _ _ (ret val) l ≅ ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret: forall (val: R) (l : mem),
      @interp_st E S _ _ _ _ _ (Ret val) l ≅ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret_eutt: forall {T : Type} (val: T) (l : mem),
      @interp_st E S _ _ _ _ _ (Ret val) l ≈ Ret (l, val).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_vis
    {T U} 
    (e : (STEvent S +' E) T)
    (k : T -> itree (STEvent S +' E) U)
    (l : mem)
    : interp_st _ (Vis e k) l
    ≅ x <- handle_STEvent_leave_rest _ e l;;
      Tau (interp_st _ (k (snd x)) (fst x)).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

    
  Lemma interp_st_tau {T : Type}
      (t : itree (STEvent S +' E) T)
      (l : mem)
      : interp_st _ (Tau t) l ≅ Tau (interp_st _ t l).
    Proof using Type.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.


  Lemma Ret_is_ret (x : R) : ((Ret x) : itree E R)  = ret x.
    Proof using Type. reflexivity. Qed.
    
  Lemma interp_st_trigger
    {T : Type} 
    (e : (STEvent S +' E) T)
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
Proper (@eq_itree (STEvent S +' E) T T eq ==> eq ==> eq_itree_eqv_global)
        (interp_st T).
Proof using Type.
  repeat red.
  ginit. pcofix CIH. intros.
  rewrite !unfold_interp_st. punfold H2. red in H2.
    destruct H2; subst; pclearbot; try discriminate; cbn.
    - gstep; constructor; auto.
    - gstep; constructor; auto with paco.
    - guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros. gstep. rewrite H1. destruct u2 eqn:Equ2.
        constructor; auto with paco itree.
  Qed.

    
Lemma interp_st_bind {U} 
  (t : itree (STEvent S +' E) R)
  (k : R -> itree (STEvent S +' E) U)
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

Lemma interp_st_bind_eutt {U} 
  (t : itree (STEvent S +' E) R)
  (k : R -> itree (STEvent S +' E) U)
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

Lemma interp_st_bind_eutt' {U} 
  (t : itree (STEvent S +' E) R)
  (k : R -> itree (STEvent S +' E) U)
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


Lemma eutt_eq_bind_interp_st {U}
  (k2 : (mem * R) -> itree E (mem * U))
  (lmem : mem)
  (t1 : itree (STEvent S +' E) R)
  (t2 : itree E (mem * R))
  (k1: R -> itree (STEvent S +' E) U)
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
  Context {Map : Map (Idx S) R map}.
  Context {MOK : MapOk eq Map}.

  Lemma st_lookup_err_add_eq : forall (s : map) (k : Idx S) (v : R),
      lookup_err k (Maps.add k v s) = @ret (itree E) _ _ v.
  Proof using MOK.
    intros. unfold lookup_err.
    rewrite (@lookup_add_eq (Idx S) R map Map MOK).
    reflexivity.
  Qed.

  Lemma st_lookup_err_remove_eq : forall (k : Idx S) (s : map),
      lookup_err k (Maps.remove k s) = @throw Err E _ _ (Error "Failed to find key in map").
  Proof using MOK.
    intros. unfold lookup_err.
    rewrite (@lookup_remove_eq (Idx S) R map Map MOK k s).
    reflexivity.
  Qed.

End STLookupErr.



Require Stdlib.derive.Derive.
Section Examples.

  Context {S : Type}.
  Context {E : Type -> Type}.
  Context `{IdxGenE -< E}.
  Context `{exceptE Err -< E}.

  Lemma eutt_fmap {E' : Type -> Type} {R U : Type} {t1 t2 : itree E' R} {f : R -> U} :
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

(* TODO: move to separate ltac section. *)
Ltac refine_prod :=
  (refine (fun '(a,b) => _)).

Ltac refine_arg :=
  (refine (fun arg => _)).

Ltac refine_arg2 :=
  (refine (fun arg1 arg2 => _)).



Theorem bind_Ret_l : forall A B (f : A -> itree E B) (x : A), bind (Ret x) f ≈ f x.
  setoid_rewrite Ret_is_ret.
  setoid_rewrite Monad.bind_ret_l.
  reflexivity.
  Qed.
          

Theorem bind_Ret_r : forall A (x : itree E A), bind x (fun y => Ret y) ≈ x.
  intros A x. setoid_rewrite Monad.bind_ret_r. reflexivity. Qed.


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

Opaque Maps.add.
  
  Derive (tree_simplified : itree E nat) in
    ( runSt (fun S => @tree_simp S E)
        ≈
      tree_simplified
    ) as tree_simplification.
  Proof.
    etransitivity.
    { unfold runSt.
      eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltac:(refine_prod)).
      - unfold newSTRef.
        rewrite interp_st_trigger.
        cbn.
        reflexivity.
      - intros u lmem'.
        unfold readSTRef.
        rewrite interp_st_trigger.
        cbn.
        reflexivity. }
    etransitivity.
    { eapply eutt_fmap.
      change_to_monad.
      monad_simpl_inner.
      bind_split_refl_intros ltac:(eapply (eutt_eq_bind' _ ltac:(refine_arg))).
      rewrite IdxRefSameIdx.
      rewrite st_lookup_err_add_eq.
      monad_simpl_inner.
      reflexivity. }
    cbn.
    setoid_rewrite map_bind.
    setoid_rewrite map_ret.
    unfold snd.
    unfold tree_simplified.
    reflexivity.
  Defined.


  (* TODO: fill out the other examples in a likewise manner to above. *)
  Derive (readboth_simplified : itree E (nat*nat)) in
    ( runSt (fun S => @newAndReadBoth S E)
        ≈
      readboth_simplified
    ) as tree_simplification2.
  Proof.
    etransitivity.
    { unfold runSt.
      eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltac:(refine_arg)).
      - unfold newSTRef.
        rewrite interp_st_trigger.
        cbn.
        reflexivity.
      - intros u lmem'.
        unfold readSTRef.
        eapply (eutt_eq_bind_interp_st ltac:(refine_arg)).
        {
          unfold newSTRef.
          rewrite interp_st_trigger.
          cbn.
          change lmem' with (fst (lmem', u)). (* TODO: unfortunate change. *)
          reflexivity.
        }
        intros ? ?.
        eapply (eutt_eq_bind_interp_st ltac:(refine_arg)).
        {
          unfold newSTRef.
          rewrite interp_st_trigger.
          cbn. change u with (snd (lmem', u)).
          change lmem'0 with (fst (lmem'0, u0)).
          reflexivity.
        }
        intros ? ?. 
        eapply (eutt_eq_bind_interp_st ltac:(refine_arg)).
        {
          unfold newSTRef.
          rewrite interp_st_trigger.
          cbn. change u with (snd (lmem', u)).
          change lmem'0 with (fst (lmem'0, u0)).
          change u0 with (snd (lmem'0, u0)).
          change lmem'1 with (fst (lmem'1, u1)).
          reflexivity.
        }
        intros ? ?.
        rewrite interp_st_Ret.
        change lmem'2 with (fst (lmem'2, u2)).
        change u1 with (snd (lmem'1, u1)).
        change u2 with (snd (lmem'2, u2)).
        reflexivity. }
    etransitivity.
    { eapply eutt_fmap.
      change_to_monad.
      monad_simpl_inner.
      bind_split_refl_intros ltac:(eapply (eutt_eq_bind' _ ltac:(refine_arg))).
      monad_simpl_inner.
      bind_split_refl_intros ltac:(eapply (eutt_eq_bind' _ ltac:(refine_arg))).
      monad_simpl_inner. cbn.
      rewrite IdxRefSameIdx.
      Transparent Maps.add. unfold lookup_err at 1.
      assert (lookup u (add u0 6 (add u 5 [])) = Some 5).
      {
        cbn. give_up. (* TODO: needs uniqueness of elements from stream. *)
      }

      setoid_rewrite H1.
      monad_simpl_inner.
      setoid_rewrite IdxRefSameIdx.
      setoid_rewrite st_lookup_err_add_eq.
      monad_simpl_inner.
      reflexivity.
    }
    cbn.
    setoid_rewrite map_bind.
    setoid_rewrite map_bind.
    setoid_rewrite map_ret.
    unfold snd.
    unfold readboth_simplified.
    reflexivity.
    Abort.

End Examples.

(* CPP Bindings *)

  
From Crane Require Extraction.


(* TODO: how to obtain integer reference statically? *)
Crane Extract Inlined Constant STRef => "%t1".
Crane Extract Inlined Constant newSTRef => "%result = %a0".
Crane Extract Inlined Constant readSTRef => "%a0". 
Crane Extract Inlined Constant writeSTRef => "%a0 = %a1".
Crane Extract Skip IdxRefSameIdx.
Crane Extract Skip IdxRefSameRef.
Crane Extract Skip E0.
Crane Extract Skip newIdx.


