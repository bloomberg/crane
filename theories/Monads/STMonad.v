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
Import MonadNotation.
Import ListNotations.
From Coq Require Import
     Morphisms
     Setoid
     Relation_Definitions
     RelationClasses
.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(* Variant st : Type -> Type :=
 *   | MkST (T : Type) : st T.  *)

Axiom STRef : forall (S A : Type), Type. 
Axiom Idx : forall (S : Type), Type.

Axiom IdxDecEq : forall (S : Type) (i1 i2 : Idx S),  
    {i1 = i2} + {i1 <> i2}.

Axiom STRefToIdx : forall (S A : Type) (ref : STRef S A),
    Idx S.


(* Variant STRef : Type -> Type -> Type :=
 *   | MkStRef (S : Type) (idx : nat) : STRef S nat. *)
  

(* TODO: Expand to cover more types than nat *)
Variant STEvent (S : Type) : Type -> Type :=
  | NewSTRef (v : nat) : STEvent S (STRef S nat)
  | ReadSTRef : STRef S nat -> STEvent S nat
  | WriteSTRef : STRef S nat -> nat -> STEvent S unit
.


(* TODO: make this typecheck *)



(* TODO: Unfortunate duplication from tests/monadic/itree_effects/ITreeEffects.v*)
Inductive randomE : Type -> Type :=
| RandomNat : nat -> randomE nat.

(* TODO: Drop 100000 bound here?*)
Definition randomNat {E : Type -> Type} `{randomE -< E} : itree E nat :=
  trigger (RandomNat 100). 

Variant Err : Type :=
| Error (x : string) : Err.

Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).

Section Translation.

  Context {E : Type -> Type}.
  Context {S : Type}.
  Context `{STEvent S -< E}. 
  
  (* TODO: nit; switch to embed instead of trigger? *)
  Definition newSTRef (v : nat) : itree E (STRef S nat) :=
    trigger (NewSTRef S v). 

  Definition readSTRef (ref : STRef S nat) : itree E nat :=
    trigger (ReadSTRef S ref). 

  Definition writeSTRef (ref : STRef S nat) (a : nat) : itree E unit :=
    trigger (WriteSTRef S ref a).

End Translation.

(* Example Programs*)
Section ExampleTrees.

  Context {S : Type}.
  Context {E : Type -> Type}.
  Context `{randomE -< E}.
  Context `{exceptE Err -< E}.


  Definition E0 := STEvent S +' E.

  Definition newAndReadBoth : itree (STEvent S) (nat * nat) :=
    r1 <- newSTRef 5 ;;
    r2 <- newSTRef 6 ;;
    x1 <- readSTRef r1 ;;
    x2 <- readSTRef r2 ;;
    Ret (x1, x2).

  (* NOTE: this should not work! *)
  Fail Definition tree_escape_example : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v (match v with MkStRef _ idx => idx end);;
    readSTRef v.

  Definition tree2 : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v 6;;
    val <- readSTRef v;;
    ret val.

End ExampleTrees.




Section MemoryRep.

Inductive node : Type := (* TODO: More types! *)
  | NInt (x : nat) : node
.


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

  (* Context {E : Type -> Type}.
   * Context {S : Type}. *)

  Definition stStateT (s : Type) (m : Type -> Type) (a : Type) : Type :=
    s -> m (prod s a).

  Definition stState (s a : Type) := s -> prod s a.

  Definition run_stStateT {s m a} (x : stStateT s m a) : s -> m (s * a)%type := x.

  Definition lookup_err
    {E : Type -> Type} `{exceptE Err -< E}
    {map} `{Map nat nat map}
    (k : nat) (mem : map) : itree E nat :=
    match lookup k mem with
      | None => throw (Error "Failed to find key in map")
      | Some v => ret v
    end.


  (* TODO: Cleanup! *)
  Definition handle_STEvent
    {E : Type -> Type} {S : Type}
    {map} `{Map nat nat map}
    `{randomE -< E} `{exceptE Err -< E}
    : forall (T : Type),  STEvent S T -> stateT map (itree E) T :=
    fun T e mem =>
    match e in (STEvent _ T0) return (itree E (map * T0)) with
    | NewSTRef _ v =>
        (fun v0 : nat => idx <- randomNat;; ret (add idx v0 mem, MkStRef S idx)) v
    | ReadSTRef _ s =>
        (fun s0 : STRef S nat =>
        let S0 := nat in
        match s0 in (STRef T0 T1) return (Map T1 T1 map -> itree E (map * T1)) with
        | MkStRef S1 idx =>
            (fun (_ : Type) (idx0 : nat) (H2 : Map nat nat map) =>
              v <- lookup_err idx0 mem;; ret (mem, v)) S1 idx
        end H) s
    | WriteSTRef _ s n =>
        (fun (s0 : STRef S nat) (n0 : nat) =>
        let S0 := nat in
        match
          s0 in (STRef T0 T1) return (Map T1 T1 map -> T1 -> itree E (map * unit))
        with
        | MkStRef S1 idx =>
            (fun (_ : Type) (idx0 : nat) (H2 : Map nat nat map) (n1 : nat) =>
              ret (add idx0 n1 mem, tt)) S1 idx
        end H n0) s n
    end.

  
  (* TODO: better name perhaps *)
  Definition handle_STEvent_leave_rest
    {mem} `{Map nat nat mem}
    {E : Type -> Type} {S : Type}
    `{exceptE Err -< E} `{randomE -< E}
    (T : Type) (e : (STEvent S +' E) T)
    : stateT mem (itree (E)) T :=
    match e with
    | inl1 e0 => handle_STEvent T e0
    | inr1 e0 => fun st : mem => r <- trigger e0;; ret (st, r)
    end.


  Definition interp_st
    {E : Type -> Type} {S : Type}
    `{exceptE Err -< E} `{randomE -< E}
    {mem} `{Map nat nat mem}
    : itree (STEvent S +' E) ~> stateT mem (itree (E)) :=
    interp_state handle_STEvent_leave_rest.

  
  Definition runSt {A : Type} {E : Type -> Type}
    {map} `{Map nat nat map} `{exceptE Err -< E} `{randomE -< E}
    : (forall (S : Type), itree ((STEvent S) +' E) A) -> itree E A :=
  fun f =>
  let tree := f unit in
  fmap snd (interp_st _ tree Maps.empty).

  
  

End InterpST.



Section InterpSTTheorems.

  (* TODO: refactor to above. *)
  (* Context {E : Type -> Type}.
   * Context `{exceptE Err -< E}.
   * Context `{randomE -< E}. *)

  Definition mem := alist nat nat.


  Definition _interp_st {R E S}
    `{exceptE Err -< E} `{randomE -< E}
    (ot : itree' (STEvent S +' E) R)
    (l : mem)
    : itree (E) (mem * R) :=
    match ot with
    | RetF r => ret (l, r)
    | TauF t => Tau (interp_st _ t l)
    | @VisF _ _ _ X e k =>
        x <- handle_STEvent_leave_rest X e l;;
        Tau (interp_st _ (k (snd x)) (fst x))
    end.


  Lemma unfold_interp_st {R E} {S : Type}
    `{exceptE Err -< E} `{randomE -< E}
    (t : itree (STEvent S +' E) R)
    (l : mem) :
    eq_itree eq
    (interp_st _ t l)
    (_interp_st (observe t) l).
  Proof.
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

  Lemma interp_st_ret: forall {R E S} `{exceptE Err -< E} `{randomE -< E} (val: R) (l : mem),
      @interp_st E S _ _ _ _ _ (ret val) l ≅ ret (l, val).
    Proof.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret: forall {R E S} `{exceptE Err -< E} `{randomE -< E} (val: R) (l : mem),
      @interp_st E S _ _ _ _ _ (Ret val) l ≅ Ret (l, val).
    Proof.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_Ret_eutt: forall {R E S} `{exceptE Err -< E} `{randomE -< E} (val: R) (l : mem),
      @interp_st E S _ _ _ _ _ (Ret val) l ≈ Ret (l, val).
    Proof.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

  Lemma interp_st_vis
    {T U E S} `{exceptE Err -< E} `{randomE -< E}
    (e : (STEvent S +' E) T)
    (k : T -> itree (STEvent S +' E) U)
    (l : mem)
    : interp_st _ (Vis e k) l
    ≅ x <- handle_STEvent_leave_rest _ e l;;
      Tau (interp_st _ (k (snd x)) (fst x)).
    Proof.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.

    
  Lemma interp_st_tau
      {R E S} `{exceptE Err -< E} `{randomE -< E}
      (t : itree (STEvent S +' E) R)
      (l : mem)
      : interp_st _ (Tau t) l ≅ Tau (interp_st _ t l).
    Proof.
      intros. rewrite unfold_interp_st. reflexivity.
    Qed.


  Lemma Ret_is_ret {E R} (x : R) : ((Ret x) : itree E R)  = ret x.
    Proof. reflexivity. Qed.
    
  Lemma interp_st_trigger
    {T E S} `{exceptE Err -< E} `{randomE -< E}
    (e : (STEvent S +' E) T)
    (l : mem) :
    interp_st _ (ITree.trigger e) l ≈ handle_STEvent_leave_rest _ e l.
    Proof.
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


Global Instance eq_itree_interp_st {R E S} `{exceptE Err -< E} `{randomE -< E}: 
Proper (@eq_itree (STEvent S +' E) R R eq ==> eq ==> eq_itree_eqv_global)
        (interp_st R).
Proof.
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

    
  Lemma interp_st_bind {R U E S} `{exceptE Err -< E} `{randomE -< E}
    (t : itree (STEvent S +' E) R)
    (k : R -> itree (STEvent S +' E) U)
    (mem : mem)
    : interp_st U (bind t k) mem
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


End InterpSTTheorems.

Require Stdlib.derive.Derive.

Section Example1.
  
  Definition E1 :=
  Derive tree1_simplified SuchThat
    ( runSt (fun S => @tree1 S E0)
        ≈
      tree1_simplified 
    ) As tree_simplification_works.


End Example1.
  
Derive (out_tree : itree E) in (
    
  )  
Example ex1_run {E : Type -> Type} `{exceptE Err -< E} `{randomE -< E} :
  runSt (fun S => @tree1 S E) = runSt (fun S => tree1).
unfold runSt at 1.
unfold tree1. 
Fail setoid_rewrite interp_st_bind. (* TODO: fix this! *)
  

  

(* CPP Bindings *)
