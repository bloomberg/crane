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
  Classes.EquivDec
.

From Crane Require Import Monads.ITree Utils.HMap Utils.HAList Extraction.
From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Data.Option
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


(* TODO: canonicalize on style, according to https://github.com/bloomberg/game-trees/blob/main/theories/Eval.v *)
(* TODO: canonicalize map -> mem. *)
(* TODO: canonicalize STRef, no other capitalization! *)
(* TODO: canonicalize Idx -> Ix. *)

(* Used for runtime checks, though an ideal impl won't need these. *)

Variant Err : Type :=
| Error (x : string) : Err.

Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).


(* Modeled after Ix type in https://hackage.haskell.org/package/base-4.18.1.0/docs/Data-Ix.html#t:Ix *)
Class Ix (T : Type)
  (ltu : T -> T -> Prop) (* lte *)
  {CD : CmpDec eq ltu}
  : Type :=
  {
    (* The list of values defined in the range *)
    range : prod T T -> list T; 

    (* diverge from haskell in using error type *)
    index : prod T T -> T -> option nat; 

    (* decidable equality over the range *)
    inRange : prod T T -> T -> Prop; (* NOTE: bool here? *)

    (* the size of the elements in the range *)
    rangeSize : prod T T -> nat;

    (* a constructor for an index plus one. *)
    suc : T -> T;

    (* function that gives max between indices. *)
    max : T -> T -> T;

    (* zero value, least value to compare with. *)
    zero : T; 
  }.

#[export] Instance cmp_dec_nat : CmpDec eq Nat.le := {| cmp_dec := Nat.compare |}.
#[export] Instance cmp_dec_correct : CmpDec_Correct cmp_dec_nat.
  econstructor. intros.
  destruct (cmp_dec x y) eqn:Heq
  + inversion Heq.
    apply Nat.compare_eq_iff; assumption.
  + inversion Heq. 
    apply Nat.compare_le_iff.
    unfold not.
    intros HG.
    destruct (x ?= y)%nat. 
    * inversion H0.
    * inversion HG.
    * inversion H0.
  + inversion Heq. 
    specialize (Nat.compare_gt_iff x y) as Hgt.
    destruct Hgt.
    * specialize (H H0).
      apply (Nat.lt_le_incl). assumption.
  Qed.


#[export] Instance nat_ix : Ix nat Nat.le :=
  {|
    range := fun p : nat * nat => seq (fst p) ((1 + snd p) - fst p);
    index := fun (p : nat * nat) (i : nat) =>
               if andb (Nat.leb (fst p) i) (Nat.leb i (snd p))
               then Some (i - fst p)
               else None;
    inRange := 
      fun (p : nat * nat) (i : nat) => Nat.le (fst p) i /\ Nat.le i (snd p);
    rangeSize := fun p : nat * nat => (1 + snd p) - fst p;
    
    (* needed to generate new indices *)
    suc := Datatypes.S; 
    max := Nat.max; 
    zero := 0;
  |}.


(* taken from https://hackage.haskell.org/package/base-4.18.1.0/docs/Data-Ix.html#t:Ix*)
Definition option_map_list
  {A B : Type}
  (l : list (option A))
  (f : A -> B -> B)
  (def : B)
  : option B :=
fold (fun (next : option A) (acc : option B) => match next with
                                                | Some a => option_map (f a) acc
                                                | None => None
                                                end)
  (Some def) l.

Class Ix_Correct (T : Type)
  (ltu : T -> T -> Prop) 
  {CD : @CmpDec T eq ltu}
  {CDC : @CmpDec_Correct T eq ltu CD}
  {HI : @Ix T ltu CD}
  {RD : @RelDec.RelDec T eq}
  : Type := 
  { 
    inRange_implies_elem : forall (l u i : T),
      inRange (l,u) i <-> (In i (range (l,u))); 

    (* range (l,u) !! index (l,u) i == i, when inRange (l,u) i *)
    inRange_elems_are_indexable: forall (l u v : T) (i : nat),
      index (l,u) v = Some i ->
      inRange (l,u) v -> (* TODO: superflous precond?*)
      List.nth_error (range (l,u)) i = Some v;


    (* map (index (l,u)) (range (l,u))) == [0..rangeSize (l,u)-1] *)
    map_over_indices_makes_incr_seq: forall (p : T * T),
      List.map (index p) (range p)
      =
      List.map Some (seq 0 (rangeSize p));


    (* rangeSize (l,u) == length (range (l,u)) *)
    rangeSize_is_length_of_range : forall (p : T * T),
      rangeSize p = length (range p);
      
  }.

From Stdlib Require Import Lia.

Lemma add_sub_le n m : n <= m -> n + (m - n) = m.
Proof. lia. Qed.

(* TODO: move into nat_ix_correct. unhelpful out here. *)
Lemma in_seq_iff l u i :
  In i (seq l (1 + u - l)) <-> l <= i /\ i <= u.
Proof.
  destruct (Nat.le_gt_cases l (1 + u)) as [Hle|Hgt].
  - rewrite in_seq.
    enough (l + (1 + u - l) = 1 + u) as -> by lia.
    apply add_sub_le. exact Hle.
  - replace (1 + u - l) with 0 by lia. simpl.
    split; [tauto | lia].
Qed.

#[export,refine] Instance nat_ix_correct : Ix_Correct nat Nat.le :=
  {|
    inRange_implies_elem := _;
    inRange_elems_are_indexable := _;
    map_over_indices_makes_incr_seq := _;
    rangeSize_is_length_of_range := _
  |}.
- intros l u i. exact (iff_sym (in_seq_iff l u i)).
- intros l u v i Hidx [Hl Hu].
  unfold index, range, nat_ix in *. simpl fst in *. simpl snd in *.
  destruct (Nat.leb l v) eqn:Elv; [|discriminate].
  destruct (Nat.leb v u) eqn:Evu; simpl andb in Hidx; [|discriminate].
  inversion Hidx; subst; clear Hidx.
  apply Nat.leb_le in Elv. apply Nat.leb_le in Evu.
  rewrite nth_error_seq.
  replace ((v - l <? 1 + u - l)%nat) with true
    by (symmetry; apply Nat.ltb_lt; lia).
  f_equal. apply add_sub_le. lia.
- intros [l u]. unfold index, range, rangeSize, nat_ix. simpl fst. simpl snd.
  set (n := 1 + u - l).
  erewrite List.map_ext_in.
  2: { intros a Ha. apply in_seq in Ha.
       destruct (Nat.leb l a) eqn:E1; [| apply Nat.leb_nle in E1; lia].
       destruct (Nat.leb a u) eqn:E2; [| apply Nat.leb_nle in E2; lia].
       simpl. reflexivity. }
  cut (forall k, List.map (fun i => Some (i - l)) (seq (l + k) n)
                 = List.map Some (seq k n)).
  { intro H. specialize (H 0). rewrite Nat.add_0_r in H. exact H. }
  induction n as [|n' IHn']; intro k.
  + reflexivity.
  + simpl. f_equal.
    * f_equal. lia.
    * replace (S (l + k)) with (l + S k) by lia. apply IHn'.
- intros [l u]. unfold rangeSize, range, nat_ix. simpl.
  rewrite length_seq. reflexivity.
Qed.

Class STRefClass (T : Type) : Type :=
  {
    STRef : forall S A : Type, Type; 
    mkSTRef : forall S A : Type, T -> STRef S A;
    STRefToIx : forall S A : Type, STRef S A -> T;
  }.


Section STRefNatDefs.

  Variable (T : Type).
  

  Variant STRefNat : Type -> Type -> Type :=
  | MkSTRef (S A : Type) (idx : nat) : STRefNat S A.

  
  Definition STRefToIdxNat (S A : Type) (ref : STRefNat S A) : nat :=
   match ref with
   | MkSTRef _ _ idx => idx
   end. 

End STRefNatDefs.

#[export] Instance nat_ix_stref : STRefClass nat :=
  {| STRef := STRefNat;
    mkSTRef := MkSTRef ;
    STRefToIx := STRefToIdxNat |}.




Section STEventDefine.  
  Variable (T : Type).
  Variable (ltu : T -> T -> Prop).
  Context `{STRefClass T}.

  Variant STEvent (S : Type) (V : T -> Type) : Type -> Type :=
    | NewSTRef (idx : T) (v : V idx) : STEvent S V (STRef S (V idx))
    | ReadSTRef (idx : T) : STRef S (V idx) -> STEvent S V (V idx)
    | WriteSTRef (idx : T) : STRef S (V idx) -> (V idx) -> STEvent S V unit
  .

End STEventDefine.

(* Arrays! *)

Section STArrayDef.

  (* TODO: Array event definition goes here. *)
  (* Events in Haskell *)
(* newArray :: Ix i => (i, i) -> e -> ST s (STArray s i e)
 * newListArray :: (MArray a e m, Ix i) => (i, i) -> [e] -> m (a i e) 
 * readArray :: (MArray a e m, Ix i) => a i e -> i -> m e 
 * writeArray :: (MArray a e m, Ix i) => a i e -> i -> e -> m () 
 * getElems :: (MArray a e m, Ix i) => a i e -> m [e]  *)

End STArrayDef.
  
Section Translation.

  Context {E : Type -> Type}.
  Context {T S : Type}.
  Variable (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{EqDec T eq}. (* TODO: add as hint based on Ix_Correct *)
  Context `{STRefClass T}.
  Context {V : T -> Type}.
  Context `{STEvent T S V -< E}. 
  Context `{exceptE Err -< E}.
  

  Definition newSTRef (idx : T) (v : (V idx)) : itree E (STRef S (V idx)) :=
    trigger (NewSTRef T S V idx v).

  Definition readSTRef {idx : T} (ref : STRef S (V idx)) : itree E (V idx) :=
    trigger (ReadSTRef T S V idx ref).

  Definition writeSTRef {idx : T} (ref : STRef S (V idx)) (a : (V idx)) : itree E unit :=
    trigger (WriteSTRef T S V idx ref a).


  
  Definition pkey (J K : Type) := (J * K)%type.
  Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
  Definition idx_key := pkey T. 
  Definition idx_key_type {K} (V : K -> Type) (ik : idx_key K) := V (snd ik).


  Context {M : Type}.
  Context `{HMap (idx_key T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (idx_key_type V))}.


  Definition handle_STEvent `{EqDec T eq} 
    : forall (A : Type), STEvent T S V A -> stateT M (itree E) A :=
    fun _ e mem =>
    match e with
    | NewSTRef _ _ _ idx v =>
        let n := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem)
        in Ret (add (n, idx) v mem, mkSTRef S (V idx) idx)
    | ReadSTRef _ _ _ idx s =>
        match lookup (STRefToIx S (V idx) s, idx) mem with
        | Some v => Ret (mem, v)
        | None => failwith "Lookup failed!"
        end
    | WriteSTRef _ _ _ idx s v => Ret (add (STRefToIx S (V idx) s, idx) v mem, tt)
    end.

(* Interpretation in Rocq *)

  (* TODO: better name perhaps *)
  Definition handle_STEvent_leave_rest
    (A : Type) (e : (STEvent T S V +' E) A)
    : stateT M (itree (E)) A :=
    match e with
    | inl1 e0 => handle_STEvent A e0
    | inr1 e0 => fun st : M => r <- trigger e0;; Ret (st, r)
    end.
  
  #[export] Instance hmap_from_idx :
    HMap T V (halist T V) := @HMap_halist (T) V eq_equivalence H0.

  Global Instance map_idx_correct :
    HMapOk hmap_from_idx := HMapOk_halist T V.

  Definition interp_st
    : itree (STEvent T S V +' E) ~> stateT M (itree (E)) :=
    interp_state handle_STEvent_leave_rest.

  
End Translation.

Definition runSt {A : Type}
  {T S : Type} {ltu : T -> T -> Prop}
  `{Ix T ltu}
  `{Ix_Correct T}
  `{EqDec T eq}
  `{STRefClass T}
  {E : Type -> Type}
  {V : T -> Type} `{exceptE Err -< E}
  (f : forall (S : Type), itree ((STEvent T S V) +' E) A)
  : itree E A :=
  fmap snd (interp_st ltu _ (f unit) HMap.empty).

(* CPP Bindings *)

Crane Extraction Implicit newSTRef[1].
Crane Extract Skip Ix_Correct.
Crane Extract Skip CmpDec_Correct.
Crane Extract Skip STEvent.
Crane Extract Skip CmpDec.
Crane Extract Skip Ix.
Crane Extract Skip suc.
Crane Extract Skip max.
Crane Extract Skip zero.
Crane Extract Skip mkSTRef.
Crane Extract Skip STRefToIx.
(* NOTE: skipping STRefClass seems to drop typing
  information extraction need to infer value types inside references. *)
(* Crane Extract Skip STRefClass. *)
Crane Extract Inlined Constant STRef => "%t3".
Crane Extract Inlined Constant newSTRef => "%result = %a1".
Crane Extract Inlined Constant readSTRef => "%a1".
Crane Extract Inlined Constant writeSTRef => "%a1 = %a2".


