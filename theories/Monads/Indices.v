(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)


(* A library for generic indexes accessed through a typeclass interface.
   The purpose of the interface is to abstract away the manipulations of indices
   so that writers of programs in Rocq cannot access them directly. One use-case for this is
   for a set of references. One might conceal the address type in order to make it impossible to manipulate
   addresses and do pointer arithmetic. 
 *)

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

From Crane Require Import
  Extraction
  Monads.ITree
  Monads.Error
  Utils.HAList
  Utils.HMap
.

Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.



(* Modeled after Ix type in https://hackage.haskell.org/package/base-4.18.1.0/docs/Data-Ix.html#t:Ix *)
(* TODO: The `sub,zero,fromNat,toNat` functions are there in order
  to be able to talk about ranges of indices, which is required to write
  an in-place quicksort that recurses down into sections of an array.
  This came about because STArrays are collections of STRefs, morally.
  To make that safer, one could adjust array STRefs to form a "region"
  for which one could manipulate "raw" nats instead.
 *)
Class Ix (T : Type)
  (ltu : T -> T -> Prop) (* lte *)
  : Type :=
  {
    (* The list of values defined in the range, defined inclusively *)
    range : T -> T -> list T; 

    (* diverge from haskell in using error type *)
    index : T -> T -> T -> option nat; 

    (* decidable equality over the range *)
    inRange : T -> T -> T -> Prop; (* NOTE: bool here? *)

    (* the size of the elements in the range *)
    rangeSize : T -> T -> nat;

    (* conversion to nats *)
    toNat : T -> nat;

    (* conversion from nats *)
    fromNat : nat -> T;

    (* a constructor for an index plus one. *)
    suc : T -> T;

    (* subtraction of two indices *)
    sub: T -> T -> T;

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
    range := fun fp sp : nat => seq fp ((1 + sp) - fp);
    index := fun (fp sp : nat) (i : nat) =>
               if andb (Nat.leb fp i) (Nat.leb i (sp))
               then Some (i - fp)
               else None;
    inRange := 
      fun (fp sp : nat) (i : nat) => Nat.le fp i /\ Nat.le i sp;
    rangeSize := fun fp sp : nat => (1 + sp) - fp;
    
    (* needed to generate new indices *)
    suc := Datatypes.S; 
    sub := Nat.sub;
    max := Nat.max; 
    zero := 0;
    toNat := fun n : nat => n;
    fromNat := fun n : nat => n;
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
  (HI : @Ix T ltu)
  {CD : @CmpDec T eq ltu}
  {CDC : @CmpDec_Correct T eq ltu CD}
  {EQD : EqDec T eq} 
  {RD : @RelDec.RelDec T eq}
  : Type := 
  { 
    inRange_implies_elem : forall (l u i : T),
      inRange l u i <-> (In i (range l u)); 

    (* range (l,u) !! index (l,u) i == i, when inRange (l,u) i *)
    inRange_elems_are_indexable: forall (l u v : T) (i : nat),
      index l u v = Some i ->
      inRange l u v -> (* TODO: superflous precond?*)
      List.nth_error (range l u) i = Some v;


    (* map (index (l,u)) (range (l,u))) == [0..rangeSize (l,u)-1] *)
    map_over_indices_makes_incr_seq: forall (fp sp : T),
      List.map (index fp sp) (range fp sp)
      =
      List.map Some (seq 0 (rangeSize fp sp));


    (* rangeSize (l,u) == length (range (l,u)) *)
    rangeSize_is_length_of_range : forall (fp sp : T),
      rangeSize fp sp = length (range fp sp);
      
  }.


Lemma add_sub_le n m : n <= m -> n + (m - n) = m.
Proof. lia. Qed.


#[export,refine] Instance nat_ix_correct : Ix_Correct nat Nat.le nat_ix :=
  {|
    inRange_implies_elem := _;
    inRange_elems_are_indexable := _;
    map_over_indices_makes_incr_seq := _;
    rangeSize_is_length_of_range := _
  |}.
- intros l u i.
  assert (forall l u i, In i (seq l (1 + u - l)) <-> l <= i /\ i <= u).
  {
    intros l' u' i'. 
    destruct (Nat.le_gt_cases l' (1 + u')) as [Hle|Hgt].
    - rewrite in_seq.
      enough (l' + (1 + u' - l') = 1 + u') as -> by lia.
      apply add_sub_le. exact Hle.
    - replace (1 + u' - l') with 0 by lia. simpl.
      split; [tauto | lia].
  }
  exact (iff_sym (H _ _ _)).
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
- intros l u. unfold index, range, rangeSize, nat_ix. simpl fst. simpl snd.
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
- intros l u. unfold rangeSize, range, nat_ix. simpl.
  rewrite length_seq. reflexivity.
Qed.

Crane Extract Skip Ix_Correct.
Crane Extract Skip CmpDec_Correct.
