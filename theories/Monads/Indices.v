(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Generic indices behind a typeclass interface ([Ix], specified by
    [Ix_Correct], with [nat] instances), so that programs cannot manipulate
    indices directly: a set of references can conceal its address type and
    rule out pointer arithmetic. *)

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



(* TODO: The `sub,zero,fromNat,toNat` functions are there in order
  to be able to talk about ranges of indices, which is required to write
  an in-place quicksort that recurses down into sections of an array.
  This came about because ST arrays are collections of ST references, morally.
  To make that safer, one could adjust array references to form a "region"
  for which one could manipulate "raw" nats instead.
 *)
(** Index types, after Haskell's [Data.Ix]
    (https://hackage.haskell.org/package/base-4.18.1.0/docs/Data-Ix.html#t:Ix):
    every range is given by inclusive bounds [l] and [u]; [ltu] orders them. *)
Class Ix (T : Type)
  (ltu : T -> T -> Prop) (* lte *)
  : Type :=
  {
    (** The values from [l] to [u], both included. *)
    range : T -> T -> list T; 

    (** The position of a value in [range l u]; [None] out of range, where
        Haskell raises an error. *)
    index : T -> T -> T -> option nat; 

    (** Whether a value lies between the bounds. *)
    inRange : T -> T -> T -> Prop; (* NOTE: bool here? *)

    (** The number of values in the range. *)
    rangeSize : T -> T -> nat;

    (** The index as a [nat]. *)
    toNat : T -> nat;

    (** The index of a [nat]. *)
    fromNat : nat -> T;

    (** The next index. *)
    suc : T -> T;

    (** Index subtraction. *)
    sub: T -> T -> T;

    (** The larger of two indices. *)
    max : T -> T -> T;

    (** The least index. *)
    zero : T; 
  }.

(** [nat] compared by [Nat.compare], deciding [eq] and [Nat.le]. *)
#[export] Instance cmp_dec_nat : CmpDec eq Nat.le := {| cmp_dec := Nat.compare |}.
(** [Nat.compare] agrees with [eq] and [Nat.le]. *)
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


(** [nat] indices: [range l u] is [seq l (1 + u - l)]. *)
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


(** Fold [f] over the values in [l] from [def]; [None] if any element is [None]. *)
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

(** The [Data.Ix] laws tying [range], [index],
    [inRange] and [rangeSize] together. *)
Class Ix_Correct (T : Type)
  (ltu : T -> T -> Prop) 
  (HI : @Ix T ltu)
  {CD : @CmpDec T eq ltu}
  {CDC : @CmpDec_Correct T eq ltu CD}
  {EQD : EqDec T eq} 
  {RD : @RelDec.RelDec T eq}
  : Type := 
  { 
    (** A value is in range exactly when [range] lists it. *)
    inRange_implies_elem : forall (l u i : T),
      inRange l u i <-> (In i (range l u)); 

    (** [index] finds an in-range value at its position in [range]. *)
    inRange_elems_are_indexable: forall (l u v : T) (i : nat),
      index l u v = Some i ->
      inRange l u v -> (* TODO: superflous precond?*)
      List.nth_error (range l u) i = Some v;


    (** [index] numbers [range fp sp] from [0] to [rangeSize fp sp - 1]. *)
    map_over_indices_makes_incr_seq: forall (fp sp : T),
      List.map (index fp sp) (range fp sp)
      =
      List.map Some (seq 0 (rangeSize fp sp));


    (** [rangeSize] is the length of [range]. *)
    rangeSize_is_length_of_range : forall (fp sp : T),
      rangeSize fp sp = length (range fp sp);
      
  }.


(** Arithmetic used by [nat_ix_correct]. *)
Lemma add_sub_le n m : n <= m -> n + (m - n) = m.
Proof. lia. Qed.


(** The [nat] instance satisfies the [Data.Ix] laws. *)
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

(** The law classes are proof-only. *)
Crane Extract Skip Ix_Correct.
Crane Extract Skip CmpDec_Correct.
