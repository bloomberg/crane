
From Crane Require Import Monads.STMonad.   

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
  Basics
.

From Crane Require Import Monads.ITree.
From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Map.FMapAList
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Structures.Functor
  Structures.Maps
  Structures.Traversable
  Structures.Reducible
.


From ITree Require Import
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



  

Section NatExampleTrees.

  Context {E : Type -> Type}.
  Context {T : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST: STRefClass T}.

  Let V : T -> Type := fun _ => nat. (* Nats only for this example. *)
  Let S := unit.
  Let E0 := (STEvent T S V) +' exceptE Err.


  Definition newAndReadBoth : itree E0 (nat * nat) :=
      r1 <- newSTRef zero 5 ;;
      r2 <- newSTRef (suc zero) 6 ;; (* TODO: autogenerate successive indices? *)
      x1 <- readSTRef r1 ;;
      x2 <- readSTRef r2 ;;
      Ret (x1, x2).

  Definition tree_simp : itree E0 nat :=
    v <- newSTRef zero 5;;
    readSTRef v.

  (* NOTE: this failing definition is intentional.
    The intent is to test that we don't allow reference indices to escape. *)
  Fail Definition tree_escape_example : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v (match v with mkSTRef _ _ idx => idx end);;
    readSTRef v.

  Definition tree_simp_another : itree E0 nat :=
    v <- newSTRef zero 5;;
    writeSTRef v 6;;
    val <- readSTRef v;;
    Ret val.


   Definition swap' (v w : STRef S nat) : itree E0 unit :=
    a <- @readSTRef E0 T S  _ V  _ (STRefToIx _ _ v) v;;
    b <- @readSTRef E0 T S _ V _ (STRefToIx _ _ w) w;;
    writeSTRef v b;;
    writeSTRef w a.

  (* "swap" function from "Lazy Functional State Threads", by John Launchbury and Simon L Peyton Jones. *)
  (* TODO: would be good for indices here to be inferrable. *)
  Fail Definition swap (v w : STRef S nat) : itree E0 unit :=
    a <- readSTRef v;;
    b <- readSTRef w;;
    writeSTRef v b;;
    writeSTRef w a.


  Definition array_simp_fixed_init : itree E0 nat :=
    arr <- newArray zero zero (suc (suc (suc (suc (suc zero))))) 5;;
    elem <- @readArray E0 T _ _ _ _ _ arr (suc (zero));;
    Ret elem. 
  
  Definition array_simp_list : itree E0 nat :=
    arr <- newListArray zero zero (suc (suc (suc zero))) [4;2;3;1];;
    elem <- @readArray E0 T _ _ _ _ zero arr (suc zero);;
    Ret elem. 


  Section QSort. 

  Definition swap_arr (arr : STArray T S nat) (left : T) (right : T) : itree E0 unit :=
    leftVal <- readArray arr left;;
    rightVal <- readArray arr right;;
    @writeArray E0 T S _ _ _ zero arr left rightVal;;
    @writeArray E0 T S _ _ _ (suc zero) arr right leftVal.

  Definition forEachWith {A B} (xs : list A) (v : B) (f : B -> A -> itree E0 B)
    : itree E0 B := foldM (flip f) (Ret v) xs.


  Definition partition (arr : STArray T S nat) (arr_idx : T) (left : T) (right : T) (pivotIndex : T) : itree E0 T :=
    pivotValue <- @readArray _ _ _ _ _ _ arr_idx arr pivotIndex;;
    swap_arr arr pivotIndex right;;
    storeIndex <- forEachWith (range left (sub right (suc zero))) left (fun i storeIndex =>
        val <- @readArray _ _ _ _ _ _ arr_idx arr i;;
        if (Nat.leb val pivotValue)
            then swap_arr arr i storeIndex;;
                 Ret (suc storeIndex)
            else Ret storeIndex );;
    swap_arr arr storeIndex right;;
    Ret storeIndex.


  (* TODO: define with equations. *)
  Fail Fixpoint qsort (arr : STArray T S nat) (arr_idx : T) (left : T) (right : T) : itree E0 (STArray T S nat) :=
    let leftn := toNat left in
    let rightn := toNat right in 
    let pivotIndexn := leftn + ((rightn - leftn) / 2) in
    newPivot <- partition arr arr_idx left right (fromNat pivotIndexn);;
    qsort arr arr_idx left (fromNat ((toNat newPivot) + 1));;
    qsort arr arr_idx (fromNat ((toNat newPivot) + 1)) right.

    
  End QSort.

  
End NatExampleTrees.



Module STMonadTests. 
  (* Re-exporting instances so they're available to call in the exported file. *)
  (* Just referring to them does not seem to work to extract them here, unfolding does *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.
End STMonadTests.


Require Import Crane.Mapping.NatIntStd.
Crane Extraction "stmonad" STMonadTests newAndReadBoth tree_simp tree_simp_another array_simp_fixed_init.

