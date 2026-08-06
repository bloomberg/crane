(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* An object model using STRefs for mutable state *)

From Crane Require Import
  Monads.ITree
  Monads.Error
  Monads.Indices
  Monads.STMonad
  Utils.HMap
  Utils.HAList
  Extraction.


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
  Classes.EquivDec
  Basics
  ZArith
.

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
            



Section PointDef.


  Context (S : Type).
  Let T := nat.
  Let ltu := Nat.le.
  Let V : T -> Type := fun _ => Z.
  Let E0 := (STEvent T S V) +' exceptE Err.
  

  Record Point := mkPoint {
      getX : itree E0 Z;
      moveD : Z -> itree E0 unit;
      offsetX : itree E0 Z;
    }.


  
  (* NOTE: might wanna enforce unique indices with a global effect
           draw indices from a index generator. *)
  (* Modeling off of examples in OOHaskell,
   starting from https://github.com/nkaretnikov/OOHaskell/blob/master/samples/SimpleST.hs#L69 *)
  Definition class_pointST {idx : T} (init : Z) : itree E0 Point :=
    ref <- newSTRef 0 init ;;
    let moveD :=
      fun move_amt =>
        i <- readSTRef ref;;
        writeSTRef ref (i + move_amt)%Z in
    let offsetX :=
      i <- readSTRef ref;;
      Ret (i - init)%Z in
    Ret (mkPoint (readSTRef ref) moveD offsetX).


  Definition testtoST1 : itree E0 (Z * Z * Z) :=
    p <- @class_pointST 0 1;;
    a <- getX p;;
    moveD p 2;;
    b <- getX p;;
    c <- offsetX p;;
    Ret (a,b,c).


  Definition testtoST2 : itree E0 (Z * Z * Z * Z) :=
      p1 <- @class_pointST 0 1;;
      p2 <- @class_pointST 1 10;;
      a <- getX p1;;
      b <- getX p2;;
	    (* reading from one and putting into the other *)
      v1 <- getX p1;; moveD p2 v1;;
      c <- getX p1;;
      d <- getX p2;;
      Ret (a,b,c,d)
  .
      
    
    

End PointDef.


Transparent HAList.halist_lookup HAList.halist_add
            HAList.HMap_halist HAList.HMapOk_halist.
Existing Instance nat_ix_correct.
Existing Instance nat_ix_stref.

Definition run_test1 : itree (exceptE Err) (Z * Z * Z) :=
  runST (T := nat) (ltu := Nat.le) (V := fun _ : nat => Z) (S := unit) testtoST1.

Lemma point_run_burn1 : burn 100 run_test1 = Ret (1, 3, 2)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_test2 : itree (exceptE Err) (Z * Z * Z * Z) :=
  runST (T := nat) (ltu := Nat.le) (V := fun _ : nat => Z) (S := unit) testtoST2.

Lemma point_run_burn2 : burn 100 run_test2 = Ret (1, 10, 1, 11)%Z.
Proof. lazy. reflexivity. Qed.



From Crane Require Import Mapping.ZInt.

Definition testtoST1_ext :=
  Eval unfold testtoST1, class_pointST in (testtoST1 unit).
Definition testtoST2_ext :=
  Eval unfold testtoST2, class_pointST in (testtoST2 unit).

Crane Extraction "object_model" testtoST1_ext testtoST2_ext.









  



  
