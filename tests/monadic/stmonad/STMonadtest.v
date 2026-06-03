
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
.

From Crane Require Import Monads.ITree.
From ExtLib Require Import
  Data.Bool
  Data.List
  Data.Map.FMapAList
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Structures.Functor
  Structures.Maps
  Structures.Traversable
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



  

Section ExampleTrees.

  Context {E : Type -> Type}.
  Context {S : Type}.
  (* Variable (ltu : T -> T -> Prop). *)
  Context `{Ix_Correct nat Nat.le}.
  Context {HST: STRefClass nat}.

  Let V : nat -> Type := fun _ => nat. (* Nats only for this example. *)
  Context {HSEv: STEvent nat S V -< E}. 
  Context `{exceptE Err -< E}.
  Let E0 := (STEvent nat S V) +' E.


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
    a <- @readSTRef E0 nat S  _ V  _ (STRefToIx _ _ v) v;;
    b <- @readSTRef E0 nat S _ V _ (STRefToIx _ _ w) w;;
    writeSTRef v b;;
    writeSTRef w a.

  (* "swap" function from "Lazy Functional State Threads", by John Launchbury and Simon L Peyton Jones. *)
  (* TODO: would be good for indices here to be inferrable. *)
  Fail Definition swap (v w : STRef S nat) : itree E0 unit :=
    a <- readSTRef v;;
    b <- readSTRef w;;
    writeSTRef v b;;
    writeSTRef w a.



  (* TODO: Quicksort Example in haskell. *)

(* import Control.Monad.ST
 * import Data.Array.ST
 * import Data.Foldable
 * import Control.Monad
 * 
 * -- wiki-copied code starts here
 * partition arr left right pivotIndex = do
 *     pivotValue <- readArray arr pivotIndex
 *     swap arr pivotIndex right
 *     storeIndex <- foreachWith [left..right-1] left (\i storeIndex -> do
 *         val <- readArray arr i
 *         if (val <= pivotValue)
 *             then do
 *                  swap arr i storeIndex
 *                  return (storeIndex + 1)
 *             else do
 *                  return storeIndex )
 *     swap arr storeIndex right
 *     return storeIndex
 * 
 * qsort arr left right = when (right > left) $ do
 *     let pivotIndex = left + ((right-left) `div` 2)
 *     newPivot <- partition arr left right pivotIndex
 * 
 *     qsort arr left (newPivot - 1)
 *     qsort arr (newPivot + 1) right
 * 
 * -- wrapper to sort a list as an array
 * sortList xs = runST $ do
 *     let lastIndex = length xs - 1
 *     arr <- newListArray (0,lastIndex) xs :: ST s (STUArray s Int Int)
 *     qsort arr 0 lastIndex
 *     newXs <- getElems arr
 *     return newXs
 * 
 * -- test example
 * main = print $ sortList [212498,127,5981,2749812,74879,126,4,51,2412]
 * 
 * -- helpers
 * swap arr left right = do
 *     leftVal <- readArray arr left
 *     rightVal <- readArray arr right
 *     writeArray arr left rightVal
 *     writeArray arr right leftVal
 * 
 * -- foreachWith takes a list, and a value that can be modified by the function, and
 * -- it returns the modified value after mapping the function over the list.  
 * foreachWith xs v f = foldlM (flip f) v xs *)
  
End ExampleTrees.



(* Crane Extract Skip Ix. *)
Require Import Crane.Mapping.NatIntStd.
Crane Extraction "stmonad" newAndReadBoth tree_simp tree_simp_another.

