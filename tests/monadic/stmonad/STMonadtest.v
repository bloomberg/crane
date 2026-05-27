
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
Import ST_IMPL.



Section ExampleTrees.

  Context {S : Type}.
  Context {E : Type -> Type}.
  Context `{IdxGenE -< E}.
  Context `{exceptE Err -< E}.


  Definition V : Idx S -> Type := fun _ => nat.
  Definition E0 := (STEvent S V) +' E.

(* newSTRef :
 * forall {E : Type -> Type} {S : Type} (V : Idx S -> Type),
 * STEvent S V -< E -> forall I : Idx S, V I -> itree E (STRef S (V I)) *)
  About readSTRef.
(* readSTRef :
 * forall {E : Type -> Type} {S : Type} (V : Idx S -> Type),
 * STEvent S V -< E -> forall I : Idx S, STRef S (V I) -> itree E (V I) *)
  (* TODO: tricky to state below! *)
  Definition newAndReadBoth : itree E0 (nat * nat) :=
    r1 <- newSTRef V _ 5 ;;
    r2 <- newSTRef V _ 6 ;;
    x1 <- readSTRef V _ r1 ;;
    x2 <- readSTRef V _ r2 ;;
    Ret (x1, x2).

  Definition tree_simp : itree E0 nat :=
    v <- newSTRef 5;;
    readSTRef v.

  (* NOTE: this failing definition is intentional.
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


  (* "swap" function from "Lazy Functional State Threads", by John Launchbury and Simon L Peyton Jones. *)
  Definition swap (v w : STRef S nat) : itree E0 unit :=
    a <- readSTRef v;;
    b <- readSTRef w;;
    writeSTRef v b;;
    writeSTRef w a.

End ExampleTrees.


From Crane Require Import Mapping.NatIntStd.   
Crane Extract Skip E0.
Crane Extraction "stmonad" newAndReadBoth tree_simp tree_simp_another.
