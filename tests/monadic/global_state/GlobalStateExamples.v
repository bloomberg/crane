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
  Classes.EquivDec
  PrimString
  Basics
.

From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Map.FMapAList
  Data.Monads.EitherMonad
  Data.Pair
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


From Equations Require Import Equations.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.GlobalState
.   


Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.


Section NatExampleTrees.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HGlob: GlobRefClass T}.
  
  Let V : T -> Type := fun _ => nat. (* Nats only for this example. *)
  Let E0 := (GlobEvent T V) +' exceptE Err.


  (* TODO: autogenerate successive indices here? *)
  Definition new_and_read_both_nat : itree E0 (nat * nat) :=
      r1 <- newGlobRef zero 5 ;;
      r2 <- newGlobRef (suc zero) 6 ;; 
      x1 <- readGlobRef r1 ;;
      x2 <- readGlobRef r2 ;;
      Ret (x1, x2).

  Definition tree_simp_nat : itree E0 nat :=
    v <- newGlobRef zero 5;;
    readGlobRef v.

  (* NOTE: this failing definition is intentional.
    The intent is to test that we don't allow reference indices to escape. *)
  Fail Definition tree_escape_nat : itree E0 nat :=
    v <- newGlobRef 5;;
    writeGlobRef v (match v with mkGlobRef _ _ idx => idx end);;
    readGlobRef v.

  Definition tree_simp_another_nat : itree E0 nat :=
    v <- newGlobRef zero 5;;
    writeGlobRef v 6;;
    val <- readGlobRef v;;
    Ret val.


  (* TODO: indices here should be derivable from reference *)
   Definition write_incr_one (v : GlobRef nat) : itree E0 unit :=
    a <- @readGlobRef E0 T HGlob V _ zero v;;
    @writeGlobRef E0 T HGlob V _ zero v (a + 1).

   Definition swap' (v w : GlobRef nat) : itree E0 unit :=
    a <- @readGlobRef E0 T _ V  _ zero v;;
    b <- @readGlobRef E0 T _ V _ (suc zero) w;;
    writeGlobRef v b;;
    writeGlobRef w a.

  (* "swap" function from "Lazy Functional State Threads", by John Launchbury and Simon L Peyton Jones. *)
  (* TODO: would be good for indices here (and everywhere in the file) to be inferrable. *)
  Fail Definition swap (v w : GlobRef nat) : itree E0 unit :=
    a <- readGlobRef v;;
    b <- readGlobRef w;;
    writeGlobRef v b;;
    writeGlobRef w a.



  (* source: https://wiki.haskell.org/Monad/Glob *)

  Definition idx_x := zero.
  Definition idx_y := suc zero.

  Fixpoint fib_loop (k : nat) (x y : GlobRef nat) : itree E0 nat :=
    match k with
    | 0 => @readGlobRef _ _ _ _ _ idx_x x
    | Datatypes.S k' =>
        x' <- @readGlobRef _ _ _ V _ idx_x x;;
        y' <- @readGlobRef _ _ _ V _ idx_y y;;
        @writeGlobRef _ _ _ _ _ idx_x x y';;
        @writeGlobRef _ _ _ _ _ idx_y y (x' + y');;
        fib_loop k' x y 
    end.

  Definition fib_Glob (n : nat) : itree E0 nat :=
    if (Nat.ltb n 2)
    then Ret n
    else
      x <- newGlobRef zero 0;;
      y <- newGlobRef (suc zero) 1;;
      fib_loop n x y.

  Definition fib_fun (n : nat) : nat :=
    let fix fib' (n : nat) :=
      match n with
      | 0 => 0
      | 1 => 1
      | Datatypes.S (Datatypes.S m as m0) => fib' m0 + fib' m
      end in
    fib' n.

  Definition ctr_idx := suc (suc zero).

  Definition start_counter : itree E0 (GlobRef nat) := newGlobRef ctr_idx 0.

  Definition counter_next (ctr : GlobRef nat) :  itree E0 nat :=
    a <- @readGlobRef E0 T HGlob V _ ctr_idx ctr;;
    @writeGlobRef E0 T HGlob V _ ctr_idx ctr (a + 1);;
    Ret a.

    
End NatExampleTrees.  

