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

From Crane Require Monads.Global.
From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.Indices
.   


Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.


Section NatExampleTrees.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HGlob: Global.RefClass T}.
  
  Let V : T -> Type := fun _ => nat. (* Nats only for this example. *)
  Let E0 := (Global.Event T V) +' exceptE Err.


  Definition new_and_read_both_nat : itree E0 (nat * nat) :=
      r1 <- Global.new_ref zero 5 ;;
      r2 <- Global.new_ref (suc zero) 6 ;; 
      x1 <- Global.read_ref r1 ;;
      x2 <- Global.read_ref r2 ;;
      Ret (x1, x2).

  Definition tree_simp_nat : itree E0 nat :=
    v <- Global.new_ref zero 5;;
    Global.read_ref v.

  (* NOTE: this failing definition is intentional.
    The intent is to test that we don't allow reference indices to escape. *)
  Fail Definition tree_escape_nat : itree E0 nat :=
    v <- Global.new_ref 5;;
    Global.write_ref v (match v with Global.make_ref _ _ idx => idx end);;
    Global.read_ref v.

  Definition tree_simp_another_nat : itree E0 nat :=
    v <- Global.new_ref zero 5;;
    Global.write_ref v 6;;
    val <- Global.read_ref v;;
    Ret val.


   Definition write_incr_one (v : Global.ref nat) : itree E0 unit :=
    a <- @Global.read_ref E0 T HGlob V _ zero v;;
    @Global.write_ref E0 T HGlob V _ zero v (a + 1).

   Definition swap' (v w : Global.ref nat) : itree E0 unit :=
    a <- @Global.read_ref E0 T _ V  _ zero v;;
    b <- @Global.read_ref E0 T _ V _ (suc zero) w;;
    Global.write_ref v b;;
    Global.write_ref w a.

  (* "swap" function from "Lazy Functional State Threads", by John Launchbury and Simon L Peyton Jones. *)
  Fail Definition swap (v w : Global.ref nat) : itree E0 unit :=
    a <- Global.read_ref v;;
    b <- Global.read_ref w;;
    Global.write_ref v b;;
    Global.write_ref w a.



  (* source: https://wiki.haskell.org/Monad/Glob *)

  Definition idx_x := zero.
  Definition idx_y := suc zero.

  Fixpoint fib_loop (k : nat) (x y : Global.ref nat) : itree E0 nat :=
    match k with
    | 0 => @Global.read_ref _ _ _ _ _ idx_x x
    | Datatypes.S k' =>
        x' <- @Global.read_ref _ _ _ V _ idx_x x;;
        y' <- @Global.read_ref _ _ _ V _ idx_y y;;
        @Global.write_ref _ _ _ _ _ idx_x x y';;
        @Global.write_ref _ _ _ _ _ idx_y y (x' + y');;
        fib_loop k' x y 
    end.

  Definition fib_Glob (n : nat) : itree E0 nat :=
    if (Nat.ltb n 2)
    then Ret n
    else
      x <- Global.new_ref zero 0;;
      y <- Global.new_ref (suc zero) 1;;
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

  Definition start_counter : itree E0 (Global.ref nat) := Global.new_ref ctr_idx 0.

  Definition counter_next (ctr : Global.ref nat) :  itree E0 nat :=
    a <- @Global.read_ref E0 T HGlob V _ ctr_idx ctr;;
    @Global.write_ref E0 T HGlob V _ ctr_idx ctr (a + 1);;
    Ret a.

    
End NatExampleTrees.  

