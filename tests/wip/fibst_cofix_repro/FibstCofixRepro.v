From Crane Require Import Monads.STMonad.

From Stdlib Require Import
  Arith.PeanoNat
  Strings.String
.

From Crane Require Import Monads.ITree.

From ExtLib Require Import
  Data.Monads.EitherMonad
  Structures.Maps
.

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

Import Monads.
Local Open Scope monad_scope.

Section FibstCofixRepro.

  Context {T : Type} {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST: STRefClass T}.

  Let V : T -> Type := fun _ => nat.
  Let S := unit.
  Let E0 := (STEvent T S V) +' exceptE Err.

  (* Reproduces a version of fibST in STMonadtest.v.
     This appears to recurse infinitely because 'n' is not decremented 
     on each recursive call.
      *)
  Definition fibst_repro (n : nat) : itree E0 nat :=
    let cofix go (x y : STRef S nat) (idx_x idx_y : T) : itree E0 nat :=
      match n with
      | 0 => @readSTRef _ _ _ _ _ _ idx_x x
      | Datatypes.S n =>
          x' <- @readSTRef _ _ _ _ _ _ idx_x x;;
          y' <- @readSTRef _ _ _ _ _ _ idx_y y;;
          @writeSTRef _ _ _ _ _ _ idx_x x y';;
          @writeSTRef _ _ _ _ _ _ idx_y y (x' + y');;
          Tau (go x y idx_x idx_y)
      end in
    if (Nat.leb n 2)
    then Ret n
    else
      x <- newSTRef zero 0;;
      y <- newSTRef (suc zero) 1;;
      go x y zero (suc zero).

End FibstCofixRepro.

Module FibstCofixReproTests.
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.
End FibstCofixReproTests.

Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Crane Extraction "fibst_cofix_repro"
  FibstCofixReproTests
  fibst_repro.
