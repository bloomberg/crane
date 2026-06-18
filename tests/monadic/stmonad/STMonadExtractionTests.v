
(* TODO: optimize imports *)
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

From CraneTestsMonadic.stmonad Require Import STMonadExamples.

Module STMonadTests. 
  (* Re-exporting instances so they're available to call in the exported file. *)
  (* Just referring to them does not seem to work to extract them here, unfolding does *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.

  Definition array_simp_fixed_init := Eval unfold array_simp_fixed_init in (@array_simp_fixed_init nat unit Nat.le).
  Definition array_simp_list := Eval unfold array_simp_list in (@array_simp_list nat unit Nat.le).
  Definition fib_ST := Eval unfold fib_ST in (@fib_ST nat unit Nat.le).
  Definition fib_fun := Eval unfold fib_fun in fib_fun.
  Definition list_hd := List.hd.
  Definition list_tl := List.tl.
  Definition new_and_read_both_bool := Eval unfold new_and_read_both_bool in (@new_and_read_both_bool nat unit Nat.le).
  Definition new_and_read_both_nat := Eval unfold new_and_read_both_nat in (@new_and_read_both_nat nat unit Nat.le).
  Definition tree_simp_another_nat := Eval unfold tree_simp_another_nat in (@tree_simp_another_nat nat unit Nat.le).
  Definition tree_simp_bool := Eval unfold tree_simp_bool in (@tree_simp_bool nat unit Nat.le).
  Definition tree_simp_nat := Eval unfold tree_simp_nat in (@tree_simp_nat nat unit Nat.le).
  (* qsort TODO: extract qsort! *)

End STMonadTests.


Require Import Crane.Mapping.NatIntStd.



Crane Extraction "stmonad" STMonadTests.
