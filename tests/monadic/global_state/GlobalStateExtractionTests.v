(* TODO: optimize imports *)

From Stdlib Require Import
  Arith.PeanoNat
  Classes.EquivDec
  Extraction
  Init.Peano
  List
  Morphisms
  PrimString
  Strings.String
.

From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Map.FMapAList
  Data.String
.


From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.GlobalState
.   

From CraneTestsMonadic.global_state Require Import GlobalStateExamples.

Import ListNotations.


Module GlobalStateTests. 
  (* Re-exporting instances so they're available to call in the exported file. *)
  (* Just referring to them does not seem to work to extract them here, unfolding does *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : GlobRefClass nat := Eval unfold nat_ix_globref in nat_ix_globref.
  Definition new_and_read_both_nat := Eval unfold new_and_read_both_nat in (@new_and_read_both_nat nat Nat.le).
  Definition fib_Glob := Eval unfold fib_Glob,fib_loop in (@fib_Glob nat Nat.le).
  Definition fib_fun := Eval unfold fib_fun in fib_fun.

End GlobalStateTests. 
  
Set Crane Loopify.

Require Import Crane.Mapping.NatIntStd.
Crane Extraction "global_state" GlobalStateTests.
