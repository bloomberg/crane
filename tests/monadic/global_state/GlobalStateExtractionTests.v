From Stdlib Require Import
  Arith.PeanoNat
  Extraction
  PrimString
.


From ITree Require Import ITree.

From Crane Require Import
  Monads.ITree
  Monads.Indices
  Monads.GlobalState
  Mapping.NatIntStd
.   


From CraneTestsMonadic.global_state Require Import GlobalStateExamples.


Module GlobalStateTests. 
  (* Re-exporting instances so they're available to call in the exported file. *)
  (* Just referring to them does not seem to work to extract them here, unfolding does *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : GlobRefClass nat := Eval unfold nat_ix_globref in nat_ix_globref.
  Definition new_and_read_both_nat := Eval unfold new_and_read_both_nat in (@new_and_read_both_nat nat Nat.le).
  Definition fib_Glob := Eval unfold fib_Glob,fib_loop in (@fib_Glob nat Nat.le).
  Definition fib_fun := Eval unfold fib_fun in fib_fun.

  Definition counter := Eval unfold start_counter in (@start_counter nat Nat.le nat_idx nat_stref).
  Definition counter_next_mine := Eval unfold counter_next in (@counter_next nat Nat.le nat_idx nat_stref).

  Definition gensym (counter : GlobRef nat) (prefix : string) :=
    v <- counter_next_mine counter;;
    Ret (PrimString.cat prefix (string_of_nat v)).

End GlobalStateTests. 
  
Set Crane Loopify.


Crane Extraction "global_state" GlobalStateTests.
