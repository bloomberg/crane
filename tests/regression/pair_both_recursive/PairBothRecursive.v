(* Regression: a [prod] whose *both* components are recursive gets no iterative
   drain.

   [br : (t * t) -> t] is the natural way to spell a binary node with a pair.
   A direct two-field constructor [br : t -> t -> t] does get a worklist
   destructor and survives 300k levels; routing the same two children through
   [std::pair] loses it.

   The value here is a degenerate left spine, so the recursion depth on
   destruction is the full 300k. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module PairBothRecursive.
Inductive t : Type := leaf : nat -> t | br : (t * t) -> t.
Definition wrap (acc : t) : t := br (acc, leaf 0).
Definition empty : t := leaf 1.
Fixpoint size (x : t) : nat :=
  match x with leaf _ => 1 | br p => match p with (a, b) => size a + size b end end.
End PairBothRecursive.
Crane Extraction "pair_both_recursive" PairBothRecursive.
