From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification gap: a non-tail recursive call whose result is immediately
    destructured and consumed.

    [swap_pair]'s recursive call [swap_pair m] returns a pair that is taken
    apart with [let (a, b) := ...] and both components are used to build the
    result.  This is genuine non-tail recursion whose continuation depends on
    the destructured recursive result; loopify does not linearise it, so the
    extracted C++ stays a plain recursive function. *)

Set Crane Loopify.

Module LoopifyGapPairDestructure.

Fixpoint swap_pair (n : nat) : nat * nat :=
  match n with
  | O => (0, 0)
  | S m => let (a, b) := swap_pair m in (b, S a)
  end.

End LoopifyGapPairDestructure.

Crane Extraction "loopify_gap_pair_destructure"
  LoopifyGapPairDestructure.swap_pair.
