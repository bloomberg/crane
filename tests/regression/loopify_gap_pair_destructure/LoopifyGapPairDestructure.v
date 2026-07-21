From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification of a non-tail recursive call whose result is immediately
    destructured and consumed.

    [swap_pair]'s recursive call [swap_pair m] returns a pair that is taken
    apart with [let (a, b) := ...] and both components are used to build the
    result.  Loopify now hoists the recursive call out of the match scrutinee
    into a temporary and linearises the continuation with a resume frame, so
    the extracted C++ is an explicit-stack loop.  (This shape previously stayed
    plain recursion.)  Kept as a regression guard. *)

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
