From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification gap: a recursive call whose result feeds a branch condition.

    [parity]'s recursive call [parity m] is used inside the [if] guard
    [Nat.eqb (parity m) 0].  Loopify's [has_recursive_branch_dependency] check
    detects a recursive call in a condition/scrutinee position and bails out
    (the frame-based rewriter cannot keep the cloned subtree alive while
    evaluating the selected continuation), so the extracted C++ stays a plain
    recursive function rather than an explicit-stack loop.

    The recursion is linear (the guard names the recursive result exactly once),
    so it computes [n mod 2] without exponential blow-up. *)

Set Crane Loopify.

Module LoopifyGapIfCondition.

Fixpoint parity (n : nat) : nat :=
  match n with
  | O => 0
  | S m => if Nat.eqb (parity m) 0 then 1 else 0
  end.

End LoopifyGapIfCondition.

Crane Extraction "loopify_gap_if_condition" LoopifyGapIfCondition.parity.
