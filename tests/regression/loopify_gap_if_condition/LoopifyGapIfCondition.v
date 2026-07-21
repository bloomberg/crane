From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification of a recursive call whose result feeds a branch condition.

    [parity]'s recursive call [parity m] is used inside the [if] guard
    [Nat.eqb (parity m) 0].  Loopify now hoists the value-typed recursive call
    out of the condition into a temporary and linearises it with a resume
    frame, so the extracted C++ is an explicit-stack loop.  (This shape
    previously defeated loopification: [has_recursive_branch_dependency] bailed
    to plain recursion.)  Kept as a regression guard.

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
