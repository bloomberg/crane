From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification of three-way mutual recursion.

    Loopify's mutual-recursion inliner ([try_inline_mutual_into]) folds cycle
    partners into a self-recursive function that can then be loopified.  It now
    handles cycles longer than two (transitive reachability), so a three-way
    cycle [a -> b -> c -> a] is inlined one hop at a time until self-recursive
    and each of [rot_a]/[rot_b]/[rot_c] extracts to a while-loop.  (Previously
    only 2-way cycles were inlined and these stayed recursive.)  Kept as a
    regression guard. *)

Set Crane Loopify.

Module LoopifyGapMutual3.

Fixpoint rot_a (n : nat) : nat :=
  match n with O => 0 | S k => rot_b k end
with rot_b (n : nat) : nat :=
  match n with O => 1 | S k => rot_c k end
with rot_c (n : nat) : nat :=
  match n with O => 2 | S k => rot_a k end.

End LoopifyGapMutual3.

Crane Extraction "loopify_gap_mutual3"
  LoopifyGapMutual3.rot_a
  LoopifyGapMutual3.rot_b
  LoopifyGapMutual3.rot_c.
