From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification gap: three-way mutual recursion.

    Loopify's mutual-recursion inliner ([try_inline_mutual_into]) folds a single
    partner into a self-recursive function that can then be loopified.  With a
    three-way cycle [a -> b -> c -> a] there is no single partner to inline, so
    none of the three is converted to self-recursion and all remain plain
    (mutually) recursive functions in the extracted C++. *)

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
