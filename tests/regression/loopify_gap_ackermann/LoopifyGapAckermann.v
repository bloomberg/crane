From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.

(** Nested (non-structural in a single argument) recursion through a local
    fixpoint.

    The Ackermann function recurses with the inner result as the argument of an
    outer recursive call: [ack m' (ack_n n')].  [ack_n] is a fixpoint local to
    [ack], so loopification adopts it as a second entry point of [ack]'s frame
    machine -- [_Enter] for [ack], [_Enter_ack_n] for the local fixpoint, one
    shared stack -- and the extracted [ack] has no C++ self-call. *)

Set Crane Loopify.

Module LoopifyGapAckermann.

Fixpoint ack (m : nat) : nat -> nat :=
  fix ack_n (n : nat) : nat :=
    match m with
    | O => S n
    | S m' =>
      match n with
      | O => ack m' 1
      | S n' => ack m' (ack_n n')
      end
    end.

End LoopifyGapAckermann.

Crane Extraction "loopify_gap_ackermann" LoopifyGapAckermann.ack.
