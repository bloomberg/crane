From Stdlib Require Import Arith.PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(** Loopification gap: nested (non-structural in a single argument) recursion.

    The Ackermann function recurses with the inner result as the argument of an
    outer recursive call: [ack m' (ack_n n')].  The outer [ack] call is not in a
    position loopify can linearise (its argument is itself a recursive
    invocation of the enclosing [fix]), so the extracted [ack] keeps a recursive
    self-call. *)

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
