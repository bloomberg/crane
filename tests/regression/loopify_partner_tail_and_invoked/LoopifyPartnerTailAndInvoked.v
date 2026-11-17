From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** [walk] calls its partner [step] both as a tail call and as the operand
    of an addition, and [step] calls [walk] back where its body runs.  Its
    machine continues in [step]'s body at the tail call and enters a copy of
    [step] at the other, whose calls of [walk] are turns of the one machine:
    no call between the two runs on the C++ stack, however deep. *)

Module LoopifyPartnerTailAndInvoked.

  Fixpoint walk (n : nat) : nat :=
    match n with
    | O => 0
    | S m => if Nat.eqb (Nat.modulo m 2) 0 then step m else 1 + step m
    end
  with step (n : nat) : nat :=
    match n with
    | O => 1
    | S m => S (walk m)
    end.

End LoopifyPartnerTailAndInvoked.

Set Crane Loopify.
Crane Extraction "loopify_partner_tail_and_invoked" LoopifyPartnerTailAndInvoked.
