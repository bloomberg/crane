From Stdlib Require Import PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

(** A recursive call made through a coercion of its callee is a recursive
    call.

    [Nat.even_EvenT] calls itself as [(magic even_EvenT) n'], the coercion
    standing for the change of index in its result type, and the C++ calls
    [even_EvenT(n1)] where it stands, below the frame that binds the result.
    The recursion plan read only a callee written as a bare global, saw no
    recursion, and the function was left calling itself: [half] of two
    million ran two million C++ frames deep. *)

Module LoopifyCoercedSelfCall.

Definition half (n : nat) (H : Nat.even n = true) : nat := proj1_sig (Nat.even_EvenT n H).

End LoopifyCoercedSelfCall.

Crane Extraction "loopify_coerced_self_call" LoopifyCoercedSelfCall.
