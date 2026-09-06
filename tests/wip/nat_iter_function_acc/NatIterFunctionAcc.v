From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** [Nat.iter] is lowered to a [for] whose accumulator is declared [auto] from
    the *initial* value.  When the iterated type is a function type the initial
    value is a lambda, so the accumulator's deduced type is that one closure
    type, and the assignment of the next iteration's [std::function] to it has
    no viable overload.  The accumulator must be declared at the iteration's
    type, not the seed's. *)

Module NatIterFunctionAcc.

  Definition run : nat :=
    Nat.iter 10 (fun f => fun x => f (x + 1)) (fun x => x) 0.

End NatIterFunctionAcc.

Crane Extraction "nat_iter_function_acc" NatIterFunctionAcc.
