(** Crane bug, found by Ephyra round 31: a partial application passed where
    a polymorphic helper's callable parameter is deduced, at a function type
    whose argument is itself a function.  The inner [twice] is written at
    the curried template argument the outer slot states,
    [twice<fn<fn<nat(nat)>(fn<nat(nat)>)>>], but its arguments are lowered
    flat: the eta-expansion of [pick true h] takes [fn<nat(fn<nat(nat)>,
    nat)>] and returns a two-argument lambda, and [h] is a two-argument
    lambda.  "no matching function for call to 'twice'" (the
    [is_invocable_r] constraint fails).  Expected: [d = 4].  Present at
    081553f85. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module TwiceCurriedSlotFlatArgs.

Definition pick {A : Type} (b : bool) (x y : A) : A := if b then x else y.
Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition h (_ : nat -> nat) : nat -> nat := fun _ => 4.
Definition d : nat := (twice (twice (pick true h) h) (fun _ : nat => 5)) 3.

End TwiceCurriedSlotFlatArgs.

Crane Extraction "twice_curried_slot_flat_args" TwiceCurriedSlotFlatArgs.
