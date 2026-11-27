From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [fold_left] whose accumulator is a two-argument function: the step lambda's
    accumulator parameter is spelled flat ([crane::fn<uint64_t(uint64_t, uint64_t)>])
    while [fold_left]'s [T1] is the curried [crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>],
    so the [requires] clause rejects the call. *)
Module FoldCurriedAccumulator.

Definition g (l : list nat) : nat -> nat -> nat :=
  fold_left (fun (acc : nat -> nat -> nat) (e : nat) => fun x y => acc y (x + e))
    l (fun x y => x).

End FoldCurriedAccumulator.

Crane Extraction "fold_curried_accumulator" FoldCurriedAccumulator.
