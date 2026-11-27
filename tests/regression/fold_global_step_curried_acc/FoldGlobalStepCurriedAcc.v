From Crane Require Import Mapping.NatInt Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane, alongside branch_callables_curried_join.

    A global step passed to [fold_left] whose accumulator is a function of
    two arguments: [fold_left]'s type variable spells the accumulator
    curried, [fold_left<fn<fn<uint64_t(bool)>(int64_t)>>], while the
    adapter naming [step] as a value took it, and returned it, flat ("no
    matching member function for call to 'fold_left'").  The adapter now
    takes such a parameter curried, hands [step] a flat closure applying it
    one argument at a time, and returns the rest curried. *)
Module FoldGlobalStepCurriedAcc.

Definition step (acc : Z -> bool -> nat) (x : nat) : Z -> bool -> nat :=
  match x with
  | O => (fun _ : Z => (fun b : bool => if b then 1 else 0))
  | S _ => (fun z b => acc z (negb b))
  end.

Definition t1 (l : list nat) : nat := (fold_left step l (fun _ _ => 7)) 0%Z true.

Definition step2 (acc : nat -> nat) (x : nat) : nat -> nat := fun y => acc (x + y).

Definition t2 (l : list nat) : nat := (fold_left step2 l (fun y => y)) 1.

End FoldGlobalStepCurriedAcc.

Crane Extraction "fold_global_step_curried_acc" FoldGlobalStepCurriedAcc.
