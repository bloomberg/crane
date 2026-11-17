From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [tt] returned where the result type is computed by a type-level function.

    [tuple (nats n)] is [unit] at [0] and a pair otherwise; erased, it
    is the box, which holds [tt] as well as it holds a pair.  The [0] branch
    of [ones] is reachable -- every call ends there -- so it must return its
    [tt], not be taken for a branch a dependent match rules out. *)
Module TtAtComputedType.

Fixpoint tuple (xs : list Set) : Set :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Fixpoint nats (n : nat) : list Set :=
  match n with
  | 0 => []
  | S m => nat :: nats m
  end.

Fixpoint ones (n : nat) : tuple (nats n) :=
  match n with
  | 0 => tt
  | S m => (1, ones m)
  end.

Definition first : nat := fst (ones 1).
Definition second : nat := fst (snd (ones 2)).

End TtAtComputedType.

Crane Extraction "tt_at_computed_type" TtAtComputedType.
