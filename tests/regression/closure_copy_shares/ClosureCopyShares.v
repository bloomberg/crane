From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A closure is a shared, immutable value: copying one copies a pointer.
    The closures below capture a list and other closures, so a copy that
    cloned its captures would allocate. *)
Module ClosureCopyShares.

Fixpoint sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

(** Captures a list. *)
Definition adder (l : list nat) : nat -> nat := fun x => sum l + x.

(** Captures two closures. *)
Definition compose (f g : nat -> nat) : nat -> nat := fun x => f (g x).

(** Stored in a list, so they are function values rather than functions. *)
Definition closures : list (nat -> nat) :=
  let a := adder [1; 2; 3; 4; 5; 6; 7; 8] in
  [a; compose a (compose S a)].

End ClosureCopyShares.

Crane Extraction "closure_copy_shares" ClosureCopyShares.
