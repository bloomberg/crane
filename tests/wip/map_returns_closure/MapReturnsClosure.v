From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module MapReturnsClosure.

(** Mapping a list to a list of {e closures}.  The element type of the
    result is a function type, and the emitted [List::map] call fails its
    [std::is_invocable_r_v] constraint because the generated lambda returns a
    lambda rather than the declared element type. *)
Definition make_adders (xs : list nat) : list (nat -> nat) :=
  map (fun x => fun y => x + y) xs.

Definition apply_all (fs : list (nat -> nat)) (n : nat) : nat :=
  fold_left (fun acc f => acc + f n) fs 0.

Definition total : nat := apply_all (make_adders [1;2;3]) 10.

End MapReturnsClosure.
Crane Extraction "map_returns_closure" MapReturnsClosure.
