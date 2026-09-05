From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module CurriedValueInContainer.

(** A curried or partially applied function value stored in a container is
    emitted as an uncurried multi-argument lambda. *)
Definition constK {A : Type} : forall B : Type, A -> B -> A := fun B a _ => a.

Definition use : nat :=
  constK bool 5 true + constK (list nat) 6 [1;2] + constK (nat -> nat) 7 (fun n => n).

(** Stored in a list and reapplied. *)
Definition stored : list (nat -> nat -> nat) := [constK nat; fun a _ => a * 2].

Definition total : nat :=
  use + fold_left (fun acc f => acc + f 3 4) stored 0.

End CurriedValueInContainer.
Crane Extraction "curried_value_in_container" CurriedValueInContainer.
