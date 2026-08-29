From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AssocTypeTwoSwapped.
  (** Two associated [Type] fields in one class.  Crane assigns the wrong
      associated type to each method: [mkx] is declared returning [Y]'s C++
      type and [xy] returning [X]'s, so neither instance method compiles. *)
  Class Two :=
    { X : Type ; Y : Type ; mkx : nat -> X ; xy : X -> Y ; ynat : Y -> nat }.

  Instance TT : Two :=
    { X := (nat * nat)%type
    ; Y := list nat
    ; mkx := fun n => (n, n)
    ; xy := fun p => [fst p; snd p]
    ; ynat := fun l => fold_left Nat.add l 0 }.

  Definition go `{Two} (n : nat) : nat := ynat (xy (mkx n)).

  Definition run (k : nat) : nat := go (k + 6).
End AssocTypeTwoSwapped.

Crane Extraction "assoc_type_two_swapped" AssocTypeTwoSwapped.
