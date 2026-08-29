From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AssocTypeTwoSwapped.
  (** Two associated [Type] fields in one class.  Each method must be given
      the associated type it actually mentions: [mkx] returns [X] and [xy]
      returns [Y], even though extraction sees the class's fields in reverse
      declaration order. *)
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
