From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AssocTypeOptionLeak.
  (** Same associated-type resolution as [assoc_type_tvar_leak], reached
      through [option] rather than [list]. *)
  Class Opt := { O : Type ; some_ : nat -> option O ; sz : O -> nat }.

  Instance OL : Opt :=
    { O := list nat
    ; some_ := fun n => Some (repeat n n)
    ; sz := @length nat }.

  Definition go `{Opt} (n : nat) : nat :=
    match some_ n with Some o => sz o | None => 0 end.

  Definition run (k : nat) : nat := go (k + 4).
End AssocTypeOptionLeak.

Crane Extraction "assoc_type_option_leak" AssocTypeOptionLeak.
