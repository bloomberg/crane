From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AssocTypeOptionLeak.
  (** Same template-parameter leak as [assoc_type_tvar_leak], reached through
      [option] rather than [list]: the instance body mentions the class's
      template parameter, which is not in scope in the instance struct. *)
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
