(** A typeclass with a [Type]-valued carrier field, instantiated at a mapped
    type ([option nat]).  The instance method casts a value that is already
    concrete, and binds the payload at the erased element type:

    {v
      no viable conversion from 'std::any' to 'const uint64_t'
    v} *)

From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module TcCarrierOptionCast.

Class Box := { carrier : Type ; wrap : nat -> carrier ; peek : carrier -> nat }.

Instance OptBox : Box :=
  { carrier := option nat
  ; wrap := fun n => Some n
  ; peek := fun o => match o with Some n => n | None => 0 end }.

Definition test (n : nat) : nat := peek (wrap n).

End TcCarrierOptionCast.

Crane Extraction "tc_carrier_option_cast" TcCarrierOptionCast.
