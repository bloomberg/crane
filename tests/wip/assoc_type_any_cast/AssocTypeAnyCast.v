From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AssocTypeAnyCast.
  (** A type class with an associated [Type] field.  The instance's method
      parameter is correctly specialised to [std::pair<uint64_t, uint64_t>],
      but its body still [any_cast]s the parameter as if it were erased, so the
      generated instance does not compile. *)
  Class Wrap := { W : Type ; wrap : nat -> W ; unwrap : W -> nat }.

  Instance PairWrap : Wrap :=
    { W := (nat * nat)%type
    ; wrap := fun n => (n, n)
    ; unwrap := fun p => fst p + snd p }.

  Definition roundtrip `{Wrap} (n : nat) : nat := unwrap (wrap n).

  Definition run (k : nat) : nat := roundtrip (k + 5).
End AssocTypeAnyCast.

Crane Extraction "assoc_type_any_cast" AssocTypeAnyCast.
