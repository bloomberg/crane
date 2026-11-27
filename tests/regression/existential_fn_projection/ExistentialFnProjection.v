(** The second component of a [sigT] is stored at the erased type [std::any],
    because the first component is a [Type].  Projecting it out therefore has
    to cast it back to the type the projection's position expects.  It does
    not: the [std::any] is used directly, as a callee when the payload is a
    function and as a value when it is data. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.

Module ExistentialFnProjection.
  Definition measurer : {A : Type & A -> nat} :=
    existT (fun A => A -> nat) nat (fun x => x + 1).

  Definition measured : nat := projT2 measurer 4.

  Definition tagged : {A : Type & (A * nat)%type} :=
    existT (fun A => (A * nat)%type) nat (7, 8).

  Definition tag : nat := snd (projT2 tagged).
End ExistentialFnProjection.

Crane Extraction "existential_fn_projection" ExistentialFnProjection.
