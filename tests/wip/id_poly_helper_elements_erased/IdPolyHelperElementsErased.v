(** Crane bug, found by Ephyra round 31: a polymorphic helper at a function
    type handed to [id] (declared at [crane::obj]).  Type reconstruction
    instantiates [nth_or]'s [A] at the erased type, so the list elements
    are coerced into a box and lowered as erased callables
    ([crane_erase_fn] of a generic lambda returning [List<crane::obj>]),
    while the call names [nth_or<crane::fn<List<uint64_t>(uint64_t)>>]:
    "no viable conversion from 'fn<crane::obj (...)>' to 'fn<List<unsigned
    long long> (unsigned long long)>'".  Expected: [c = 1].  Present at
    081553f85. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module IdPolyHelperElementsErased.

Definition nth_or {A : Type} (l : list A) (n : nat) (d : A) : A := nth n l d.
Definition c : nat :=
  length ((id (nth_or [(fun _ : nat => [7])] 0 (fun _ : nat => @nil nat))) 0).

End IdPolyHelperElementsErased.

Crane Extraction "id_poly_helper_elements_erased" IdPolyHelperElementsErased.
