From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module SigtTypeWitnessContainer.

(** [projT2] of a [{ T : Type & list T }] is a [list T], but Crane erases the
    whole payload to [std::any], so the container operation on it fails:

      error: no member named 'length' in 'std::any'

    The payload's *outer* constructor is known ([list]); only the element type
    is existential, so [List<std::any>] would be the right erasure. *)

Definition pack {A} (l : list A) : { T : Type & list T } := existT _ A l.

Definition depth (p : { T : Type & list T }) : nat := List.length (projT2 p).

Definition run : nat := depth (pack (cons 1 (cons 2 nil))).

End SigtTypeWitnessContainer.

Crane Extraction "sigt_type_witness_container" SigtTypeWitnessContainer.run.
