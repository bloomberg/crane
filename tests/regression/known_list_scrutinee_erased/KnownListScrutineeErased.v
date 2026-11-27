From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Matching a literal [[None]] with a nested pattern: the known outer cons is
    simplified away and the tail is matched as [List<uint64_t>::nil()] while the
    alternative test names [List<std::optional<crane::obj>>::Nil]: the element
    type of the literal was lost, and [std::holds_alternative] does not compile. *)
Module KnownListScrutineeErased.

Definition t : option nat :=
  nth_error (match [@None nat] with [] => [] | [_] => [5] | _ :: _ :: _ => [0] end) 0.

End KnownListScrutineeErased.

Crane Extraction "known_list_scrutinee_erased" KnownListScrutineeErased.
