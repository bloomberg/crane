From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [@nil (nat * A)] in a polymorphic definition still loses the type
    parameter (the [@nil A] case in poly_nil_type_erased is fixed): the
    [fold_left] receiver is a list of [crane::obj] pairs and its [requires]
    clause rejects the step function. *)
Module PolyNilPairTypeErased.

Definition f {A : Type} (a : A) : nat :=
  fold_left (fun (acc : nat) (e : nat * A) => S acc) (@nil (nat * A)) 3.

Definition t : nat := f true.

End PolyNilPairTypeErased.

Crane Extraction "poly_nil_pair_type_erased" PolyNilPairTypeErased.
