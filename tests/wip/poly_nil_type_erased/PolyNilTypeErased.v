From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [@nil A] in a polymorphic definition prints as [List<crane::obj>::nil()]
    instead of [List<T1>::nil()], so [fold_left]'s [requires] clause rejects
    the step function ([const crane::obj &] is not a [T1]).  The same erasure
    shows as "no viable conversion from 'List<crane::obj>'" when a local
    fixpoint's accumulator is a literal list of [@nil A]. *)
Module PolyNilTypeErased.

Definition f {A : Type} (a : A) : A :=
  fold_left (fun (acc : A) (e : A) => acc) (@nil A) a.

Definition t : nat := f 4.

End PolyNilTypeErased.

Crane Extraction "poly_nil_type_erased" PolyNilTypeErased.
