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
    fixpoint's accumulator is a literal list of [@nil A]; [g] is that list
    without the fixpoint.

    Nothing but the parameter written at [nil] says what the list holds; it
    names one of the definition's own type variables, which the constructor
    now takes when unification leaves its type argument open. *)
Module PolyNilTypeErased.

Definition f {A : Type} (a : A) : A :=
  fold_left (fun (acc : A) (e : A) => acc) (@nil A) a.

Definition t : nat := f 4.

Definition g {A : Type} (a : A) : nat := length [@nil A; @nil A].

Definition u : nat := g true.

End PolyNilTypeErased.

Crane Extraction "poly_nil_type_erased" PolyNilTypeErased.
