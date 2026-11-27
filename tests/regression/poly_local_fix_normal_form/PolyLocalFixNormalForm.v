From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A polymorphic definition whose local fixpoint returns list literals of the
    type parameter: under CRANE_CHECK_IR=1 (the test suite's setting)
    extraction raises an anomaly, "the normalized Core program is not in
    normal form: normalizing ... again rewrites it".  Without the check the
    C++ builds. *)
Module PolyLocalFixNormalForm.

Definition f {A : Type} (a : A) : list A :=
  let fix go (l : list nat) (acc : list A) {struct l} : list A :=
    match l with [] => [a] | _ :: _ => [a; a] end in go [] [a].

Definition t : nat := length (f 3).

End PolyLocalFixNormalForm.

Crane Extraction "poly_local_fix_normal_form" PolyLocalFixNormalForm.
