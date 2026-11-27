From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.

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

(** [@nil (list A)] in a definition constrained by a class: no [fold_left]
    matched a list of erased elements. *)
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.

Definition f1 {A : Type} `{Sz A} (a : A) : string :=
  let fix go (l : list bool) (acc : string) {struct l} : string :=
    match l with [] => "" | _ :: _ => "ab" end in
  go (fold_left (fun (acc : list bool) (e : list A) => [true]) (@nil (list A)) []) "".

Definition f4 (n : nat) : string := f1 n.
Definition t4 : nat := String.length (f4 5).

End PolyNilPairTypeErased.

Crane Extraction "poly_nil_pair_type_erased" PolyNilPairTypeErased.
