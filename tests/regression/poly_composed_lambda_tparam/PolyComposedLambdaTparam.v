From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    In a polymorphic definition with a class constraint, composing two
    let-bound lambdas ([cf (cg c)] where [cg : nat -> A]) prints a type that
    names [T1] outside any template: "use of undeclared identifier 'T1'". *)
Module PolyComposedLambdaTparam.

Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_bool : Sz bool := { sz b := if b then 1 else 0 }.

Definition f {A : Type} `{Sz A} (a : A) : nat -> bool * nat :=
  let cf := (fun y : A => (true, 0)) in let cg := (fun y : nat => a) in fun c : nat => cf (cg c).

Definition t : nat := snd (f true 3) + (if fst (f false 4) then 1 else 0).

End PolyComposedLambdaTparam.

Crane Extraction "poly_composed_lambda_tparam" PolyComposedLambdaTparam.
