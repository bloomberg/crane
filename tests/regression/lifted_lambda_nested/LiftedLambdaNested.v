(* WIP: a lambda nested inside a lambda is lifted to a helper emitted after its use. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module LiftedLambdaNested.
Inductive t : Type := L | N : t -> t.
Fixpoint depth (x : t) : nat := match x with L => 0 | N u => S (depth u) end.
Definition go : nat :=
  let x := N (N L) in
  let outer := fun (_ : nat) => let inner := fun (_ : nat) => depth x in inner 0 + depth x in
  outer 0 + outer 1.
End LiftedLambdaNested.
Crane Extraction "lifted_lambda_nested" LiftedLambdaNested.
