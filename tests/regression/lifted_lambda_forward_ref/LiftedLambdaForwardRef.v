(* WIP: the lifted lambda helper is emitted after the definition that calls it, so the call site references an undeclared function. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module LiftedLambdaForwardRef.
Inductive t : Type := L | N : t -> t.
Definition later (x : t) : nat := match x with L => 1 | N _ => 2 end.
Definition go : nat := let x := N L in let f := fun (_ : nat) => later x in f 0 + f 1.
End LiftedLambdaForwardRef.
Crane Extraction "lifted_lambda_forward_ref" LiftedLambdaForwardRef.
