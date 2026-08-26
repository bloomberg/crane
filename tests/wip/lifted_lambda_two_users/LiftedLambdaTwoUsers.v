(* WIP: two definitions each lift a lambda; the helpers are emitted after their call sites. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module LiftedLambdaTwoUsers.
Inductive t : Type := L | N : t -> t.
Fixpoint depth (x : t) : nat := match x with L => 0 | N u => S (depth u) end.
Definition one : nat := let x := N L in let f := fun (_ : nat) => depth x in f 0 + f 1.
Definition two : nat := let y := N (N L) in let g := fun (_ : nat) => depth y in g 0 + g 1.
Definition go : nat := one + two.
End LiftedLambdaTwoUsers.
Crane Extraction "lifted_lambda_two_users" LiftedLambdaTwoUsers.
