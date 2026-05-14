From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module Type Params.
  Parameter A : Type.
End Params.

Module Worker (P : Params).
  Fixpoint replicate (n : nat) (x : P.A) : list P.A :=
    match n with
    | O => nil
    | S n' => cons x (replicate n' x)
    end.

  Definition process_with_context (ctx : list P.A) (xs : list nat) : list nat :=
    map (fun x => x + length ctx) xs.
End Worker.

Module NatParams <: Params.
  Definition A := nat.
End NatParams.

Module W := Worker NatParams.

Module LambdaCapturePerf.

Fixpoint iota (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => cons n' (iota n')
  end.

Definition test : nat :=
  let ctx := W.replicate 500 42 in
  let input := iota 500 in
  length (W.process_with_context ctx input).

End LambdaCapturePerf.

Crane Extraction "lambda_capture_perf" LambdaCapturePerf.
