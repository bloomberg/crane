From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    [g4] returns [Z -> list pt] through a non-tail local fixpoint whose step folds over the recursive result: CRANE_CHECK_IR=1 reports "resume plan: the recursion plan and the finished body disagree on whether a statement resumes after a recursive call". *)
Module NontailFoldResumePlan.
Record pt : Type := mkpt { px : nat; py : bool }.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Definition st (A : Type) : Type := nat -> A * nat.

Fixpoint g4 (n80 : nat) : (Z -> (list pt)) :=
  match n80 with O => (fun _ : Z => (@nil pt)) | S m81 => (let fix go92 (l93 : (list pt)) (acc94 : (Z -> (list pt))) {struct l93} : (Z -> (list pt)) := match l93 with [] => (g4 m81) | e95 :: rest96 => let rv97 := go92 rest96 acc94 in (fold_right (fun (e101 : (list nat)) (acc100 : (Z -> (list pt))) => acc100) rv97 (@nil (list nat))) end in go92 (@nil pt) (fun _ : Z => (@nil pt)))
  end.
End NontailFoldResumePlan.

Crane Extraction "nontail_fold_resume_plan" NontailFoldResumePlan.
