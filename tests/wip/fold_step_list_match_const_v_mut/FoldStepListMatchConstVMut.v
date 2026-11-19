From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    A [fold_right] step lambda over [list pt] passes [match e5 with [] | [_] | _ :: _ :: _ => ..] as a local fixpoint's argument while the fixpoint's step folds over [e5]: the nested match calls [v_mut()] on a [const List<pt>] ("function is not marked const").  Same family as the fixed sum_match_const_v_mut. *)
Module FoldStepListMatchConstVMut.
Record pt : Type := mkpt { px : nat; py : bool }.
CoInductive stream : Type := SCons : nat -> stream -> stream.

Definition t_2 : nat :=
  ((fun w62 : ((list bool) -> (list Z)) => ((fun w63 : (list Z) => fold_left (fun w65 e => (w65 * 3 + (fun w64 : Z => Z.to_nat (Z.abs w64) * 2 + (if Z.ltb w64 0%Z then 1 else 0)) e) mod 10007) w63 1) (w62 (@nil bool)) + (fun w63 : (list Z) => fold_left (fun w65 e => (w65 * 3 + (fun w64 : Z => Z.to_nat (Z.abs w64) * 2 + (if Z.ltb w64 0%Z then 1 else 0)) e) mod 10007) w63 1) (w62 (@nil bool))) mod 10007) (fold_right (fun (e5 : (list pt)) (acc4 : ((list bool) -> (list Z))) => (let fix go6 (l7 : (list bool)) (acc8 : ((list bool) -> (list Z))) {struct l7} : ((list bool) -> (list Z)) := match l7 with [] => (fun _ : (list bool) => (@nil Z)) | e9 :: rest10 => go6 rest10 (if (fold_left (fun (acc12 : bool) (e13 : pt) => true) e5 true) then (fun _ : (list bool) => (@nil Z)) else (fun _ : (list bool) => (@nil Z))) end in go6 (match e5 with [] => (@nil bool) | [h22] => (@nil bool) | h22 :: h24 :: r23 => (@nil bool) end) (fun _ : (list bool) => (@nil Z)))) (fun _ : (list bool) => (@nil Z)) (@nil (list pt)))).
End FoldStepListMatchConstVMut.

Crane Extraction "fold_step_list_match_const_v_mut" FoldStepListMatchConstVMut.
