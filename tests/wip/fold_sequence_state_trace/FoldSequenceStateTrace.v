(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: fold-sequence state updates over real-valued origami primitives. *)

From Stdlib Require Import Reals List.
Import ListNotations.
Open Scope R_scope.

Module FoldSequenceStateTraceCase.

Definition Point : Type := (R * R)%type.

Record Line : Type := {
  A : R;
  B : R;
  C : R
}.

Inductive Fold : Type :=
| fold_line_ctor : Line -> Fold.

Definition fold_line (f : Fold) : Line :=
  match f with
  | fold_line_ctor l => l
  end.

Definition line_xaxis : Line := {| A := 0; B := 1; C := 0 |}.
Definition line_yaxis : Line := {| A := 1; B := 0; C := 0 |}.

Definition point_O : Point := (0, 0).
Definition point_X : Point := (1, 0).
Definition point_diag : Point := (1, 1).

Definition line_through (p1 p2 : Point) : Line :=
  let '(x1, y1) := p1 in
  let '(x2, y2) := p2 in
  match Req_EM_T x1 x2 with
  | left _ =>
      {| A := 1; B := 0; C := - x1 |}
  | right _ =>
      let a := y1 - y2 in
      let b := x2 - x1 in
      let c := x1 * y2 - x2 * y1 in
      {| A := a; B := b; C := c |}
  end.

Definition perp_bisector (p1 p2 : Point) : Line :=
  let '(x1, y1) := p1 in
  let '(x2, y2) := p2 in
  match Req_EM_T x1 x2 with
  | left _ =>
      match Req_EM_T y1 y2 with
      | left _ => {| A := 1; B := 0; C := - x1 |}
      | right _ =>
          let a := 0 in
          let b := 2 * (y2 - y1) in
          let c := x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2 in
          {| A := a; B := b; C := c |}
      end
  | right _ =>
      let a := 2 * (x2 - x1) in
      let b := 2 * (y2 - y1) in
      let c := x1 * x1 + y1 * y1 - x2 * x2 - y2 * y2 in
      {| A := a; B := b; C := c |}
  end.

Definition perp_through (p : Point) (l : Line) : Line :=
  let '(x, y) := p in
  let c := A l * y - B l * x in
  {| A := B l; B := - A l; C := c |}.

Definition fold_O1 (p1 p2 : Point) : Fold :=
  fold_line_ctor (line_through p1 p2).

Definition fold_O2 (p1 p2 : Point) : Fold :=
  fold_line_ctor (perp_bisector p1 p2).

Definition fold_O4 (p : Point) (l : Line) : Fold :=
  fold_line_ctor (perp_through p l).

Inductive FoldStep : Type :=
| FS_O1 : Point -> Point -> FoldStep
| FS_O2 : Point -> Point -> FoldStep
| FS_O4 : Point -> Line -> FoldStep.

Definition FoldSequence : Type := list FoldStep.

Definition execute_fold_step (step : FoldStep) : Line :=
  match step with
  | FS_O1 p1 p2 => fold_line (fold_O1 p1 p2)
  | FS_O2 p1 p2 => fold_line (fold_O2 p1 p2)
  | FS_O4 p l => fold_line (fold_O4 p l)
  end.

Record ConstructionState : Type := mkState {
  state_points : list Point;
  state_lines : list Line
}.

Definition initial_state : ConstructionState :=
  mkState [point_O; point_X] [line_xaxis; line_yaxis].

Definition add_fold_to_state
    (st : ConstructionState)
    (step : FoldStep)
    : ConstructionState :=
  let new_line := execute_fold_step step in
  mkState (state_points st) (new_line :: state_lines st).

Fixpoint execute_sequence
    (st : ConstructionState)
    (seq : FoldSequence)
    : ConstructionState :=
  match seq with
  | [] => st
  | step :: rest => execute_sequence (add_fold_to_state st step) rest
  end.

Definition sample_sequence : FoldSequence :=
  [FS_O1 point_O point_diag;
   FS_O2 point_O point_X;
   FS_O4 point_diag line_xaxis].

Definition sample_final_state : ConstructionState :=
  execute_sequence initial_state sample_sequence.

Definition line_count_after_sample_sequence
    (st : ConstructionState)
    : nat :=
  length (state_lines (execute_sequence st sample_sequence)).

Definition sample_sequence_length : nat :=
  length sample_sequence.

Definition sample_line_count : nat :=
  line_count_after_sample_sequence initial_state.

Definition sample_point_count : nat :=
  length (state_points sample_final_state).

Definition sample_lines_nonempty : bool :=
  negb (Nat.eqb sample_line_count 0).

Definition sample_has_expected_lines : bool :=
  Nat.eqb sample_line_count 5.

End FoldSequenceStateTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "fold_sequence_state_trace" FoldSequenceStateTraceCase.
