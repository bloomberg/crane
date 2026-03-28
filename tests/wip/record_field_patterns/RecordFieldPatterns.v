(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Tests for record extraction edge cases.

   Known bugs exposed by this test:
   1. Sub-module type qualification: PointImpl.mk generates unqualified
      "Point" instead of "RecordFieldPatterns::Point" in the .cpp file.
      (struct_qualifier_for doesn't handle types referenced from sibling
      sub-modules.)
   2. Records with Type-valued fields (Container, commented out):
      Crane promotes the record to a C++ concept, but call sites still
      try to instantiate it as a struct.

   Additionally exercises (all currently working):
   - Matching on record field VALUES (Rocq desugars to nested if/else)
   - Nested record destructuring (Segment containing Points)
   - Records with erased Prop fields (Bounded)
   - Higher-order record projection (map/fold over fields)
   - Records through module types and functors
*)
From Stdlib Require Import List Bool.
Import ListNotations.
From Crane Require Mapping.Std Mapping.NatIntStd.
Require Crane.Extraction.

Module RecordFieldPatterns.

(* ========================================================================= *)
(* 1. Basic record field-value matching.                                     *)
(*    Rocq desugars this to nested if/else inside a single-branch case.      *)
(*    This works, but exercises the general destructuring path.              *)
(* ========================================================================= *)

Record Point := mkPoint { px : nat; py : nat }.

Definition classify_point (p : Point) : nat :=
  match p with
  | {| px := 0;   py := 0   |} => 0
  | {| px := 0;   py := _   |} => 1
  | {| px := _;   py := 0   |} => 2
  | {| px := x;   py := y   |} => x + y
  end.

Definition zero_x (p : Point) : nat :=
  match p with
  | {| px := 0; py := n |} => n
  | {| px := S m; py := n |} => m + n
  end.

(* ========================================================================= *)
(* 2. Record through a polymorphic function.                                 *)
(*    If the type parameter erases the Tglob, record_fields_of_type          *)
(*    returns [] and the handler is skipped.                                 *)
(* ========================================================================= *)

Definition identity {A : Type} (x : A) : A := x.

(** Apply a polymorphic function to a record — the record type flows
    through a type variable. *)
Definition id_point (p : Point) : Point := identity p.

(** Polymorphic projection: the match happens inside a polymorphic context
    where the scrutinee's type might not be Tglob. *)
Definition generic_first {A B : Type} (pair : A * B) : A := fst pair.

Definition point_pair (p : Point) : nat * nat := (px p, py p).

Definition first_coord (p : Point) : nat :=
  generic_first (point_pair p).

(* ========================================================================= *)
(* 3. Record through a Section variable.                                     *)
(*    After section closing, the record type becomes parameterized.          *)
(* ========================================================================= *)

Section WithScale.
  Variable scale : nat.

  (** Record whose field default depends on the section variable. *)
  Record ScaledPoint := mkScaledPoint {
    sp_x : nat;
    sp_y : nat
  }.

  Definition scaled_sum (sp : ScaledPoint) : nat :=
    match sp with
    | mkScaledPoint x y => scale * (x + y)
    end.
End WithScale.

(** After section closing, scaled_sum is parameterized by [scale : nat].
    The record type itself is NOT parameterized (scale is only used in
    the function body), but the function signature changes. *)
Definition test_labeled := scaled_sum 3 (mkScaledPoint 10 20).

(* ========================================================================= *)
(* 4. Record inside a module type / functor — the record type is abstract    *)
(*    until instantiation, which may prevent Tglob resolution.              *)
(* ========================================================================= *)

Module Type HasRecord.
  Parameter R : Type.
  Parameter mk : nat -> nat -> R.
  Parameter get_x : R -> nat.
  Parameter get_y : R -> nat.
End HasRecord.

Module PointImpl <: HasRecord.
  Definition R := Point.
  Definition mk := mkPoint.
  Definition get_x := px.
  Definition get_y := py.
End PointImpl.

Module UseRecord (M : HasRecord).
  Definition sum_fields (r : M.R) : nat := M.get_x r + M.get_y r.
End UseRecord.

Module UR := UseRecord PointImpl.
Definition test_functor := UR.sum_fields (mkPoint 100 200).

(* ========================================================================= *)
(* 5. Nested record destructuring — matching on inner record fields.         *)
(* ========================================================================= *)

Record Segment := mkSegment { seg_start : Point; seg_end : Point }.

Definition segment_length_sq (s : Segment) : nat :=
  match s with
  | {| seg_start := mkPoint x1 y1; seg_end := mkPoint x2 y2 |} =>
      let dx := x2 - x1 in
      let dy := y2 - y1 in
      dx * dx + dy * dy
  end.

(* ========================================================================= *)
(* 6. Record with erased Prop fields — tests index alignment.               *)
(* ========================================================================= *)

Record Bounded := mkBounded {
  lo : nat;
  lo_bound : lo > 0;
  hi : nat;
  hi_bound : hi < 1000;
  mid : nat
}.

Definition bounded_range (b : Bounded) : nat :=
  match b with
  | mkBounded l _ h _ m => h - l + m
  end.

(* ========================================================================= *)
(* 7. Higher-order record projection — field accessors used as functions.    *)
(* ========================================================================= *)

Definition sum_px (points : list Point) : nat :=
  fold_left (fun acc p => acc + px p) points 0.

Definition map_py (points : list Point) : list nat :=
  map py points.

(* ========================================================================= *)
(* 8. Record swap — construction + destruction in one function.              *)
(* ========================================================================= *)

Definition swap (p : Point) : Point :=
  match p with
  | {| px := x; py := y |} => mkPoint y x
  end.

Definition double_swap (p : Point) : Point :=
  swap (swap p).

(* ========================================================================= *)
(* 9. Record with a Type-valued field (promoted).                            *)
(*    BUG: The Type-valued field causes Crane to promote the record to a     *)
(*    C++ concept, but call sites still try to instantiate it as a struct.   *)
(* ========================================================================= *)

Record Container := mkContainer {
  elem_type : Type;
  elem : elem_type;
  count : nat
}.

Definition get_count (c : Container) : nat := count c.

Definition test_container := get_count (mkContainer nat 42 5).

(* ========================================================================= *)
(* Test values                                                               *)
(* ========================================================================= *)

Definition test_origin   := classify_point (mkPoint 0 0).
Definition test_y_axis   := classify_point (mkPoint 0 5).
Definition test_x_axis   := classify_point (mkPoint 3 0).
Definition test_general  := classify_point (mkPoint 3 4).
Definition test_zero_x   := zero_x (mkPoint 0 42).
Definition test_nonzero  := zero_x (mkPoint 5 10).

Definition test_id := id_point (mkPoint 99 1).

Definition test_seg := segment_length_sq
  (mkSegment (mkPoint 1 2) (mkPoint 4 6)).

Definition test_sum := sum_px [mkPoint 10 0; mkPoint 20 0; mkPoint 30 0].
Definition test_map := map_py [mkPoint 0 1; mkPoint 0 2; mkPoint 0 3].

Definition test_swap := swap (mkPoint 3 7).

End RecordFieldPatterns.

Crane Extraction "record_field_patterns" RecordFieldPatterns.
