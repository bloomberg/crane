(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: spherical polygon winding and area trace over real-valued geometry. *)

From Stdlib Require Import Reals Rtrigo Rtrigo_facts Ratan Rsqrt_def List.
Import ListNotations.
Open Scope R_scope.

Module PolygonWindingAreaTraceCase.

Record Point : Type := mkPoint {
  phi : R;
  lambda : R
}.

Definition R_earth_default : R := 3440.065.
Definition R_earth : R := R_earth_default.

Definition hav (theta : R) : R := Rsqr (sin (theta / 2)).

Definition distance (p1 p2 : Point) : R :=
  let dphi := phi p2 - phi p1 in
  let dlambda := lambda p2 - lambda p1 in
  let a := hav dphi + cos (phi p1) * cos (phi p2) * hav dlambda in
  2 * R_earth * asin (sqrt a).

Definition Polygon : Type := list Point.

Definition nth_cyclic {A : Type} (default : A) (l : list A) (i : nat) : A :=
  nth (i mod length l) l default.

Definition lon_diff (lon1 lon2 : R) : R :=
  let raw := lon2 - lon1 in
  if Rlt_dec PI raw then raw - 2 * PI
  else if Rlt_dec raw (-PI) then raw + 2 * PI
  else raw.

Fixpoint spherical_shoelace_aux
    (pts : list Point)
    (all_pts : list Point)
    (idx : nat)
    : R :=
  match pts with
  | [] => 0
  | p :: rest =>
      let n := length all_pts in
      let lambda_prev := lambda (nth_cyclic p all_pts (idx + n - 1)) in
      let lambda_next := lambda (nth_cyclic p all_pts (idx + 1)) in
      let term := lon_diff lambda_prev lambda_next * sin (phi p) in
      term + spherical_shoelace_aux rest all_pts (idx + 1)
  end.

Definition spherical_shoelace (pts : list Point) : R :=
  spherical_shoelace_aux pts pts 0.

Definition spherical_polygon_area (poly : Polygon) : R :=
  Rabs (Rsqr R_earth * spherical_shoelace poly / 2).

Definition distance_to_central_angle (d : R) : R :=
  d / R_earth.

Definition spherical_cosine_arg (ca cb cab : R) : R :=
  let num := cos cab - cos ca * cos cb in
  let denom := sin ca * sin cb in
  Rmax (-1) (Rmin 1 (num / Rmax (Rabs denom) 1e-10)).

Definition law_of_cosines_arg (da db dab : R) : R :=
  let ca := distance_to_central_angle da in
  let cb := distance_to_central_angle db in
  let cab := distance_to_central_angle dab in
  spherical_cosine_arg ca cb cab.

Definition segment_angle (p a b : Point) : R :=
  let da := distance p a in
  let db := distance p b in
  let dab := distance a b in
  acos (law_of_cosines_arg da db dab).

Fixpoint winding_sum_aux (p : Point) (pts : list Point) (first : Point) : R :=
  match pts with
  | [] => 0
  | [a] => segment_angle p a first
  | a :: ((b :: _) as rest) => segment_angle p a b + winding_sum_aux p rest first
  end.

Definition winding_sum (p : Point) (poly : Polygon) : R :=
  match poly with
  | [] => 0
  | first :: _ => winding_sum_aux p poly first
  end.

Definition winding_number (p : Point) (poly : Polygon) : R :=
  winding_sum p poly / (2 * PI).

Definition inside_by_winding (p : Point) (poly : Polygon) : bool :=
  if Rlt_dec PI (winding_sum p poly)
  then true
  else false.

Definition nonnegative_area (poly : Polygon) : bool :=
  if Rle_dec 0 (spherical_polygon_area poly)
  then true
  else false.

Definition nonnegative_segment_angle (p a b : Point) : bool :=
  if Rle_dec 0 (segment_angle p a b)
  then true
  else false.

Definition winding_number_gt_half (p : Point) (poly : Polygon) : bool :=
  if Rlt_dec (1 / 2) (winding_number p poly)
  then true
  else false.

Definition test_triangle_v1 : Point := mkPoint 0 0.
Definition test_triangle_v2 : Point := mkPoint 1 0.
Definition test_triangle_v3 : Point := mkPoint (1 / 2) 1.

Definition test_triangle : Polygon :=
  [test_triangle_v1; test_triangle_v2; test_triangle_v3].

Definition test_centroid : Point := mkPoint (1 / 2) (1 / 3).
Definition test_exterior : Point := mkPoint (1 / 2) (-1).

Definition test_equatorial_square (delta : R) : Polygon :=
  [ mkPoint 0 0;
    mkPoint 0 delta;
    mkPoint delta delta;
    mkPoint delta 0 ].

Definition sample_square_delta : R := 1 / 10.

Definition sample_centroid_inside : bool :=
  inside_by_winding test_centroid test_triangle.

Definition sample_exterior_inside : bool :=
  inside_by_winding test_exterior test_triangle.

Definition sample_triangle_area_nonnegative : bool :=
  nonnegative_area test_triangle.

Definition sample_square_area_nonnegative : bool :=
  nonnegative_area (test_equatorial_square sample_square_delta).

Definition sample_first_angle_nonnegative : bool :=
  nonnegative_segment_angle test_centroid test_triangle_v1 test_triangle_v2.

Definition sample_centroid_winding_gt_half : bool :=
  winding_number_gt_half test_centroid test_triangle.

End PolygonWindingAreaTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "polygon_winding_area_trace" PolygonWindingAreaTraceCase.
