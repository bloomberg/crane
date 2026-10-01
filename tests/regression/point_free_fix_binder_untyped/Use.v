From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import Denote.

#[global] Instance nat_params : Params := { base := nat ; base_default := 0 }.

#[global] Instance c1n : C1 nat := { c1 x := x }.
#[global] Instance c2n : C2 nat := { c2 x := x }.
#[global] Instance c3n : C3 nat := { c3 x := x }.
#[global] Instance c4n : C4 nat := { c4 x := x }.

Definition go (t : @tree nat_params) : option (@tree nat_params) := freeze t.

Crane Extraction "point_free_fix_binder_untyped" go.
