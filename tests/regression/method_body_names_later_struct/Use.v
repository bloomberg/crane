From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import method_body_names_later_struct.A.
From CraneTestsRegression Require Import method_body_names_later_struct.Arith.
From CraneTestsRegression Require Import method_body_names_later_struct.ZedDec.

Definition le (x y : zed) : bool := le_dec x y.

Definition round (x : zed) : zed := roundtrip x.

Crane Extraction "method_body_names_later_struct" le round.
