From Crane Require Import Mapping.Std.
From CraneTestsWIP Require Import method_body_names_later_struct.A.
From CraneTestsWIP Require Import method_body_names_later_struct.Arith.
From CraneTestsWIP Require Import method_body_names_later_struct.ZedDec.

Definition le (x y : zed) : bool := le_dec x y.

Definition round (x : zed) : zed := roundtrip x.

Crane Extraction "method_body_names_later_struct" le round.
