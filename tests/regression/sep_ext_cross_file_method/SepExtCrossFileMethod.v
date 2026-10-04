From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_cross_file_method.Num.
From CraneTestsRegression Require Import sep_ext_cross_file_method.NumDec.

Definition use_it : bool := num_le_two (Succ Zero).

Crane Separate Extraction use_it.
