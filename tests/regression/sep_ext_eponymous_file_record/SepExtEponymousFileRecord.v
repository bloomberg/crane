From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_eponymous_file_record.CFG.

Definition use_it (c : cfg bool) : bool * bool := first_twice c.

Crane Separate Extraction use_it.
