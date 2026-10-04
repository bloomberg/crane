From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_mutual_template_order.Ty sep_ext_mutual_template_order.Tr.

Definition use_it (t : tree bool) : tree bool := tmap negb t.

Crane Separate Extraction use_it.
