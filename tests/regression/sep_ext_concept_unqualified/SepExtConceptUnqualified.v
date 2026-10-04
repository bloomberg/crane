From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_concept_unqualified.ParamsDef.

Definition use_it `{Params} (x : prov) : prov := x.

Crane Separate Extraction use_it.
