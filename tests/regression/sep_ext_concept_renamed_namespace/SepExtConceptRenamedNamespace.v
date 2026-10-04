From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_concept_renamed_namespace.Foo.

Definition use_it `{Foo} : nat := foo_val.

Crane Separate Extraction use_it.
