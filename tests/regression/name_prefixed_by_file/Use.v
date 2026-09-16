From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.
From CraneTestsRegression Require name_prefixed_by_file.EOU.

Import MonadNotation.
Open Scope monad.

Module NamePrefixedByFile.
  Definition use (n : nat) : EOU.EOU nat :=
    x <- EOU.option_ub 0 (Some n) ;; ret (S x).
End NamePrefixedByFile.

Crane Extraction "name_prefixed_by_file" NamePrefixedByFile.
