From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import promoted_alias_out_of_line.Defs.
From CraneTestsRegression Require promoted_alias_out_of_line.F.
From CraneTestsRegression Require promoted_alias_out_of_line.Other.

Module PromotedAliasOutOfLine.
  Definition use : nat := Other.size (F.size 0) + F.lst tt nil.
End PromotedAliasOutOfLine.

Crane Extraction "promoted_alias_out_of_line" PromotedAliasOutOfLine.
