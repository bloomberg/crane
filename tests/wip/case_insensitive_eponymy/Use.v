From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From CraneTestsWIP Require case_insensitive_eponymy.CFG.
From CraneTestsWIP Require case_insensitive_eponymy.Other.

Module CaseInsensitiveEponymy.
  Definition use (g : CFG.cfg nat) : nat := Other.size (CFG.size g).
End CaseInsensitiveEponymy.

Crane Extraction "case_insensitive_eponymy" CaseInsensitiveEponymy.
