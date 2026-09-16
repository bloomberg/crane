From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require file_eponymous_with_alias.DList.

Module FileEponymousWithAlias.
  Definition use : list nat :=
    DList.DList_append DList.DList_empty DList.DList_empty (cons 1 nil).
End FileEponymousWithAlias.

Crane Extraction "file_eponymous_with_alias" FileEponymousWithAlias.
