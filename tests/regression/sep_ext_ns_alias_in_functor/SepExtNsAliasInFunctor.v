From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Module Type S.
  Parameter t : Type.
End S.

Module Inner.
  Definition val_x := 0.
End Inner.

Module MyFunctor (X : S).
  Module R := Inner.
  Definition use_r := R.val_x.
End MyFunctor.

Crane Separate Extraction MyFunctor.
