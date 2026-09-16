From Crane Require Extraction.
From CraneTestsWIP Require cross_file_module_ref.Lib.

Module Type S.
  Parameter t : Set.
  Parameter zero : t.
End S.

Module F (X : S).
  Definition twice (f : X.t -> X.t) : X.t := f (f X.zero).
End F.

Module M := F Lib.Ord.
