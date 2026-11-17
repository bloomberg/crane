From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module Type Base.
  Parameter t : Type.
End Base.

Module F (X : Base).
  Module Type S.
    Parameter u : Type.
    Parameter f : u -> X.t.
  End S.
  Module Use (Y : S).
    Definition g (y : Y.u) : X.t := Y.f y.
  End Use.
End F.
