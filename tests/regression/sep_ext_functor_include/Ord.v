From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module Type Ordered.
  Parameter t : Type.
  Parameter leb : t -> t -> bool.
End Ordered.

Module Full (O : Ordered).
  Definition t := O.t.
  Definition geb (x y : t) : bool := O.leb y x.
End Full.
