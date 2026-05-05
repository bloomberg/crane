(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: using a method-ified stdlib function (List.length) as a
   higher-order argument inside a free function template must generate
   a lambda wrapper `[](const auto &_x) { return _x.length(); }`, not
   an invalid `this->length()` reference. *)

From Stdlib Require Import List.

Module Type S.
  Parameter t : Type.
End S.

Module FreeFn (X : S).
  (** List.length is method-ified; used here as a HOF arg in a free fn *)
  Definition map_lengths {A : Type} (xss : list (list A)) : list nat :=
    List.map (@List.length A) xss.
End FreeFn.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction FreeFn.
