(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: inside a functor, a definition that produces a sigma type
   (existT / sigT) must be represented consistently in the C++ header
   and body.  Previously Crane emitted `std::any` for the type but
   generated accessor code that treats it as a std::pair field. *)

Module Type S.
  Parameter t : Type.
End S.

Module MyMod (X : S).
  (** existT gives a sigma type {A : Type & unit}; body accesses .projT1 / .projT2 *)
  Definition ex := existT (fun (_ : Type) => unit) X.t tt.
End MyMod.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction MyMod.
