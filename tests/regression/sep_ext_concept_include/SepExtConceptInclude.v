(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction must correctly render concept aliases
   and track include dependencies for concept base types. *)

Module Type BaseType.
  Parameter t : Type.
  Parameter default : t.
End BaseType.

(** DerivedType is a pure alias for BaseType.
    This triggers the concept alias path: concept DerivedType = BaseType<M>; *)
Module Type DerivedType := BaseType.

Module Use (X : DerivedType).
  Definition get_default : X.t := X.default.
End Use.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction Use.
