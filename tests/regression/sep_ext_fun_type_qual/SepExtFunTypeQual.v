(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: function-type arguments in concept requires-expressions must
   qualify module member types.  Previously, (elt -> bool) in a requires
   block rendered as std::function<bool(elt)> instead of
   std::function<bool(typename M::elt)>. *)

Module Type S.
  Parameter elt : Type.
  Parameter t : Type.
  Parameter for_all : (elt -> bool) -> t -> bool.
  Parameter exists_ : (elt -> bool) -> t -> bool.
  Parameter filter : (elt -> bool) -> t -> t.
End S.

Module MyModule (M : S).
  (** Trivial definition; only the generated concept for S matters here. *)
  Definition test (x : M.t) : M.t := x.
End MyModule.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction MyModule.
