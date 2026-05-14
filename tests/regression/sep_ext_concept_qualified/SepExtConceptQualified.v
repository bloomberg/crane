(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction must qualify concept references
   from different namespaces and self-qualify top-level concepts.
   Bug 1: cross-namespace concept alias must be namespace-qualified.
   Bug 2: top-level concept used as constraint needs self-qualification. *)

Module Type OrderedType.
  Parameter t : Type.
  Parameter compare : t -> t -> comparison.
End OrderedType.

Module Type DecidableType <: OrderedType.
  Parameter t : Type.
  Parameter compare : t -> t -> comparison.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End DecidableType.

Module Make (X : OrderedType).
  Definition is_eq (a b : X.t) : bool :=
    match X.compare a b with
    | Eq => true
    | _ => false
    end.
End Make.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction Make.
