(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: render_cpp_type_simple must handle Tqualified types so that
   raw string rendering (for clone/converting constructors) produces
   fully qualified names like "typename X::t" instead of bare "t". *)

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

Module Make (X : OrderedType).

  Inductive fmap (A : Type) : Type :=
    | Empty : fmap A
    | Node : X.t -> A -> fmap A -> fmap A.

  Definition is_empty {A : Type} (m : fmap A) : bool :=
    match m with
    | Empty _ => true
    | Node _ _ _ _ => false
    end.

End Make.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Separate Extraction Make.
