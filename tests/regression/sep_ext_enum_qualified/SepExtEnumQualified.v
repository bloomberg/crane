(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction must fully qualify enum type names
   in switch case labels (e.g. Datatypes::Comparison::e_EQ, not
   Comparison::e_EQ). *)

Module Type OrderedType.
  Parameter t : Type.
  Parameter compare : t -> t -> comparison.
End OrderedType.

Module Make (X : OrderedType).

  Definition is_lt (a b : X.t) : bool :=
    match X.compare a b with
    | Lt => true
    | _ => false
    end.

  Definition is_eq (a b : X.t) : bool :=
    match X.compare a b with
    | Eq => true
    | _ => false
    end.

End Make.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction Make.
