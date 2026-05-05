(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: a module member whose type is Prop (e.g. `relation X.t`
   which unfolds to `X.t -> X.t -> Prop`) must be silently erased
   in the generated C++ header.  Previously Crane emitted an invalid
   `using relation_on_X = Relation_Definitions::...;` referencing a
   namespace that does not exist in the extracted output. *)

Require Import Coq.Relations.Relation_Definitions.

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

Module FMapList (X : OrderedType).
  (** relation X.t = X.t -> X.t -> Prop -- Prop-kinded, must be erased *)
  Definition relation_on_X := relation X.t.

  (** This non-Prop member must still be emitted. *)
  Definition eq_key (a b : X.t) : bool := true.
End FMapList.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction FMapList.
