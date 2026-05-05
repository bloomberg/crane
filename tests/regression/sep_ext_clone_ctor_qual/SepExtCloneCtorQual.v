(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: the unique-ptr pre-extraction binding for list tails inside
   a template functor must use the fully-qualified type name.  Previously,
   Crane emitted bare List<std::pair<t, T1>> deriving from the unique_ptr
   field instead of Datatypes::List<std::pair<typename X::t, T1>>. *)

From Stdlib Require Import List.

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

Module FMapList (X : OrderedType).

  (** The cons branch body is a value-capture lambda (fun _ => true).
      This triggers branch_needs_uptr_preextract for the list tail field,
      which was the code path that generated unqualified type names. *)
  Definition has_tail {T : Type} (l : list (X.t * T)) : T -> bool :=
    match l with
    | nil => fun _ => false
    | cons _ tl => fun _ => true
    end.

End FMapList.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction FMapList.
