(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction must qualify inductive names and
   dependent type arguments in object-construction positions. *)

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

(** Simple self-recursive list inductive — generates unique_ptr<MyList<A>> tails *)
Inductive MyList (A : Type) :=
  | mynil  : MyList A
  | mycons : A -> MyList A -> MyList A.

Module FMap (X : OrderedType).

  (** tail: extracts the unique_ptr tail field, triggering the clone expression *)
  Definition tail {T : Type} (l : MyList (X.t * T)) : MyList (X.t * T) :=
    match l with
    | mynil _       => mynil _
    | mycons _ _ t  => t
    end.

End FMap.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction MyList FMap.
