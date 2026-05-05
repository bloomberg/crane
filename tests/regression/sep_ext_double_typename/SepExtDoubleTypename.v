(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: separate extraction must emit exactly one typename for
   nested dependent types like Datatypes::List<pair<typename X::t, T1>>::Nil *)

From Stdlib Require Import List.
Import ListNotations.

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

Module FMapList (X : OrderedType).

  Definition is_empty {A : Type} (l : list (X.t * A)) : bool :=
    match l with
    | [] => true
    | _ => false
    end.

  Definition head_key {A : Type} (l : list (X.t * A)) : option X.t :=
    match l with
    | (k, _) :: _ => Some k
    | [] => None
    end.

End FMapList.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Separate Extraction FMapList.
