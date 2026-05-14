(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: pattern matching on dependent types must emit exactly one
   typename keyword, not two. *)

From Stdlib Require Import List.
Import ListNotations.

Module DoubleTypename.

Module Type OrderedType.
  Parameter t : Type.
End OrderedType.

Module MakeMap (X : OrderedType).
  Inductive entry (A : Type) : Type :=
  | Entry : X.t -> A -> entry A.

  Definition keys {A : Type} (l : list (entry A)) : list X.t :=
    match l with
    | [] => []
    | Entry _ k _ :: _ => [k]
    end.
End MakeMap.

Module NatOrd <: OrderedType.
  Definition t := nat.
End NatOrd.

Module NatMap := MakeMap NatOrd.

Definition test : list nat :=
  NatMap.keys [NatMap.Entry nat 1 2].

End DoubleTypename.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "double_typename" DoubleTypename.
