(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import NArith.
Open Scope nat_scope.

Module Type BaseType.
  Parameter t : Type.
End BaseType.

(* Module type defining ordered keys *)
Module Type OrderedType.
  Parameter t : Type.
  Parameter compare : t -> t -> comparison.
End OrderedType.

(* Module type for Maps *)
Module Type Map.
  Parameter key : Type.
  Parameter value : Type.
  Parameter t : Type.

  Parameter empty : t.
  Parameter add : key -> value -> t -> t.
  Parameter find : key -> t -> option value.
End Map.

(* Functor creating Maps from ordered keys *)
Module MakeMap (K : OrderedType) (V : BaseType) : Map
  with Definition key := K.t
  with Definition value := V.t.

  Definition key := K.t.
  Definition value := V.t.

  Inductive tree :=
  | Empty : tree
  | Node : tree -> key -> value -> tree -> tree.

  Definition t := tree.

  Definition empty := Empty.

  Fixpoint add (k : key) (v : value) (m : t) : t :=
    match m with
    | Empty => Node Empty k v Empty
    | Node l k' v' r =>
        match K.compare k k' with
        | Eq => Node l k v r
        | Lt => Node (add k v l) k' v' r
        | Gt => Node l k' v' (add k v r)
        end
    end.

  Fixpoint find (k : key) (m : t) : option value :=
    match m with
    | Empty => None
    | Node l k' v' r =>
        match K.compare k k' with
        | Eq => Some v'
        | Lt => find k l
        | Gt => find k r
        end
    end.

End MakeMap.

Module NatBase : BaseType
  with Definition t := nat.
  Definition t := nat.
End NatBase.

Module NatOrdered : OrderedType
  with Definition t := nat.
  Definition t := nat.
  Definition compare := Nat.compare.
End NatOrdered.

(* Concrete integer-to-integer map *)
Module NatMap := MakeMap NatOrdered NatBase.

(* Example usage *)
Definition mymap :=
  NatMap.add 1 10 (NatMap.add 2 20 (NatMap.add 3 30 NatMap.empty)).

Compute NatMap.find 2 mymap.   (* Should output Some 20 *)
Compute NatMap.find 4 mymap.   (* Should output None *)

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction TestCompile "module" mymap.
