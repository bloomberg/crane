(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared vector effect definitions (flavor-independent).

   Contains the [vector] axiom, [vectorE] inductive, and polymorphic smart
   constructors that are identical across library flavors. Flavor files
   ([Vector.v], [VectorBDE.v]) re-export this module and add
   flavor-specific C++ extraction mappings for the [vector] type.
*)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** A mutable, growable array, changed in place through [vectorE] events. *)
Axiom vector : Type -> Type.

(** The vector events, each indexed by its result type.  [Get] is
    bounds-checked; [Assign v n a] makes [v] [n] copies of [a]. *)
Inductive vectorE : Type -> Type :=
| EmptyVec : forall (A : Type), vectorE (vector A)
| Get : forall {A}, vector A -> int -> vectorE A
| Push : forall {A}, vector A -> A -> vectorE unit
| Pop : forall {A}, vector A -> vectorE unit
| Size : forall {A}, vector A -> vectorE int
| IsEmpty : forall {A}, vector A -> vectorE bool
| Assign : forall {A}, vector A -> int -> A -> vectorE (vector A).

(** Each event is the member call on its vector: [Get] is [at], which
    throws out of range, and [Assign] is [assign(n, a)]. *)
#[export] Instance vectorE_mapping (T : Type) : TypeMapping (vectorE T) :=
  event_family []
    [event (Ref (@EmptyVec)) "{}"; event (Ref (@Get)) "%a0.at(%a1)"; event (Ref (@Push)) "%a0.push_back(%a1)";
     event (Ref (@Pop)) "%a0.pop_back()"; event (Ref (@Size)) "%a0.size()"; event (Ref (@IsEmpty)) "%a0.empty()";
     event (Ref (@Assign)) "%a0.assign(%a1, %a2)"].

(** A fresh empty vector of [A]. *)
Definition empty_vector {E} `{vectorE -< E} (A : Type) : itree E (vector A) :=
  embed (EmptyVec A).
(** The element at index [x]. *)
Definition get {E} `{vectorE -< E} {A} (v : vector A) (x : int) : itree E A :=
  embed (Get v x).
(** Append [a]. *)
Definition push {E} `{vectorE -< E} {A} (v : vector A) (a : A) : itree E unit :=
  embed (Push v a).
(** Remove the last element. *)
Definition pop {E} `{vectorE -< E} {A} (v : vector A) : itree E unit :=
  embed (Pop v).
(** The number of elements. *)
Definition size {E} `{vectorE -< E} {A} (v : vector A) : itree E int :=
  embed (Size v).
(** Whether there are no elements. *)
Definition is_empty {E} `{vectorE -< E} {A} (v : vector A) : itree E bool :=
  embed (IsEmpty v).
(** Replace the contents with [x] copies of [a]. *)
Definition assign {E} `{vectorE -< E} {A} (v : vector A) (x : int) (a : A)
  : itree E (vector A) := embed (Assign v x a).

(** [empty_vector] is [{}], a value-initialised vector. *)
#[export] Instance empty_vector_mapping : OperationMapping (Ref (@empty_vector)) :=
  effect_cpp [] [] (Structured (Verbatim "{}")).
(** [get v x] is [v.at(x)], which throws [std::out_of_range] out of
    range. *)
#[export] Instance get_mapping : OperationMapping (Ref (@get)) :=
  effect_cpp [] ["v"; "x"] (Structured (Method (Arg "v") "at" [Arg "x"])).
(** [push v a] is [v.push_back(a)], taking [a]. *)
#[export] Instance push_mapping : OperationMapping (Ref (@push)) :=
  effect_args [] (uses ReadCanonical ["v"] ++ uses Take ["a"]) (Structured (Method (Arg "v") "push_back" [Arg "a"])).
(** [pop v] is [v.pop_back()], undefined on an empty vector. *)
#[export] Instance pop_mapping : OperationMapping (Ref (@pop)) :=
  effect_cpp [] ["v"] (Structured (Method (Arg "v") "pop_back" [])).
(** [size v] is [v.size()]. *)
#[export] Instance size_mapping : OperationMapping (Ref (@size)) :=
  effect_cpp [] ["v"] (Structured (Method (Arg "v") "size" [])).
(** [is_empty v] is [v.empty()]. *)
#[export] Instance is_empty_mapping : OperationMapping (Ref (@is_empty)) :=
  effect_cpp [] ["v"] (Structured (Method (Arg "v") "empty" [])).
(** [assign v x a] is [v.assign(x, a)], taking [a]. *)
#[export] Instance assign_mapping : OperationMapping (Ref (@assign)) :=
  effect_args [] (uses ReadCanonical ["v"; "x"] ++ uses Take ["a"]) (Structured (Method (Arg "v") "assign" [Arg "x"; Arg "a"])).
