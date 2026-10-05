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

Axiom vector : Type -> Type.

Inductive vectorE : Type -> Type :=
| EmptyVec : forall (A : Type), vectorE (vector A)
| Get : forall {A}, vector A -> int -> vectorE A
| Push : forall {A}, vector A -> A -> vectorE unit
| Pop : forall {A}, vector A -> vectorE unit
| Size : forall {A}, vector A -> vectorE int
| IsEmpty : forall {A}, vector A -> vectorE bool
| Assign : forall {A}, vector A -> int -> A -> vectorE (vector A).

Crane Extract Inductive vectorE => ""
  [ "{}" "%a0.at(%a1)" "%a0.push_back(%a1)"
    "%a0.pop_back()" "%a0.size()" "%a0.empty()" "%a0.assign(%a1, %a2)" ].

Definition emptyVec {E} `{vectorE -< E} (A : Type) : itree E (vector A) :=
  embed (EmptyVec A).
Definition get {E} `{vectorE -< E} {A} (v : vector A) (x : int) : itree E A :=
  embed (Get v x).
Definition push {E} `{vectorE -< E} {A} (v : vector A) (a : A) : itree E unit :=
  embed (Push v a).
Definition pop {E} `{vectorE -< E} {A} (v : vector A) : itree E unit :=
  embed (Pop v).
Definition size {E} `{vectorE -< E} {A} (v : vector A) : itree E int :=
  embed (Size v).
Definition isEmpty {E} `{vectorE -< E} {A} (v : vector A) : itree E bool :=
  embed (IsEmpty v).
Definition assign {E} `{vectorE -< E} {A} (v : vector A) (x : int) (a : A)
  : itree E (vector A) := embed (Assign v x a).

Crane Extract Inlined Constant emptyVec => "{}".
Crane Extract Inlined Constant get => "%a0.at(%a1)".
Crane Extract Inlined Constant push => "%a0.push_back(%a1)".
Crane Extract Inlined Constant pop => "%a0.pop_back()".
Crane Extract Inlined Constant size => "%a0.size()".
Crane Extract Inlined Constant isEmpty => "%a0.empty()".
Crane Extract Inlined Constant assign => "%a0.assign(%a1, %a2)".
