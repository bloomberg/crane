(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared parallel computation effect definitions (flavor-independent).

   Contains the effect inductive ([parE]), axioms, and smart constructors
   that are identical across library flavors. Flavor files ([Par.v],
   [ParBDE.v]) re-export this module and add flavor-specific C++ extraction
   mappings.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

Axiom future : Type -> Type.

#[universes(polymorphic)]
Inductive parE : Type -> Type :=
| MkThread : forall {A B}, (A -> B) -> A -> parE (future B)
| GetThread : forall {B}, future B -> parE B.

Definition async {E} `{parE -< E} {A B} (f : A -> B) (a : A)
  : itree E (future B) := embed (MkThread f a).
Definition get_thread {E} `{parE -< E} {B} (t : future B)
  : itree E B := embed (GetThread t).

Crane Extract Inlined Constant get_thread => "%a0.get()".

Axiom runPar : forall {A}, itree parE A -> A.
Crane Extract Inlined Constant runPar => "%a0".
