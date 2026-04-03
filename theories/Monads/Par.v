(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Parallel computation effects using [std::async] / [std::future].

   Provides parallel effects ([parE]) as composable inductives with smart
   constructors and C++ extraction mappings. Use [itree parE A] (or any
   composed effect containing [parE]) as the monadic type.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.

Open Scope itree_scope.

Axiom future : Type -> Type.

#[universes(polymorphic)]
Inductive parE : Type -> Type :=
| MkThread : forall {A B}, (A -> B) -> A -> parE (future B)
| GetThread : forall {B}, future B -> parE B.

Crane Extract Skip parE.


Definition mk_thread {E} `{parE -< E} {A B} (f : A -> B) (a : A)
  : itree E (future B) := embed (MkThread f a).
Definition get_thread {E} `{parE -< E} {B} (t : future B)
  : itree E B := embed (GetThread t).

Crane Extract Inlined Constant future => "std::future<%t0>" From "future".
Crane Extract Inlined Constant mk_thread =>
  "std::async(std::launch::async, %a0, %a1)".
Crane Extract Inlined Constant get_thread => "%a0.get()".

Axiom runPar : forall {A}, itree parE A -> A.
Crane Extract Inlined Constant runPar => "%a0".
