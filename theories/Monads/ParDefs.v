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
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** A handle on a value being computed in
    parallel; opaque in Rocq, a C++ future. *)
Axiom future : Type -> Type.

#[universes(polymorphic)]
(** Fork-join parallelism over pure functions. *)
Inductive parE : Type -> Type :=
(** Start computing [f a] in parallel. *)
| MkThread : forall {A B}, (A -> B) -> A -> parE (future B)
(** Wait for a future and take its value. *)
| GetThread : forall {B}, future B -> parE B.

(** Run [f a] on another thread, returning a handle on its result. *)
Definition async {E} `{parE -< E} {A B} (f : A -> B) (a : A)
  : itree E (future B) := embed (MkThread f a).
(** Block until [t] is done and return its value. *)
Definition get_thread {E} `{parE -< E} {B} (t : future B)
  : itree E B := embed (GetThread t).

(** [get_thread] is the future's [get]. *)
#[export] Instance get_thread_mapping : OperationMapping (Ref (@get_thread)) :=
  effect_cpp [] ["t"]
    (Structured (Method (Arg "t") "get" [])).

(** Run a parallel computation to its value;
    an axiom realized only by extraction. *)
Axiom run_par : forall {A}, itree parE A -> A.
(** [run_par] is the identity: an extracted
    [itree parE A] already computes its result. *)
#[export] Instance run_par_mapping : OperationMapping (Ref (@run_par)) :=
  pass_through [] "t" [].
