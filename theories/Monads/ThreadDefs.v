(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared thread effect definitions (flavor-independent).

   Contains the [thread] axiom, the [threadE] effect inductive, the
   composed effect [concE], and smart constructors that are identical
   across library flavors. Flavor files ([Thread.v], [ThreadBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.

   [spawn] remains an axiom because its higher-order argument [(A -> B)]
   cannot satisfy universe constraints when [B] is an [itree] type.
*)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** A handle on a running thread; opaque in Rocq, a C++ thread or future. *)
Axiom thread : Type.

(** Thread control: waiting on a thread and pausing the current one. *)
Inductive threadE : Type -> Type :=
(** Wait until the thread has finished. *)
| Join : thread -> threadE unit
(** Pause the current thread for the given number of milliseconds. *)
| Sleep : int -> threadE unit.

(** Concurrent programs: threads plus console
    IO. Only a Rocq abbreviation, never emitted. *)
Definition concE := threadE +' consoleE.
Crane Extract Skip concE.

(** Start computing [f a] on a new thread, discarding its result. *)
Axiom spawn : forall {E} `{threadE -< E} {A B},
  (A -> B) -> A -> itree E thread.
(** Wait for [t] to finish. *)
Definition join {E} `{threadE -< E} (t : thread) : itree E unit :=
  embed (Join t).
(** Pause for [d] milliseconds. *)
Definition sleep {E} `{threadE -< E} (d : int) : itree E unit :=
  embed (Sleep d).

(** Run a concurrent program to its value; an axiom realized only by extraction. *)
Axiom run_conc : forall {A}, itree concE A -> A.
(** [run_conc] is the identity: an extracted
    [itree concE A] already computes its result. *)
#[export] Instance run_conc_mapping : OperationMapping (Ref (@run_conc)) :=
  pass_through [] "t" [].
