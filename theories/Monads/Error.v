(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Runtime errors: the [Err] exception type and [failwith], which
    throws it in an [itree] and extracts to a thrown [std::runtime_error]. *)

From Stdlib Require Import
  PrimString
.

From Crane Require Import Monads.ITree Extraction.

From ITree Require Import
  Events.Exception
  ITree
.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.


(** The payload of a runtime failure: its message. *)
Variant Err : Type :=
| Error (x : string) : Err.

(** Fail with message [s], as a [Throw] of [exceptE Err]. *)
Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).

(** An erased tree performs its events where it is built, and nothing handles
   a [Throw] there: [failwith s] raises [s] as a C++ exception, at the type its
   call yields. *)
#[export] Instance failwith_mapping : OperationMapping (Ref (@failwith)) :=
  effect_cpp ["stdexcept"] ["s"]
    (Expr "[&]() -> %ret { throw std::runtime_error(%arg(s)); }()").
