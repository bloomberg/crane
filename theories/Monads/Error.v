(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Stdlib Require Import
  Strings.String
.

From Crane Require Import Monads.ITree Extraction.

From ITree Require Import
  Events.Exception
  ITree
.


(* An error type used for runtime errors. *)

Variant Err : Type :=
| Error (x : string) : Err.

Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).
