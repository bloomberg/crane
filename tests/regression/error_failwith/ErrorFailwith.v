(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Monads.Error.failwith] does not compile.  It is the
    interaction trees' [throw] over [exceptE], for which Crane has no
    mapping, and the generated code is a call with no callee:
    [return <T2, T3, T3>(ExceptE<T1>::Throw_(e), ...)] -- "expected
    expression".  Crane ships [failwith], and nothing exercises it. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO Monads.Env Monads.Error.
From ITree Require Import Events.Exception.

Module ErrorFailwith.

Open Scope itree_scope.
Open Scope pstring_scope.

Definition safe_div (a b : nat) : itree (exceptE Err +' ioE) nat :=
  if Nat.eqb b 0 then failwith "div by zero" else Ret (Nat.div a b).

Definition result := safe_div 10 2.

End ErrorFailwith.

Crane Extraction "error_failwith" ErrorFailwith.
