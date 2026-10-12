(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module-level alias for a sum of Crane's own event types,
    [Definition bigE := ioE +' envE +' clockE], does not compile.  The event
    types print as nothing, so the alias over their sum is emitted as
    [using E = Sum1 << crane::obj >, ...>]: "use of class template 'Sum1'
    requires template arguments".  Crane's own tests of such sums declare
    [Crane Extract Skip] on the alias; Crane should skip or erase it
    itself. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO Monads.Env Monads.Clock.

Module EventSumAlias.

Open Scope itree_scope.
Open Scope pstring_scope.

Definition bigE := ioE +' envE +' clockE.

Definition go : itree ioE nat := Ret 3.

End EventSumAlias.

Crane Extraction "event_sum_alias" EventSumAlias.
