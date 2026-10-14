(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** BUG: a [CoFixpoint] inside a nested module eponymous with its coinductive
    is declared in the header, [static stream from(uint64_t n);] inside
    [struct Stream], and defined nowhere, so every use fails to link.  The
    sibling functions [hd] and [tl], which become methods of [stream], are
    written correctly. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module CofixNestedEponymousUndefined.

Module Stream.

CoInductive stream : Type :=
| scons : nat -> stream -> stream.

Definition hd (s : stream) : nat := match s with scons x _ => x end.

Definition tl (s : stream) : stream := match s with scons _ t => t end.

CoFixpoint from (n : nat) : stream := scons n (from (S n)).

End Stream.

Import Stream.

Definition third_of (n : nat) : nat := hd (tl (tl (from n))).

End CofixNestedEponymousUndefined.

Crane Extraction "cofix_nested_eponymous_undefined" CofixNestedEponymousUndefined.
