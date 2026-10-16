(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [CoFixpoint] declared outside a nested module eponymous with its
    coinductive spells the constructor's struct as a member of the type,
    [Stream::stream::Scons].  A nested module is not promoted to its
    inductive; the implementation once counted it promoted, having no struct
    around it, and every reference spelled [CoindProjectionBorrow::Stream::Scons],
    which names nothing. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module CofixCtorOutsideEponymous.

Module Stream.

CoInductive stream : Type :=
| scons : nat -> stream -> stream.

Definition hd (s : stream) : nat := match s with scons x _ => x end.

Definition tl (s : stream) : stream := match s with scons _ t => t end.

End Stream.

Import Stream.

CoFixpoint from (n : nat) : stream := scons n (from (S n)).

Definition third_of (n : nat) : nat := hd (tl (tl (from n))).

End CofixCtorOutsideEponymous.

Crane Extraction "cofix_ctor_outside_eponymous" CofixCtorOutsideEponymous.
