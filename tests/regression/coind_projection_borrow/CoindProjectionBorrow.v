(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A coinductive's field projections are split by [Borrow_projection]: an
    lvalue receiver gets a reference into the receiver, a temporary one gets
    a copy, so no projection of a call's result dangles.  The projections are
    methods because [Stream] is eponymous with [stream].

    Streams are only consumed here; the test driver builds them.  Producing
    one in this layout meets one of two unrelated bugs, recorded as
    [tests/wip/cofix_nested_eponymous_undefined] and
    [tests/wip/cofix_ctor_outside_eponymous]. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module CoindProjectionBorrow.

Module Stream.

CoInductive stream : Type :=
| scons : nat -> stream -> stream.

Definition hd (s : stream) : nat := match s with scons x _ => x end.

Definition tl (s : stream) : stream := match s with scons _ t => t end.

End Stream.

Import Stream.

(** A stream returned by value: a call to it is a temporary receiver. *)
Definition skip2 (s : stream) : stream := tl (tl s).

(** Projections whose receivers are temporaries. *)
Definition third (s : stream) : nat := hd (skip2 s).

(** Projections whose receiver is a parameter, an lvalue. *)
Definition sum_two (s : stream) : nat := hd s + hd (tl s).

End CoindProjectionBorrow.

Crane Extraction "coind_projection_borrow" CoindProjectionBorrow.
