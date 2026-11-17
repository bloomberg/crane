(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: matching on an [option] that is a field of a call's result,
    [match sub (mk n) with Some l => ...], evaluates the call twice and binds
    the payload by reference into a temporary.  The [std::optional] mapping
    of [Mapping.Std] names its scrutinee twice -- [if (%scrut.has_value())
    { const T& x = *%scrut; ... }] -- and Crane copies a scrutinee into a
    local [_cs] first only when it is a call.  A field read off a call is
    treated as cheap, so the generated code is
    [if (mk(n).sub.has_value()) { const List<uint64_t> &l = *mk(n).sub; ...]
    and [l] refers into a [box] destroyed at the end of that statement.
    Clang rejects it ([-Wdangling-gsl] under [-Werror]); without the warning
    it is a heap use-after-free.  A bare call and a user inductive's field
    read off a call are both handled. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.

Module OptionFieldOfCallScrutinee.

Record box := { sub : option (list nat) }.

Definition mk (n : nat) : box := {| sub := Some (seq 0 n) |}.

Definition count (n : nat) : nat :=
  match sub (mk n) with Some l => List.length l | None => 0 end.

Definition result : nat := count 5.

End OptionFieldOfCallScrutinee.

Crane Extraction "option_field_of_call_scrutinee" OptionFieldOfCallScrutinee.
