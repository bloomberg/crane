(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a constructor named after a C or C++ standard macro breaks the
    generated header.  An enum-shaped inductive becomes an [enum class] whose
    enumerators are the constructors' names in upper case, and [NAN],
    [INFINITY], [EOF], [NULL] or [ERRNO]-like names are macros once
    [<cmath>], [<cstdio>] or [<cerrno>] is included, so the preprocessor
    rewrites the enumerator list into something that does not parse.  The
    keyword avoidance Crane applies to names does not cover macros.  Rocq's
    own [float_class] has a constructor [NaN], emitted as [NAN], so any use
    of [PrimFloat.classify] hits this too. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimFloat.
From Crane Require Import Mapping.Std.

Module MacroNamedConstructor.

Inductive num := NAN | INFINITY | EOF | NULL | errno.

Definition code (n : num) : nat :=
  match n with NAN => 1 | INFINITY => 2 | EOF => 3 | NULL => 4 | errno => 5 end.

Definition total : nat := code EOF + code errno.

(** The standard library's own [float_class] has a [NAN] constructor. *)
Definition is_normal (f : float) : bool :=
  match PrimFloat.classify f with FloatClass.PNormal => true | _ => false end.

Definition two_is_normal : bool := is_normal 2.5%float.

End MacroNamedConstructor.

Crane Extraction "macro_named_constructor" MacroNamedConstructor.
