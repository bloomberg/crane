(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Known bug: a record field whose type is a function returning an alias
    of a function type, [nat -> pred nat], is the curried
    [crane::fn<pred<Nat>(Nat)>], but a record literal fills it with the
    two-argument lambda the term is written as, [[](const Nat &a, Nat b)],
    which converts only through the currying adapter [crane::fn] has when
    [CRANE_STRICT_ARITY] is off.  The same lambda passed to a parameter of
    that type is split into a lambda returning a lambda, as the slot's type
    says. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module RecordLiteralCodomainAlias.
  Definition pred (A : Type) : Type := A -> bool.

  Definition use (f : nat -> pred nat) : bool := f 1 2.
  Definition through_parameter : bool := use (fun a b => Nat.eqb (a + b) 3).

  Record holder := { staged : nat -> pred nat; tag : nat }.

  Definition h : holder := {| staged := fun a b => Nat.eqb (a + b) 3; tag := 0 |}.
  Definition through_field : bool := staged h 1 2.
End RecordLiteralCodomainAlias.

Crane Extraction "record_literal_codomain_alias" RecordLiteralCodomainAlias.
