(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module type that mentions a record declared in the same
    extracted module produces a concept and a struct that need each other.
    The concept [T] mentions the module's own [ops], so it is emitted
    after the module's struct, but the functor [Use], a member template of
    that struct, is declared as [template <T X> struct Use] and needs the
    concept first: "unknown type name 'T'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeMentionsOuterRecord.

Record ops (A : Type) := { plus : A -> A -> A; zero : A }.

Module Type T. Parameter t : Type. Parameter o : ops t. End T.

Module NatT <: T.
  Definition t := nat.
  Definition o : ops nat := {| plus := Nat.add; zero := 0 |}.
End NatT.

Module Use (X : T).
  Definition sum (l : list X.t) : X.t := fold_left (plus _ X.o) l (zero _ X.o).
End Use.

Module U := Use NatT.

Definition result : nat := U.sum [1; 2; 3].

End ModuleTypeMentionsOuterRecord.

Crane Extraction "module_type_mentions_outer_record" ModuleTypeMentionsOuterRecord.
