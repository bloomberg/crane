(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module type declaring an inductive or a record with a type
    parameter becomes a concept no module can satisfy.  Each inductive in a
    module type becomes the requirement [typename M::tr;], but a
    parameterised inductive is a class template, which [typename M::tr]
    cannot name: "typename specifier refers to class template member".  So
    [Use<Impl>] fails its constraints, for [tr A] and for [box A] alike.
    Module types with unparameterised inductives work. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeParameterisedInductive.

Module Type T.
  Inductive tr (A : Type) := L | N : tr A -> A -> tr A -> tr A.
  Record box (A : Type) := { unbox : A }.
End T.

Module Impl <: T.
  Inductive tr (A : Type) := L | N : tr A -> A -> tr A -> tr A.
  Record box (A : Type) := { unbox : A }.
End Impl.

Module Use (X : T).
  Fixpoint size {A} (t : X.tr A) : nat :=
    match t with X.L _ => 0 | X.N _ l _ r => S (size l + size r) end.
  Definition get (b : X.box nat) : nat := S (X.unbox _ b).
End Use.

Module U := Use Impl.

Definition result : nat :=
  U.size (Impl.N nat (Impl.L nat) 1 (Impl.L nat)) + U.get {| Impl.unbox := 4 |}.

End ModuleTypeParameterisedInductive.

Crane Extraction "module_type_parameterised_inductive" ModuleTypeParameterisedInductive.
