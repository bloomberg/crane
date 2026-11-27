(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test exposes the known issue mentioned in CLAUDE.md:
   "Missing typename keywords"

   Dependent type references like K::t need typename K::t in C++
   when K is a template parameter.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module DependentTypename.

(* A module type with a type member *)
Module Type HasType.
  Parameter t : Type.
  Parameter default : t.
End HasType.

(* A functor that uses the type from its parameter *)
Module UsesType (M : HasType).
  (* This should generate code that references M::t
     If M is a template parameter (concept), this needs typename M::t *)
  Definition get_default : M.t := M.default.

  Definition identity (x : M.t) : M.t := x.

  (* Function that returns the type from the module *)
  Definition make_default : M.t := M.default.
End UsesType.

(* An implementation of HasType *)
Module NatType <: HasType.
  Definition t := nat.
  Definition default : t := 42.
End NatType.

(* Apply the functor *)
Module NatUser := UsesType NatType.

Definition test := NatUser.get_default.

(* Another variant: nested dependent types *)
Module Type Container.
  Parameter t : Type -> Type.
  Parameter empty : forall A : Type, t A.
  Parameter singleton : forall A : Type, A -> t A.
End Container.

Module UseContainer (C : Container).
  (* C::t<nat> needs typename when C is a concept *)
  Definition make_nat_container : C.t nat := C.empty nat.

  Definition use_singleton (x : nat) : C.t nat := C.singleton nat x.
End UseContainer.

End DependentTypename.

Crane Extraction "dependent_typename" DependentTypename.
