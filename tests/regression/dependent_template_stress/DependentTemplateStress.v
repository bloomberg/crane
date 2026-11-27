(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   More aggressive test for missing typename/template keywords.
   Creates deeply nested dependent template names and multiple levels
   of template parameters.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module DependentTemplateStress.

(* Module type with multiple type members *)
Module Type Container.
  Parameter t : Type -> Type.
  Parameter inner : Type -> Type.
  Parameter elem : Type.
  Parameter empty : forall A : Type, t A.
  Parameter singleton : forall A : Type, A -> t A.
  Parameter wrap : forall A : Type, A -> inner A.
End Container.

(* Module type with nested type dependencies *)
Module Type NestedContainer.
  Parameter outer : Type -> Type.
  Parameter middle : Type -> Type.
  Parameter inner : Type -> Type.
  Parameter mk_outer : forall A : Type, middle A -> outer A.
  Parameter mk_middle : forall A : Type, inner A -> middle A.
  Parameter mk_inner : forall A : Type, A -> inner A.
End NestedContainer.

(* Functor using multiple dependent types from its parameter *)
Module UseContainer (C : Container).
  (* Each of these should need typename C::template t<...> *)
  Definition make_nat_container : C.t nat := C.empty nat.
  Definition make_inner_nat : C.inner nat := C.wrap nat 0.
  Definition make_bool_container : C.t bool := C.empty bool.

  (* Nested template application *)
  Definition use_both : C.t nat := C.singleton nat 42.

  (* Multiple template arguments *)
  Definition complex_use (x : nat) : C.t nat := C.singleton nat x.
End UseContainer.

(* Functor with nested dependent templates *)
Module UseNested (N : NestedContainer).
  Definition make_outer_nat : N.outer nat :=
    N.mk_outer nat (N.mk_middle nat (N.mk_inner nat 0)).

  Definition make_middle_bool : N.middle bool :=
    N.mk_middle bool (N.mk_inner bool true).

  (* This creates: N::template outer<nat> *)
  Definition get_outer : N.outer nat := make_outer_nat.
End UseNested.

(* Functor composition *)
Module Compose (C1 : Container) (C2 : Container).
  (* Multiple dependent type references in one module *)
  Definition use_c1 : C1.t nat := C1.empty nat.
  Definition use_c2 : C2.t bool := C2.empty bool.
  Definition use_c1_inner : C1.inner nat := C1.wrap nat 0.
  Definition use_c2_inner : C2.inner bool := C2.wrap bool true.
End Compose.

End DependentTemplateStress.

Crane Extraction "dependent_template_stress" DependentTemplateStress.
