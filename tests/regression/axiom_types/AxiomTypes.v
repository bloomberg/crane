(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test exercises axiom types and axiom values in extraction.
   Axioms are extracted as functions that throw std::logic_error when called.
   The C++ test verifies that calling axiom-dependent code throws catchable
   exceptions at runtime (not at static initialization time).
*)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module AxiomTypes.

(* Axiomatize types that will appear in extraction *)
Axiom MysteryType : Type.
Axiom mystery_value : MysteryType.
Axiom mystery_function : MysteryType -> MysteryType.

(* Functions that use axioms — these become callable C++ functions
   that throw when invoked, rather than crashing at static init *)
Definition use_axiom (u : unit) : MysteryType := mystery_function mystery_value.

(* Axiom in record *)
Record AxiomRecord := mkAxiomRecord {
  normal_field : nat;
  axiom_field : MysteryType
}.

Definition make_axiom_record (u : unit) : AxiomRecord :=
  mkAxiomRecord 42 mystery_value.

(* Match on axiom record *)
Definition extract_axiom_field (r : AxiomRecord) : MysteryType :=
  match r with
  | mkAxiomRecord _ ax => ax
  end.

(* Axiom in inductive *)
Inductive AxiomInductive : Type :=
| AxConstr1 : nat -> AxiomInductive
| AxConstr2 : MysteryType -> AxiomInductive.

Definition use_axiom_inductive (u : unit) : AxiomInductive :=
  AxConstr2 mystery_value.

(* Function taking and returning axiom types *)
Definition axiom_identity (x : MysteryType) : MysteryType := x.

(* Nested axioms — wrapped in a function *)
Definition nested_axiom (u : unit) : MysteryType :=
  axiom_identity (mystery_function (axiom_identity mystery_value)).

(* List of axiom types *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Definition axiom_list (u : unit) : list MysteryType :=
  cons mystery_value (cons (mystery_function mystery_value) nil).

(* Axiom in polymorphic context *)
Definition poly_axiom {A : Type} (x : A) : A := x.
Definition use_poly_axiom (u : unit) := poly_axiom mystery_value.

End AxiomTypes.

Crane Extraction "axiom_types" AxiomTypes.
