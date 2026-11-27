(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import
  Program.Wf.

Module Nat.

  Axiom int : Type.
  Axiom zero : int.
  Axiom one : int.
  Axiom positive : int -> bool.
  Axiom iplus : int -> int -> int.
  Axiom iminus : int -> int -> int.

  Inductive nat : Type :=
  | O : nat
  | S (n : nat) : nat.

  Fixpoint add (m : nat) (n : nat) : nat :=
    match m with
    | O => n
    | S x => S (add x n)
    end.

  Fixpoint nat_to_int (n : nat) : int :=
    match n with
    | O => zero
    | S n' => iplus one (nat_to_int n')
    end.

(*
  Axiom fuel : int -> Datatypes.nat.
  Axiom good_fuel1 : forall x, (forall x0 : int, fuel x0 < fuel x -> nat) -> fuel (iminus x one) < fuel x.
  Axiom good_fuel2 : well_founded (MR lt (fun x : int => fuel x)).

  Program Fixpoint int_to_nat (x : int)
    { measure (fuel x) } : nat :=
    if negb (positive x) then
      O
    else
      S (int_to_nat (iminus x one)).
  Next Obligation.
  Proof.
    apply good_fuel1; assumption.
  Qed.
  Next Obligation.
  Proof.
    apply good_fuel2.
  Qed.
*)

End Nat.

Require Crane.Extraction.
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Require Import Crane.Mapping.BDE.


Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance int_mapping : TypeMapping Nat.int :=
  value_type [] (Int I32) BitCopy.
#[global] Instance zero_mapping : OperationMapping (Ref (@Nat.zero)) :=
  pure_cpp [] []
    (Structured (Verbatim "0")).
#[global] Instance one_mapping : OperationMapping (Ref (@Nat.one)) :=
  pure_cpp [] []
    (Structured (Verbatim "1")).
#[global] Instance iplus_mapping : OperationMapping (Ref (@Nat.iplus)) :=
  pure_cpp [] ["x0"; "x1"]
    (Structured (Binop (Add Unchecked) (Arg "x0") (Arg "x1"))).
#[global] Instance iminus_mapping : OperationMapping (Ref (@Nat.iminus)) :=
  pure_cpp [] ["x0"; "x1"]
    (Structured (Binop (Sub Unchecked) (Arg "x0") (Arg "x1"))).
#[global] Instance positive_mapping : OperationMapping (Ref (@Nat.positive)) :=
  pure_cpp [] ["x0"]
    (Structured (Binop Greater (Arg "x0") (Verbatim "0"))).


Set Crane BDE Directory "~/bde_install/".
Crane Extraction "nat_bde" Nat.
