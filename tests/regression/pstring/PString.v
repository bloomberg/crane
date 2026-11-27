(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Require Import PrimString.
From Stdlib Require Import Lists.List.
Import ListNotations.

Axiom int : Type.
Axiom zero : int.
Axiom one : int.
Axiom iplus : int -> int -> int.

Module PString.

Fixpoint nat_to_string (n : nat) : string :=
  match n with
  | O => "O"
  | S n' => cat "S" (nat_to_string n')
  end.

Fixpoint nat_to_int (n : nat) : int :=
  match n with
  | O => zero
  | S n' => iplus one (nat_to_int n')
  end.

Fixpoint list_to_string {A : Type} (p : A -> string) (l : list A) : string :=
  match l with
  | nil => "[]"
  | cons y l' => cat (cat (p y) "::") (list_to_string p l')
  end.

End PString.

Require Crane.Extraction.

Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance int_mapping : TypeMapping int :=
  value_type [] (Int I32) BitCopy.
#[global] Instance zero_mapping : OperationMapping (Ref (@zero)) :=
  pure_cpp [] []
    (Structured (Verbatim "0")).
#[global] Instance one_mapping : OperationMapping (Ref (@one)) :=
  pure_cpp [] []
    (Structured (Verbatim "1")).
#[global] Instance iplus_mapping : OperationMapping (Ref (@iplus)) :=
  pure_cpp [] ["x0"; "x1"]
    (Structured (Binop (Add Unchecked) (Arg "x0") (Arg "x1"))).

Require Import Crane.Mapping.Std.
Crane Extraction "pstring" PString.
