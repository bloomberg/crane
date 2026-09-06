(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A parameterised typeclass instance reached through a generic function.
    The instance is passed as a dictionary, but is emitted as a template
    instantiation in expression position, which is not an expression. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module MonoidClassArg.
Class Monoid (A : Type) := { unit_ : A ; op : A -> A -> A }.
Instance MNat : Monoid nat := { unit_ := 0 ; op := Nat.add }.
Instance MList (A : Type) : Monoid (list A) := { unit_ := [] ; op := @app A }.
Instance MPair (A B : Type) (MA : Monoid A) (MB : Monoid B) : Monoid (A * B) :=
  { unit_ := (unit_, unit_) ; op := fun p q => (op (fst p) (fst q), op (snd p) (snd q)) }.
Definition mconcat {A} `{Monoid A} (l : list A) : A := fold_right op unit_ l.
Definition run : nat :=
  mconcat [1;2;3] + length (mconcat [[1];[2;3]]) + fst (mconcat [(1,[1]);(2,[2])]).
End MonoidClassArg.

Crane Extraction "monoid_class_arg" MonoidClassArg.run.
