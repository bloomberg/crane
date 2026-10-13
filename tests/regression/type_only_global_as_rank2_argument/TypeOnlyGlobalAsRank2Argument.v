(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a global whose only binder is a type, passed for a rank-2
    argument [forall A, P A []], is called as a function.  [base (A : Type)
    : nat := 0] erases its binder and becomes the constant [static
    constexpr uint64_t base], but the adapter written for the argument is
    [[]() -> uint64_t { return base(); }]: "called object type 'uint64_t'
    is not a function or function pointer".  [step], which keeps value
    parameters, is adapted correctly. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TypeOnlyGlobalAsRank2Argument.

Definition grect (P : forall A : Type, list A -> Type) (f : forall A, P A [])
  (f0 : forall A x (t : list A), P A t -> P A (x :: t)) (A : Type) (l : list A) : P A l :=
  (fix F (B : Type) (m : list B) {struct m} : P B m :=
     match m with [] => f B | x :: t => f0 B x t (F B t) end) A l.

Definition step (A : Type) (x : A) (t : list A) (k : nat) : nat := S k.
Definition base (A : Type) : nat := 0.

Definition len (A : Type) (l : list A) : nat := grect (fun _ _ => nat) base step A l.

Definition result : nat := len bool [true; true].

End TypeOnlyGlobalAsRank2Argument.

Crane Extraction "type_only_global_as_rank2_argument" TypeOnlyGlobalAsRank2Argument.
