(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a polymorphic global used as a value at a function type is
    eta-expanded to the arity of its instantiated type rather than its own.
    [idf {A} : A -> A] passed to [List.map] over [[S; pred]] is
    [A := nat -> nat], whose type [(nat -> nat) -> nat -> nat] has two
    arrows, and is wrapped as [[](_ec0, _ec1) { return
    idf<crane::fn<uint64_t(uint64_t)>>(_ec0, _ec1); }]: [idf] takes one
    argument ("requires single argument 'x', but 2 arguments were
    provided").  It has to be [idf<...>(_ec0)(_ec1)], or not expanded past
    its declared parameters.  [constf {A B} : A -> B -> A] at [B := bool]
    is the same.  Calling [idf S 3] directly works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module PolymorphicValueEtaArity.

Definition idf {A} : A -> A := fun x => x.
Definition fs := List.map idf [S; pred].
Definition through_idf : nat := fold_left (fun a g => g a) fs 5.

Definition constf {A B} : A -> B -> A := fun a _ => a.
Definition cs : list (bool -> nat) := List.map constf [1; 2].
Definition through_constf : nat := fold_left (fun a g => a + g true) cs 0.

End PolymorphicValueEtaArity.

Crane Extraction "polymorphic_value_eta_arity" PolymorphicValueEtaArity.
