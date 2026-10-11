(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a local fixpoint whose binders begin with a [let] that refers to
    the fixpoint itself, [fix F (h := H F) (l : list nat) := ...], is
    emitted as a fixpoint of no parameters returning a lambda, and names
    itself instead of its self parameter: "use of undeclared identifier
    'f'".  The pair it is packed into then does not convert either.  A
    top-level fixpoint with the same binder, and a [let] binder that does
    not mention the fixpoint, both work.  Equations generates this shape
    for the correctness lemma of mutual [where] clauses. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FixLetBinderSelfReference.

Definition both : (list nat -> nat) * (list nat -> nat).
Proof.
  pose (H := fun (g : list nat -> nat) (l : list nat) => g l + 1).
  pose (H0 := ltac:(fix F 1; pose (h := H F); intro l; destruct l as [|x t];
                    [exact 0 | exact (h t)]) : list nat -> nat).
  exact (H0, H H0).
Defined.

Definition result : nat := fst both [4; 5; 6] + snd both [1].

End FixLetBinderSelfReference.

Crane Extraction "fix_let_binder_self_reference" FixLetBinderSelfReference.
