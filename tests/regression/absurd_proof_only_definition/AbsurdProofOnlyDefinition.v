(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a definition whose only arguments are proofs and whose body is
    absurd is declared as a function and used as a value.  [absurd_nat (H :
    0 = 1) : nat := False_rect _ ...] is declared [static uint64_t
    absurd_nat();] -- a body that throws keeps a nullary function -- but
    its use, with the proof argument erased, names it as a constant:
    "incompatible operand types ('uint64_t (*)()' and 'unsigned long
    long')", and for a [list] result, "base of member reference is a
    function".  A proof-only definition with an ordinary body becomes a
    constant and works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module AbsurdProofOnlyDefinition.

Definition absurd_nat (H : 0 = 1) : nat := False_rect _ (O_S 0 H).

Definition r1 : nat := match Nat.eq_dec 0 1 with left h => absurd_nat h | right _ => 9 end.

Definition absurd_list (H : 0 = 1) : list nat := False_rect _ (O_S 0 H).

Definition r2 : nat :=
  match Nat.eq_dec 0 1 with left h => List.length (absurd_list h) | right _ => 9 end.

End AbsurdProofOnlyDefinition.

Crane Extraction "absurd_proof_only_definition" AbsurdProofOnlyDefinition.
