(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A tail-modulo-cons loop building cells of an inductive declared in
    another module, whose struct is not where that module's functions are.

    [Fin.of_nat_lt] builds [Fin.FS] around its recursive call.  [Fin.t]'s
    struct is put at file scope, as [T], beside the struct [Fin] holding
    [of_nat_lt]; the loop spelled a cell's constructor struct from the
    factory's qualifier, a value's spelling, as [typename Fin::T::FS], which
    names nothing. *)

From Stdlib Require Import Arith Lia Vectors.Fin.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Set Crane Loopify.

Module LoopifyTmcLibraryInductive.

Definition digit : Type := Fin.t 10.

Definition digit_of_nat (n : nat) (H : n < 10) : digit := Fin.of_nat_lt H.

Definition digit_to_nat (d : digit) : nat := proj1_sig (Fin.to_nat d).

Lemma lt_7_10 : 7 < 10. Proof. lia. Qed.

Definition seven : nat := digit_to_nat (digit_of_nat 7 lt_7_10).

End LoopifyTmcLibraryInductive.

Crane Extraction "loopify_tmc_library_inductive" LoopifyTmcLibraryInductive.
