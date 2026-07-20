(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression harness for the reified ITree runtime invariants
   ([theories/cpp/crane_itree.h]).  The Rocq side only needs to force the
   generated header to include <crane_itree.h>; the actual invariant checks
   (null continuations rejected, Ret re-runnable, run keeps its node alive)
   live in [itree_invariants.t.cpp], which drives the C++ runtime type
   directly. *)
From Stdlib Require Import Nat.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
Require Crane.Extraction.

Module IO_axioms.
  Axiom ioE : Type -> Type.
End IO_axioms.
Crane Extract Skip Module IO_axioms.
Export IO_axioms.

Module ItreeInvariants.

(** Emitted so the generated header includes <crane_itree.h>. *)
Fixpoint count_taus (fuel : nat) (t : itree ioE nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match observe t with
    | RetF _ => 0
    | TauF t' => S (count_taus fuel' t')
    | VisF _ _ => 0
    end
  end.

End ItreeInvariants.

Crane Extraction "itree_invariants" ItreeInvariants.
