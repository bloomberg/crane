(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an absurd case under a lambda whose binder is a proof is given
    the erased type rather than the type its position needs.  [app]'s
    result family [B : p = q -> Type] ranges over proofs; called at [fun _
    => nat] with [fun _ => False_rect nat (H eq_refl)], the absurd branch is
    [([]() -> crane::obj { throw ...; })()], while [app]'s parameter, at
    [T1 = uint64_t], is a function to [uint64_t]: "no matching function
    for call to 'app'".  A family over values is instantiated at its body
    ([regression/type_family_constant_motive]); one over proofs is not.
    This is the shape of [NoConfusion.apply_noConfusion], which every
    Equations dependent match on vectors goes through. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module AbsurdUnderProofBinder.

Definition app (p q : nat) {B : p = q -> Type} (f : forall e, B e) (e : p = q) : B e := f e.

Definition hd (l : list nat) (H : l <> []) : nat :=
  match l return l <> [] -> nat with
  | [] => fun H => @app 0 0 (fun _ => nat) (fun _ => False_rect nat (H eq_refl)) eq_refl
  | x :: _ => fun _ => x
  end H.

Lemma ne : [4; 5] <> []. Proof. discriminate. Qed.

Definition result : nat := hd [4; 5] ne.

End AbsurdUnderProofBinder.

Crane Extraction "absurd_under_proof_binder" AbsurdUnderProofBinder.
