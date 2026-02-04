(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test that Prop terms are erased during extraction *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module PropErasure.

(* A proof term that should be erased *)
Definition proof_of_true : True := I.

(* A function with a proof argument that should be erased *)
Definition with_proof_arg (n : nat) (pf : n = n) : nat := n.

(* Using the function - the proof should be erased *)
Definition use_proof : nat := with_proof_arg five eq_refl.

(* Function returning proof that should become unit *)
Definition returns_proof (n : nat) : n = n := eq_refl.

(* Logical conjunction - should be erased *)
Definition conj_proof : True /\ True := conj I I.

(* A simple definition to verify extraction works *)
Definition simple_value : nat := seven.

(* Test that computation with proof args works *)
Definition add_with_proof (a b : nat) (pf : True) : nat := Nat.add a b.
Definition test_add_proof := add_with_proof three four I.

(* Test values *)
Definition test_use_proof := use_proof.
Definition test_simple := simple_value.

End PropErasure.

Crane Extraction "prop_erasure" PropErasure.
