(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Sigma types with computation — {x : T & P x} used at runtime. *)

From Stdlib Require Import List Nat Bool Arith.
Import ListNotations.

Module SigmaTypes.

(* sigT: dependent pair where second component is a type *)
Definition nat_with_double (n : nat) : {x : nat & x = n + n} :=
  existT _ (n + n) eq_refl.

(* sig: subset type where second component is Prop *)
Definition positive_succ (n : nat) : {m : nat | m > 0} :=
  exist _ (S n) (Nat.lt_0_succ n).

(* Extract the witness from a sig *)
Definition get_positive (n : nat) : nat :=
  proj1_sig (positive_succ n).

(* Chain sig computations *)
Definition double_positive (n : nat) : {m : nat | m > 0} :=
  let p := positive_succ n in
  exist _ (proj1_sig p + proj1_sig p) (Nat.lt_0_succ _).

(* sigT with projections used in computation *)
Definition use_nat_double (n : nat) : nat :=
  projT1 (nat_with_double n).

(* List of sig values *)
Definition positives_up_to (n : nat) : list nat :=
  let fix go (k : nat) : list nat :=
    match k with
    | 0 => []
    | S k' => proj1_sig (positive_succ k') :: go k'
    end
  in go n.

(* === Test values === *)

Definition test_double_5 : nat := use_nat_double 5.
Definition test_positive_3 : nat := get_positive 3.
Definition test_double_pos : nat := proj1_sig (double_positive 3).
Definition test_positives : list nat := positives_up_to 5.

End SigmaTypes.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "sigma_types" SigmaTypes.
