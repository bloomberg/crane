(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Direct Acc_rect / well-founded induction. *)

From Stdlib Require Import Nat Bool List Wf_nat Lia PeanoNat.
Import ListNotations.

Module WellFoundedRec.

(* === Acc-based countdown === *)

Fixpoint countdown_acc (n : nat) (acc : Acc lt n) {struct acc} : list nat :=
  match n as n0 return Acc lt n0 -> list nat with
  | 0 => fun _ => [0]
  | S m => fun acc' => n :: countdown_acc m (Acc_inv acc' (Nat.lt_succ_diag_r m))
  end acc.

Definition countdown (n : nat) : list nat :=
  countdown_acc n (lt_wf n).

(* === div2 via well_founded_induction === *)

Lemma lt_S_S : forall m, m < S (S m).
Proof. intro. lia. Qed.

Definition div2_wf : nat -> nat :=
  well_founded_induction lt_wf (fun _ => nat)
    (fun n rec =>
      match n as n0 return (forall m, m < n0 -> nat) -> nat with
      | 0 => fun _ => 0
      | 1 => fun _ => 0
      | S (S m) => fun rec' => S (rec' m (lt_S_S m))
      end rec).

(* === GCD via well_founded_induction === *)

Lemma mod_lt_S : forall b a, Nat.modulo b (S a) < S a.
Proof. intros. apply Nat.mod_upper_bound. lia. Qed.

Definition gcd_wf : nat -> nat -> nat :=
  well_founded_induction lt_wf (fun _ => nat -> nat)
    (fun a rec b =>
      match a as a0 return (forall m, m < a0 -> nat -> nat) -> nat with
      | 0 => fun _ => b
      | S a' => fun rec' => rec' (Nat.modulo b (S a')) (mod_lt_S b a') (S a')
      end rec).

(* === Test values === *)

Definition test_div2_0 : nat := div2_wf 0.
Definition test_div2_1 : nat := div2_wf 1.
Definition test_div2_7 : nat := div2_wf 7.
Definition test_div2_10 : nat := div2_wf 10.

Definition test_countdown : list nat := countdown 5.

Definition test_gcd_1 : nat := gcd_wf 12 8.
Definition test_gcd_2 : nat := gcd_wf 35 14.
Definition test_gcd_3 : nat := gcd_wf 0 5.

End WellFoundedRec.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "well_founded_rec" WellFoundedRec.
