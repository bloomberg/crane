(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The ST reference examples of [StRefs] compute the expected values. *)

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.MonadFacts
  Monads.STMonad
  Monads.STMonadFacts
  Monads.STMonadSpec
.

From CraneTestsMonadic.st_refs Require Import StRefs.

Section StRefsProofs.

  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  (** Each program runs from the empty store, so every lookup is a closed
      computation. *)
  Lemma tree_simp_nat_eq_five :
    runST (S := S) (fun S => tree_simp_nat) ≈ Ret 5.
  Proof.
    destruct (st_spec_runST (S := S) (fun _ => tree_simp_nat) (fun r => r = 5))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_nat.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => nat) zero). cbv beta.
    apply (st_spec_readSTRef (V := fun _ : nat => nat) zero _ _ 5); reflexivity.
  Qed.

  Lemma tree_new_and_read_both_nat_eq_five_six :
    runST (S := S) (fun S => new_and_read_both_nat) ≈ Ret (5, 6).
  Proof.
    destruct (st_spec_runST (S := S) (fun _ => new_and_read_both_nat) (fun r => r = (5, 6)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold new_and_read_both_nat.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => nat) zero). cbv beta.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => nat) (suc zero)). cbv beta.
    apply st_spec_bind, (st_spec_readSTRef (V := fun _ : nat => nat) zero _ _ 5); [ reflexivity |]. cbv beta.
    apply st_spec_bind, (st_spec_readSTRef (V := fun _ : nat => nat) (suc zero) _ _ 6); [ reflexivity |]. cbv beta.
    apply st_spec_ret. reflexivity.
  Qed.

  Lemma tree_simp_another_nat_eq_six :
    runST (S := S) (fun S => tree_simp_another_nat) ≈ Ret 6.
  Proof.
    destruct (st_spec_runST (S := S) (fun _ => tree_simp_another_nat) (fun r => r = 6))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_another_nat.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => nat) zero). cbv beta.
    apply st_spec_bind, (st_spec_writeSTRef (V := fun _ : nat => nat) zero). cbv beta.
    apply (st_spec_readSTRef (V := fun _ : nat => nat) zero _ _ 6); reflexivity.
  Qed.

  Lemma new_and_read_both_bool_eq_false_true :
    runST (S := S) (fun S => new_and_read_both_bool) ≈ Ret (false, true).
  Proof.
    destruct (st_spec_runST (S := S) (fun _ => new_and_read_both_bool) (fun r => r = (false, true)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold new_and_read_both_bool.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => bool) zero). cbv beta.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => bool) (suc zero)). cbv beta.
    apply st_spec_bind, (st_spec_readSTRef (V := fun _ : nat => bool) zero _ _ false); [ reflexivity |]. cbv beta.
    apply st_spec_bind, (st_spec_readSTRef (V := fun _ : nat => bool) (suc zero) _ _ true); [ reflexivity |]. cbv beta.
    apply st_spec_ret. reflexivity.
  Qed.

  Lemma tree_simp_bool_eq_true :
    runST (S := S) (fun S => tree_simp_bool) ≈ Ret true.
  Proof.
    destruct (st_spec_runST (S := S) (fun _ => tree_simp_bool) (fun r => r = true))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_bool.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ : nat => bool) zero). cbv beta.
    apply (st_spec_readSTRef (V := fun _ : nat => bool) zero _ _ true); reflexivity.
  Qed.

End StRefsProofs.
