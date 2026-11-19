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
  Monads.STMonadTactics
.

From CraneTestsMonadic.st_refs Require Import StRefs.

Section StRefsProofs.

  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Lemma tree_simp_nat_eq_five :
    runST (S := S) (fun S => tree_simp_nat) ≈ Ret 5.
  Proof. unfold tree_simp_nat. strun. Qed.

  Lemma tree_new_and_read_both_nat_eq_five_six :
    runST (S := S) (fun S => new_and_read_both_nat) ≈ Ret (5, 6).
  Proof. unfold new_and_read_both_nat. strun. Qed.

  Lemma tree_simp_another_nat_eq_six :
    runST (S := S) (fun S => tree_simp_another_nat) ≈ Ret 6.
  Proof. unfold tree_simp_another_nat. strun. Qed.

  Lemma new_and_read_both_bool_eq_false_true :
    runST (S := S) (fun S => new_and_read_both_bool) ≈ Ret (false, true).
  Proof. unfold new_and_read_both_bool. strun. Qed.

  Lemma tree_simp_bool_eq_true :
    runST (S := S) (fun S => tree_simp_bool) ≈ Ret true.
  Proof. unfold tree_simp_bool. strun. Qed.

End StRefsProofs.
