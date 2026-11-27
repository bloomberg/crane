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
  Monads.STMonad
  Monads.STMonadFacts
  Monads.STMonadSpec
.

From CraneTestsMonadic.st_refs Require Import StRefs.

Section StRefsProofs.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  (** Each program runs from the empty store, so every lookup is a closed
      computation. *)
  Ltac run_closed :=
    repeat (cbv beta;
      first
        [ apply st_spec_newSTRef
        | apply st_spec_writeSTRef
        | eapply st_spec_readSTRef; [ reflexivity |]
        | apply st_spec_ret; reflexivity
        | apply st_spec_bind
        | reflexivity ]).

  Lemma tree_simp_nat_eq_five :
    runST (fun R => tree_simp_nat (R := R)) ≈ Ret 5.
  Proof.
    destruct (st_spec_runST (fun R => tree_simp_nat (R := R)) (fun r => r = 5))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_nat. run_closed.
  Qed.

  Lemma tree_new_and_read_both_nat_eq_five_six :
    runST (fun R => new_and_read_both_nat (R := R)) ≈ Ret (5, 6).
  Proof.
    destruct (st_spec_runST (fun R => new_and_read_both_nat (R := R)) (fun r => r = (5, 6)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold new_and_read_both_nat. run_closed.
  Qed.

  Lemma tree_simp_another_nat_eq_six :
    runST (fun R => tree_simp_another_nat (R := R)) ≈ Ret 6.
  Proof.
    destruct (st_spec_runST (fun R => tree_simp_another_nat (R := R)) (fun r => r = 6))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_another_nat. run_closed.
  Qed.

  Lemma swapped_eq_two_one :
    runST (fun R => swapped (R := R)) ≈ Ret (2, 1).
  Proof.
    destruct (st_spec_runST (fun R => swapped (R := R)) (fun r => r = (2, 1)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold swapped, swap. run_closed.
  Qed.

  Lemma new_and_read_both_bool_eq_false_true :
    runST (fun R => new_and_read_both_bool (R := R)) ≈ Ret (false, true).
  Proof.
    destruct (st_spec_runST (fun R => new_and_read_both_bool (R := R)) (fun r => r = (false, true)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold new_and_read_both_bool. run_closed.
  Qed.

  Lemma tree_simp_bool_eq_true :
    runST (fun R => tree_simp_bool (R := R)) ≈ Ret true.
  Proof.
    destruct (st_spec_runST (fun R => tree_simp_bool (R := R)) (fun r => r = true))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_bool. run_closed.
  Qed.

End StRefsProofs.
