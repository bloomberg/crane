(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The ST reference examples of [STRefs] compute the expected values. *)

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

From Crane Require Monads.ST.
From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.STFacts
  Monads.STSpec
.

From CraneTestsMonadic.st_refs Require Import STRefs.

Section STRefsProofs.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  (** Each program runs from the empty store, so every lookup is a closed
      computation. *)
  Ltac run_closed :=
    repeat (cbv beta;
      first
        [ apply new_ref
        | apply write_ref
        | eapply read_ref; [ reflexivity |]
        | apply spec_ret; reflexivity
        | apply spec_bind
        | reflexivity ]).

  Lemma tree_simp_nat_eq_five :
    ST.run (fun R => tree_simp_nat (R := R)) ≈ Ret 5.
  Proof.
    destruct (run (fun R => tree_simp_nat (R := R)) (fun r => r = 5))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_nat. run_closed.
  Qed.

  Lemma tree_new_and_read_both_nat_eq_five_six :
    ST.run (fun R => new_and_read_both_nat (R := R)) ≈ Ret (5, 6).
  Proof.
    destruct (run (fun R => new_and_read_both_nat (R := R)) (fun r => r = (5, 6)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold new_and_read_both_nat. run_closed.
  Qed.

  Lemma tree_simp_another_nat_eq_six :
    ST.run (fun R => tree_simp_another_nat (R := R)) ≈ Ret 6.
  Proof.
    destruct (run (fun R => tree_simp_another_nat (R := R)) (fun r => r = 6))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_another_nat. run_closed.
  Qed.

  Lemma swapped_eq_two_one :
    ST.run (fun R => swapped (R := R)) ≈ Ret (2, 1).
  Proof.
    destruct (run (fun R => swapped (R := R)) (fun r => r = (2, 1)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold swapped, swap. run_closed.
  Qed.

  Lemma new_and_read_both_bool_eq_false_true :
    ST.run (fun R => new_and_read_both_bool (R := R)) ≈ Ret (false, true).
  Proof.
    destruct (run (fun R => new_and_read_both_bool (R := R)) (fun r => r = (false, true)))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold new_and_read_both_bool. run_closed.
  Qed.

  Lemma tree_simp_bool_eq_true :
    ST.run (fun R => tree_simp_bool (R := R)) ≈ Ret true.
  Proof.
    destruct (run (fun R => tree_simp_bool (R := R)) (fun r => r = true))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold tree_simp_bool. run_closed.
  Qed.

End STRefsProofs.
