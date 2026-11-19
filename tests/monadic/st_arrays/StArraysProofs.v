(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The ST array examples of [StArrays] compute the expected values;
    [swap_first_and_last_list] agrees with [list_swap] on every input. *)

From Stdlib Require Import
  Lia
  List
.

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
  Monads.STMonadArrayFacts
  Monads.STMonadFacts
  Monads.STMonadTactics
.

From CraneTestsMonadic.st_arrays Require Import StArrays.

Import ListNotations.

Section StArraysProofs.

  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Lemma array_simp_fixed_init_eq_five :
    runST (S := S) (fun S => array_simp_fixed_init) ≈ Ret 5.
  Proof. unfold array_simp_fixed_init. strun. Qed.

  Lemma array_simp_list_eq_five_four_lst :
    runST (S := S) (fun S => array_simp_list) ≈ Ret (5, 4, [5; 4; 3; 2]).
  Proof. unfold array_simp_list. strun. Qed.

  Lemma swap_first_and_last_list_correct : forall xs, xs <> [] ->
    runST (S := S) (fun S => swap_first_and_last_list xs)
    ≈ Ret (list_swap xs 0 (length xs - 1)).
  Proof.
    intros xs Hne.
    assert (Hlen : 0 < length xs) by (destruct xs; [ congruence | simpl; lia ]).
    destruct (interp_st_newListArray (S := unit) (length xs - 1) xs) as (m0 & Hnew & Hrep).
    eapply runST_Ret. unfold swap_first_and_last_list. cbn [zero fromNat nat_ix].
    eapply interp_st_bind_Ret_l; [ exact Hnew |].
    eapply interp_st_bind_Ret_l; [ apply interp_st_swapArray with (full := xs); auto; lia |].
    apply interp_st_getElems; [ apply arr_rep_swap; auto; lia | rewrite list_swap_length; lia ].
  Qed.

  Lemma swap_list_two_one_eq_one_two :
    runST (S := S) (fun S => swap_first_and_last_list [1; 2])
    ≈ (Ret (E := exceptE Err) [2; 1]).
  Proof. rewrite swap_first_and_last_list_correct by discriminate. reflexivity. Qed.

End StArraysProofs.
