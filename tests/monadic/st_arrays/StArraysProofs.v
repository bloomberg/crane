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
  Monads.MonadFacts
  Monads.STMonad
  Monads.STMonadArrayFacts
  Monads.STMonadFacts
  Monads.STMonadSpec
.

From CraneTestsMonadic.st_arrays Require Import StArrays.

Import ListNotations.

Section StArraysProofs.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Lemma array_simp_fixed_init_eq_five :
    runST (fun R => array_simp_fixed_init (R := R)) ≈ Ret 5.
  Proof.
    destruct (st_spec_runST (fun R => array_simp_fixed_init (R := R)) (fun r => r = 5))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold array_simp_fixed_init.
    apply st_spec_bind, st_spec_newArray. intros base m Hcells. cbv beta.
    eapply st_spec_readArray; [ lia | apply Hcells; lia | reflexivity ].
  Qed.

  Lemma array_simp_list_eq_five_four_lst :
    runST (fun R => array_simp_list (R := R)) ≈ Ret (5, 4, [5; 4; 3; 2]).
  Proof.
    destruct (st_spec_runST (fun R => array_simp_list (R := R)) (fun r => r = (5, 4, [5; 4; 3; 2])))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold array_simp_list.
    apply st_spec_bind, st_spec_newListArray_rep. intros base m Hrep. cbv beta.
    apply st_spec_bind. eapply st_spec_readArray_rep; [ exact Hrep | reflexivity | cbn; lia |]. cbv beta.
    apply st_spec_bind. eapply st_spec_getElems_rep; [ exact Hrep | reflexivity |]. cbv beta.
    apply st_spec_ret. reflexivity.
  Qed.

  Lemma swap_first_and_last_list_correct : forall xs, xs <> [] ->
    runST (fun R => swap_first_and_last_list (R := R) xs)
    ≈ Ret (list_swap xs 0 (length xs - 1)).
  Proof.
    intros xs Hne.
    assert (Hlen : 0 < length xs) by (destruct xs; [ congruence | simpl; lia ]).
    destruct (st_spec_runST (fun R => swap_first_and_last_list (R := R) xs)
                (fun out => out = list_swap xs 0 (length xs - 1))) as (out & Hrun & ->);
      [| exact Hrun ].
    unfold swap_first_and_last_list.
    apply st_spec_bind, st_spec_newListArray_rep. intros base m0 Hrep0.
    apply st_spec_bind. eapply st_spec_swapArray_rep; [ exact Hrep0 | reflexivity | lia | lia |].
    intros m1 Hrep1.
    eapply st_spec_getElems_rep; [ exact Hrep1 | rewrite list_swap_length; reflexivity | reflexivity ].
  Qed.

  Lemma swap_list_two_one_eq_one_two :
    runST (fun R => swap_first_and_last_list (R := R) [1; 2])
    ≈ (Ret (E := exceptE Err) [2; 1]).
  Proof. rewrite swap_first_and_last_list_correct by discriminate. reflexivity. Qed.

End StArraysProofs.
