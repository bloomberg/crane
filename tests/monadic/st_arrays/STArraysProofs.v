(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The ST array examples of [STArrays] compute the expected values;
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

From Crane Require Monads.ST.
From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.MonadFacts
  Monads.STArrayFacts
  Monads.STFacts
  Monads.STSpec
.

From CraneTestsMonadic.st_arrays Require Import STArrays.

Import ListNotations.

Section STArraysProofs.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.hmap_ok_halist.

  Lemma array_simp_fixed_init_eq_five :
    ST.run (fun R => array_simp_fixed_init (R := R)) ≈ Ret 5.
  Proof.
    destruct (run (fun R => array_simp_fixed_init (R := R)) (fun r => r = 5))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold array_simp_fixed_init.
    apply spec_bind, new_array. intros base m Hcells. cbv beta.
    eapply read_array; [ lia | apply Hcells; lia | reflexivity ].
  Qed.

  Lemma array_simp_list_eq_five_four_lst :
    ST.run (fun R => array_simp_list (R := R)) ≈ Ret (5, 4, [5; 4; 3; 2]).
  Proof.
    destruct (run (fun R => array_simp_list (R := R)) (fun r => r = (5, 4, [5; 4; 3; 2])))
      as (r & Hrun & ->); [| exact Hrun ].
    unfold array_simp_list.
    apply spec_bind, array_of_list_rep. intros base m Hrep. cbv beta.
    apply spec_bind. eapply read_array_rep; [ exact Hrep | reflexivity | cbn; lia |]. cbv beta.
    apply spec_bind. eapply array_to_list_rep; [ exact Hrep | reflexivity |]. cbv beta.
    apply spec_ret. reflexivity.
  Qed.

  Lemma swap_first_and_last_list_correct : forall xs, xs <> [] ->
    ST.run (fun R => swap_first_and_last_list (R := R) xs)
    ≈ Ret (list_swap xs 0 (length xs - 1)).
  Proof.
    intros xs Hne.
    assert (Hlen : 0 < length xs) by (destruct xs; [ congruence | simpl; lia ]).
    destruct (run (fun R => swap_first_and_last_list (R := R) xs)
                (fun out => out = list_swap xs 0 (length xs - 1))) as (out & Hrun & ->);
      [| exact Hrun ].
    unfold swap_first_and_last_list.
    apply spec_bind, array_of_list_rep. intros base m0 Hrep0.
    apply spec_bind. eapply swap_array_rep; [ exact Hrep0 | reflexivity | lia | lia |].
    intros m1 Hrep1.
    eapply array_to_list_rep; [ exact Hrep1 | rewrite list_swap_length; reflexivity | reflexivity ].
  Qed.

  Lemma swap_list_two_one_eq_one_two :
    ST.run (fun R => swap_first_and_last_list (R := R) [1; 2])
    ≈ (Ret (E := exceptE Err) [2; 1]).
  Proof. rewrite swap_first_and_last_list_correct by discriminate. reflexivity. Qed.

End STArraysProofs.
