(* Equational theory and Derive proofs for the ST monad *)

From Crane Require Import Monads.STMonad Monads.ITree Monads.STMonadFacts.

From Stdlib Require Import
  Arith.PeanoNat
  List
  RelationClasses
  Setoid
  Strings.String
  Classes.EquivDec
.


From ExtLib Require Import
  CmpDec
  Data.List
  Data.Map.FMapAList
  Data.Monads.EitherMonad
  Data.Pair
  Structures.Functor
  Structures.Maps
  Structures.Traversable
  Structures.Reducible
.

From Paco Require Import paco.

From ITree Require Import
  Basics.HeterogeneousRelations
  Eq.Paco2
  Events.Exception
  Events.FailFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

From Corelib Require Derive.
From CraneTestsMonadic.stmonad Require Import STMonadExamples.

Section NatProgramProofs.


  Let T := nat.
  Let ltu := Nat.le.
  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.
  
  (* only integer typed values here *)
  Let V : T -> Type := fun _ => nat.

  Let E0 := (STEvent T S V) +' exceptE Err.


  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Derive (tree_simplified : itree (exceptE Err) nat) in
    ( runST (S := S) (fun S => tree_simp_nat)
        ≈
      tree_simplified
    ) as tree_simplification.
  Proof.
    unfold runST.
    unfold tree_simp_nat.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      - unfold newSTRef.
        rewrite interp_st_trigger.
        cbn.
        reflexivity.
      - intros u lmem'.
        unfold readSTRef.
        rewrite interp_st_trigger.
        cbn.
        reflexivity. }
    setoid_rewrite map_bind.
    repeat setoid_rewrite bind_Ret_l.
    simpl.
    unfold tree_simplified.
    reflexivity.
  Defined.



  Derive (readboth_simplified : itree (exceptE Err) (nat*nat)) in
    ( runST (S := S) (fun S => new_and_read_both_nat)
        ≈
      readboth_simplified
    ) as tree_simplification2.
  Proof.
    unfold runST, new_and_read_both_nat.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      - unfold newSTRef. rewrite interp_st_trigger. cbn. reflexivity.
      - intros u lmem'.
        eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
        + unfold newSTRef. rewrite interp_st_trigger. cbn.
          change lmem' with (fst (lmem', u)). reflexivity.
        + intros ? ?.
          eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
          * unfold readSTRef. rewrite interp_st_trigger. cbn.
            change u with (snd (lmem', u)).
            change lmem'0 with (fst (lmem'0, u0)). reflexivity.
          * intros ? ?.
            eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
            -- unfold readSTRef. rewrite interp_st_trigger. cbn.
               change u with (snd (lmem', u)).
               change lmem'0 with (fst (lmem'0, u0)).
               change u0 with (snd (lmem'0, u0)).
               change lmem'1 with (fst (lmem'1, u1)). reflexivity.
            -- intros ? ?.
               rewrite interp_st_Ret.
               change lmem'2 with (fst (lmem'2, u2)).
               change u1 with (snd (lmem'1, u1)).
               change u2 with (snd (lmem'2, u2)). reflexivity. }
    setoid_rewrite map_bind.
    repeat setoid_rewrite bind_Ret_l.
    simpl.
    unfold readboth_simplified.
    reflexivity.
  Defined.

  
  Derive (read_array5 : itree (exceptE Err) nat) in
    ( runST (S := S) (fun S => array_simp_fixed_init)
        ≈
      read_array5
    ) as tree_simplification3.
  Proof.
    unfold runST, array_simp_fixed_init.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold newArray. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
      {
        unfold readArray. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      rewrite interp_st_Ret. reflexivity.
    }
    setoid_rewrite map_bind.
    repeat setoid_rewrite bind_Ret_l.
    simpl.
    unfold read_array5.
    reflexivity.
    Defined.

  Derive (read_array_list_init : itree (exceptE Err) (nat * nat * list nat)) in
    ( runST (S := S) (fun S => array_simp_list)
        ≈
      read_array_list_init
    ) as tree_simplification4.
  Proof.
    unfold runST, array_simp_fixed_init.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold newListArray. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold readArray. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold getElems. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      rewrite interp_st_Ret. reflexivity.
    }
    setoid_rewrite map_bind.
    repeat setoid_rewrite bind_Ret_l.
    simpl.
    unfold read_array_list_init.
    reflexivity.
    Defined.

  Derive (swap_list12 : itree (exceptE Err) (list nat)) in
    ( runST (S := S) (fun S => swap_first_and_last_list [1;2])
        ≈
      swap_list12
    ) as tree_simplification5.
  Proof.
    unfold runST, swap_list12.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold newListArray. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold swap_arr.
        eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
        {
          unfold readArray. rewrite interp_st_trigger. cbn. reflexivity.
        }
        intros ? ?.
        eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
        {
          unfold readArray. rewrite interp_st_trigger. cbn. reflexivity.
        }
        intros ? ?.
        eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
        {
          unfold writeArray. rewrite interp_st_trigger. cbn. reflexivity.
        }
        intros ? ?.
        unfold writeArray. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      {
        unfold getElems. rewrite interp_st_trigger. cbn. reflexivity.
      }
      intros ? ?.
      rewrite interp_st_Ret. reflexivity.
    }
    setoid_rewrite map_bind.
    repeat setoid_rewrite bind_Ret_l.
    simpl.
    reflexivity.
    Defined.

  Lemma sort_list2154 :
    burn 100 (runST (S := S) (fun S0 => sort_list (S := S0) [2;1;5;4]))
    = Ret [1;2;4;5].
  Proof using Type. lazy. reflexivity. Qed.

  Lemma sort_list__long :
    burn 300 (runST (S := S) (fun S0 => sort_list (S := S0) [8;4;6;9;7;3;1;2;5]))
    = Ret [1;2;3;4;5;6;7;8;9].
  Proof using Type. lazy. reflexivity. Qed.

  Lemma fib_ST_eq_fib_fun : forall (n : nat),
      Ret (fib_fun n) ≈ runST (S := S) (fun S => fib_ST n).
  Proof.
    (* TODO: finish this proof! Do not edit the specification! *)
  Abort.



End NatProgramProofs.



