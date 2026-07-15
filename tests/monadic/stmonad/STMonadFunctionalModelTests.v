(* Equational theory and Derive proofs for the ST monad *)

From Crane Require Import Monads.STMonad Monads.ITree Monads.STMonadFacts Utils.HMap.

From Stdlib Require Import
  Arith.PeanoNat
  Classes.EquivDec
  Lia
  List
  RelationClasses
  Setoid
  Strings.String
.


From ExtLib Require Import
  CmpDec
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Structures.Functor
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

  Lemma quicksort_ST_list2154 :
    burn 100 (runST (S := S) (fun S0 => quicksort_ST_list (S := S0) [2;1;5;4]))
    = Ret [1;2;4;5].
  Proof using Type. lazy. reflexivity. Qed.

  Lemma sort_list__long :
    burn 300 (runST (S := S) (fun S0 => quicksort_ST_list (S := S0) [8;4;6;9;7;3;1;2;5]))
    = Ret [1;2;3;4;5;6;7;8;9].
  Proof using Type. lazy. reflexivity. Qed.



  (* Fibonacci function proofs. *)


  (* The subcomputation within fib, extracted out so that it can be reasoned about.
     a and b are the starting memory cells, and k is the number of iterations of fibonacci to run.
   *)
  Fixpoint fib_seq (a b k : nat) : nat :=
    match k with
    | 0 => a
    | Datatypes.S k' => fib_seq b (a + b) k'
    end.

  Lemma fib_seq_add : forall n a b c d,
    fib_seq a b n + fib_seq c d n = fib_seq (a+c) (b+d) n.
  Proof. induction n; intros; simpl; [lia | rewrite IHn; f_equal; lia]. Qed.

  Lemma fib_fun_eq_seq : forall n, fib_fun n = fib_seq 0 1 n.
  Proof.
    enough (forall n, fib_fun n = fib_seq 0 1 n /\ fib_fun (Datatypes.S n) = fib_seq 0 1 (Datatypes.S n))
      as H by (intro n; exact (proj1 (H n))).
    induction n as [|n [IH1 IH2]]; [split; reflexivity |].
    split; [exact IH2 |].
    change (fib_fun (Datatypes.S (Datatypes.S n))) with (fib_fun (Datatypes.S n) + fib_fun n).
    rewrite IH1, IH2.
    change (fib_seq 0 1 (Datatypes.S (Datatypes.S n))) with (fib_seq 1 2 n).
    change (fib_seq 0 1 (Datatypes.S n)) with (fib_seq 1 1 n).
    apply fib_seq_add.
  Qed.

  (* TODO: suggests a hintdb-shaped soln would be appropriate here. *)
  Opaque add lookup STRefToIx zero suc.
  Lemma fib_loop_correct :
    forall k (a b : nat) (m : mem) (x y : STRef S nat),
    lookup (STRefToIx S nat x, zero) m = Some a ->
    lookup (STRefToIx S nat y, suc zero) m = Some b ->
    fmap snd (interp_st ltu nat (fib_loop k x y zero (suc zero)) m)
    ≈ Ret (fib_seq a b k).
  Proof.
    induction k; intros a b m x y hx hy.
    - simpl fib_loop.
      etransitivity.
      { eapply eutt_fmap.
        unfold readSTRef. rewrite interp_st_trigger. cbn. rewrite hx. reflexivity. }
      setoid_rewrite map_ret. cbn. reflexivity.
    - simpl fib_loop.
      etransitivity.
      { eapply eutt_fmap.
        eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
        + unfold readSTRef. rewrite interp_st_trigger. cbn. rewrite hx. reflexivity.
        + intros u lmem'. eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
          * unfold readSTRef. rewrite interp_st_trigger. cbn.
            change lmem' with (fst (lmem', u)). reflexivity.
          * intros u0 lmem'0. eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
            -- unfold writeSTRef. rewrite interp_st_trigger. cbn.
               change u0 with (snd (lmem'0, u0)).
               change lmem'0 with (fst (lmem'0, u0)).
               change lmem' with (fst (lmem', u)). reflexivity.
            -- intros u1 lmem'1. eapply (eutt_eq_bind_interp_st ltu ltac:(refine_arg)).
               ++ unfold writeSTRef. rewrite interp_st_trigger. cbn.
                  change u with (snd (lmem', u)).
                  change u0 with (snd (lmem'0, u0)).
                  change lmem'1 with (fst (lmem'1, u1)).
                  change lmem' with (fst (lmem', u)). reflexivity.
               ++ intros u2 lmem'2.
                  change lmem'2 with (fst (lmem'2, u2)). reflexivity. }
      setoid_rewrite map_bind. repeat setoid_rewrite bind_Ret_l. cbn [fst snd].
      rewrite hy. cbn [fst snd].
      repeat setoid_rewrite bind_Ret_l. cbn [fst snd].
      apply IHk.
      + etransitivity; [apply hmap_lookup_add_ne; intros [=] |].
        rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
      + rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
  Qed.

  Lemma fib_ST_full_correct : forall n,
    fmap snd (interp_st (S := S) ltu nat
      (x <- newSTRef zero 0;; y <- newSTRef (suc zero) 1;; fib_loop n x y zero (suc zero))
      HMap.empty)
    ≈ Ret (fib_seq 0 1 n).
  Proof.
    intro n.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
      + unfold newSTRef. rewrite interp_st_trigger. cbn. reflexivity.
      + intros u lmem'.
        eapply (eutt_eq_bind_interp_st ltu ltac:(refine_prod)).
        * unfold newSTRef. rewrite interp_st_trigger. cbn.
          change lmem' with (fst (lmem', u)). reflexivity.
        * intros ? ?. reflexivity. }
    setoid_rewrite map_bind. repeat setoid_rewrite bind_Ret_l. cbn [fst snd].
    apply fib_loop_correct.
    + etransitivity; [apply hmap_lookup_add_ne; intros [=] |].
      rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
    + rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
  Qed.

  Transparent add lookup STRefToIx zero suc.

End NatProgramProofs.


Lemma fib_ST_eq_fib_fun : forall {S : Type} (n : nat),
    Ret (fib_fun n) ≈ runST (S := S) (fun S0 => fib_ST n).
Proof.
  intros S n. unfold runST, fib_ST.
  destruct (Nat.ltb n 2) eqn:Hn.
  - apply Nat.ltb_lt in Hn. symmetry.
    etransitivity.
    { eapply eutt_fmap. rewrite interp_st_Ret. reflexivity. }
    setoid_rewrite map_ret. cbn. apply eqit_Ret.
    destruct n as [|[|n]]; try lia; reflexivity.
  - apply Nat.ltb_ge in Hn. symmetry.
    rewrite fib_fun_eq_seq.
    exact (@fib_ST_full_correct unit n).
Qed.
