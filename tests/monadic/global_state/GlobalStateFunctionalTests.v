(* Equational theory and Derive proofs for the ST monad *)

(* TODO: unfinished! do not commit! *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Compare_dec
  Arith.Peano_dec
  Classes.EquivDec
  Lia
  List
  RelationClasses
  Setoid
  Strings.String
  Sorting.Permutation
  Sorting.Sorted
.
From Equations Require Import Equations.


From ExtLib Require Import
  CmpDec
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Structures.Functor
  Structures.Traversable
  Structures.Reducible
  Structures.Monad
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
From CraneTestsMonadic.global_state Require Import GlobalStateExamples.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.MonadFacts
  Monads.GlobalState
  Monads.GlobalStateFacts
  Utils.HMap
.

Section NatProgramProofs.


  Let T := nat.
  Let ltu := Nat.le.
  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_globref.
  Context {S : Type}.
  
  (* only integer typed values here *)
  Let V : T -> Type := fun _ => nat.

  Let E0 := (GlobEvent T V) +' exceptE Err.


  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Derive (tree_simplified : itree (exceptE Err) (HAList.halist (idx_key T) (idx_key_type (fun _ : T => nat)) * nat)) in
    ( runGlob tree_simp_nat 
        ≈
      tree_simplified
    ) as tree_simplification.
  Proof using Type.
    unfold runGlob.
    unfold tree_simp_nat.
    etransitivity.
    eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_prod)).
    - unfold newGlobRef.
      eapply interp_glob_trigger.
    - intros u lmem'.
      unfold readGlobRef.
      eapply interp_glob_trigger.
    - repeat setoid_rewrite bind_Ret_l. cbn.
      unfold tree_simplified.
      reflexivity.
  Defined.

  Lemma fib_10 :
    burn 100 (runGlob (fib_Glob 10))
    = Ret ([existT (fun k : idx_key nat => idx_key_type (fun _ : nat => nat) k) (2, 1) 89;
           existT (fun k : idx_key nat => idx_key_type (fun _ : nat => nat) k) (1, 0) 55],
          55).
  Proof using Type. lazy. reflexivity. Qed.

  (* TODO: duplicates proof work from STMonadFunctionalTests.v *)
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
  Proof using Type. induction n; intros; simpl; [lia | rewrite IHn; f_equal; lia]. Qed.

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

  Opaque add lookup GlobRefToIx zero suc.
  Lemma fib_loop_correct :
    forall k (a b : nat) (m : mem) (x y : GlobRef nat),
    lookup (GlobRefToIx nat x, idx_x) m = Some a ->
    lookup (GlobRefToIx nat y, idx_y) m = Some b ->
    fmap snd (interp_glob ltu nat (fib_loop k x y) m)
    ≈ ITreeDefinition.Ret (fib_seq a b k).
  Proof.
    induction k; intros a b m x y hx hy.
    - simpl fib_loop.
      etransitivity.
      { eapply eutt_fmap.
        unfold readGlobRef. rewrite interp_glob_trigger. cbn. rewrite hx. reflexivity. }
      setoid_rewrite map_ret. cbn. reflexivity.
    - simpl fib_loop.
      etransitivity.
      { eapply eutt_fmap.
        eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_arg)).
        + unfold readGlobRef. rewrite interp_glob_trigger. cbn. rewrite hx. reflexivity.
        + intros u lmem'. eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_arg)).
          * unfold readGlobRef. rewrite interp_glob_trigger. cbn.
            change lmem' with (fst (lmem', u)). reflexivity.
          * intros u0 lmem'0. eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_arg)).
            -- unfold writeGlobRef. rewrite interp_glob_trigger. cbn.
               change u0 with (snd (lmem'0, u0)).
               change lmem'0 with (fst (lmem'0, u0)).
               change lmem' with (fst (lmem', u)). reflexivity.
            -- intros u1 lmem'1. eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_arg)).
               ++ unfold writeGlobRef. rewrite interp_glob_trigger. cbn.
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

  Lemma fib_Glob_full_correct : forall n,
    fmap snd (interp_glob ltu nat
      (x <- newGlobRef idx_x 0;; y <- newGlobRef idx_y 1;; fib_loop n x y)
      HMap.empty)
    ≈ Ret (fib_seq 0 1 n).
  Proof.
    intro n.
    etransitivity.
    { eapply eutt_fmap.
      eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_prod)).
      + unfold newGlobRef. rewrite interp_glob_trigger. cbn. reflexivity.
      + intros u lmem'.
        eapply (eutt_eq_bind_interp_glob ltu ltac:(refine_prod)).
        * unfold newGlobRef. rewrite interp_glob_trigger. cbn.
          change lmem' with (fst (lmem', u)). reflexivity.
        * intros ? ?. reflexivity. }
    setoid_rewrite map_bind. repeat setoid_rewrite bind_Ret_l. cbn [fst snd].
    apply fib_loop_correct.
    + etransitivity; [apply hmap_lookup_add_ne; intros [=] |].
      rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
    + rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
  Qed.

End NatProgramProofs.

Lemma fib_ST_eq_fib_fun : forall (n : nat),
    Ret (fib_fun n) ≈ fmap snd (runGlob (fib_Glob n)).
Proof.
  intros n. unfold runGlob, fib_Glob.
  destruct (Nat.ltb n 2) eqn:Hn.
  - apply Nat.ltb_lt in Hn. symmetry.
    etransitivity.
    { eapply eutt_fmap. change_to_monad. rewrite interp_glob_ret. reflexivity. }
    setoid_rewrite map_ret. cbn. apply eqit_Ret.
    destruct n as [|[|n]]; try lia; reflexivity.
  - apply Nat.ltb_ge in Hn. symmetry.
    rewrite fib_fun_eq_seq.
    exact (@fib_Glob_full_correct n).
Qed.
