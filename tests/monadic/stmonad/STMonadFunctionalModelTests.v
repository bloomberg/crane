(* Equational theory and Derive proofs for the ST monad *)

From Crane Require Import Monads.STMonad Monads.ITree Monads.STMonadFacts Utils.HMap.

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Compare_dec
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
  Proof using Type.
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

  (* ---- interp_st of the array leaf operations ---- *)

  Lemma interp_st_readArray (idx : nat) (arr : STArray nat S nat) (i : nat)
        (m : mem) (v : nat) :
    @arr_lookup nat S ltu nat_ix (fun _ : nat => nat) mem _ idx arr i m = Some v ->
    interp_st ltu nat (@readArray E0 nat _ _ _ _ idx arr i) m ≈ Ret (m, v).
  Proof.
    intros Hlk. unfold readArray, E0, V, T. rewrite interp_st_trigger.
    cbn -[arr_lookup lookup add]. rewrite Hlk. reflexivity.
  Qed.

  Lemma interp_st_writeArray (idx : nat) (arr : STArray nat S nat) (i v : nat)
        (m : mem) (key : nat) :
    @arr_key nat S ltu nat_ix (fun _ : nat => nat) idx arr i = Some key ->
    interp_st ltu unit (@writeArray E0 nat _ _ _ _ idx arr i v) m
    ≈ Ret (add (key, idx) v m, tt).
  Proof.
    intros Hk. unfold writeArray, E0, V, T. rewrite interp_st_trigger.
    cbn -[arr_key lookup add]. rewrite Hk. reflexivity.
  Qed.

  (* Physical key of logical index [i] in an array with base/lo/hi. *)
  Lemma arr_key_val : forall (base lo hi i : nat),
    lo <= i -> i <= hi ->
    @arr_key nat S ltu nat_ix (fun _ : nat => nat) 0 (MkSTArray nat S nat base lo hi) i
    = Some (base + (i - lo)).
  Proof.
    intros base lo hi i Hlo Hhi. unfold arr_key. cbn -[Nat.sub].
    rewrite (proj2 (Nat.leb_le lo i) Hlo), (proj2 (Nat.leb_le i hi) Hhi).
    cbn -[Nat.sub]. f_equal.
    generalize (i - lo) as n; intro n.
    induction n as [|n' IH]; [ cbn; lia | ].
    cbn [suc_n suc nat_ix]. rewrite IH. lia.
  Qed.

  (* Representation: physical cells [base .. base+|full|-1] (idx 0) hold [full]. *)
  Definition arr_rep (m : @mem nat V) (base : nat) (full : list nat) : Prop :=
    forall k, k < length full -> lookup (base + k, 0%nat) m = Some (nth k full 0).

  Lemma arr_key_val0 : forall (base hi i : nat),
    i <= hi ->
    @arr_key nat S ltu nat_ix (fun _ : nat => nat) 0 (MkSTArray nat S nat base 0 hi) i
    = Some (base + i).
  Proof. intros. rewrite arr_key_val by lia. f_equal. lia. Qed.

  Lemma arr_lookup_rep : forall base hi full i m,
    arr_rep m base full -> i <= hi -> hi < length full ->
    @arr_lookup nat S ltu nat_ix (fun _ : nat => nat) mem _ 0
       (MkSTArray nat S nat base 0 hi) i m
    = Some (nth i full 0).
  Proof.
    intros base hi full i m Hrep Hih Hhl. unfold arr_lookup.
    rewrite arr_key_val by lia.
    replace (i - 0) with i by lia. apply Hrep. lia.
  Qed.

  (* Pure list update, for modelling in-place writes. *)
  Fixpoint upd (l : list nat) (i v : nat) : list nat :=
    match l, i with
    | nil, _ => nil
    | _ :: t, 0 => v :: t
    | h :: t, Datatypes.S i' => h :: upd t i' v
    end.

  Lemma upd_length : forall l i v, length (upd l i v) = length l.
  Proof. induction l; intros [|i] v; simpl; auto. Qed.

  Lemma nth_upd_eq : forall l i v, i < length l -> nth i (upd l i v) 0 = v.
  Proof. induction l; intros [|i] v H; simpl in *; try lia; auto. apply IHl; lia. Qed.

  Lemma nth_upd_neq : forall l i j v, i <> j -> nth j (upd l i v) 0 = nth j l 0.
  Proof.
    induction l as [|a l IHl]; intros i j v H.
    - destruct j; reflexivity.
    - destruct i as [|i]; destruct j as [|j]; simpl.
      + exfalso; lia.
      + reflexivity.
      + reflexivity.
      + apply IHl; lia.
  Qed.

  Lemma arr_rep_write : forall base full i v m,
    arr_rep m base full -> i < length full ->
    arr_rep (add (base + i, 0%nat) v m) base (upd full i v).
  Proof.
    intros base full i v m Hrep Hi k Hk. rewrite upd_length in Hk.
    destruct (Nat.eq_dec k i).
    - subst k. rewrite hmap_lookup_add_eq. rewrite nth_upd_eq by lia. reflexivity.
    - rewrite hmap_lookup_add_ne by (intros [=]; lia).
      rewrite nth_upd_neq by lia. apply Hrep. lia.
  Qed.

  Definition list_swap (l : list nat) (i j : nat) : list nat :=
    upd (upd l i (nth j l 0)) j (nth i l 0).

  Lemma list_swap_length : forall l i j, length (list_swap l i j) = length l.
  Proof. intros. unfold list_swap. rewrite !upd_length. reflexivity. Qed.

  Lemma arr_rep_swap : forall base full left right m,
    arr_rep m base full -> left < length full -> right < length full ->
    arr_rep (add (base + right, 0%nat) (nth left full 0)
              (add (base + left, 0%nat) (nth right full 0) m))
            base (list_swap full left right).
  Proof.
    intros base full left right m Hrep Hl Hr. unfold list_swap.
    apply arr_rep_write; [ apply arr_rep_write; auto | rewrite upd_length; auto ].
  Qed.

  (* Pointwise reads of a swapped list. *)
  Lemma nth_list_swap_left : forall l i j,
    i < length l -> nth i (list_swap l i j) 0 = nth j l 0.
  Proof.
    intros l i j Hi. unfold list_swap. destruct (Nat.eq_dec i j).
    - subst j. rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
    - rewrite nth_upd_neq by lia. rewrite nth_upd_eq by lia. reflexivity.
  Qed.

  Lemma nth_list_swap_right : forall l i j,
    j < length l -> nth j (list_swap l i j) 0 = nth i l 0.
  Proof.
    intros l i j Hj. unfold list_swap.
    rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
  Qed.

  Lemma nth_list_swap_other : forall l i j k,
    k <> i -> k <> j -> nth k (list_swap l i j) 0 = nth k l 0.
  Proof.
    intros l i j k Hi Hj. unfold list_swap.
    rewrite nth_upd_neq by lia. rewrite nth_upd_neq by lia. reflexivity.
  Qed.

  (* interp_st of swap_arr: read both cells, then write them crossed. *)
  Lemma interp_st_swap_arr : forall base hi full left right (m : @mem nat V),
    arr_rep m base full -> left <= hi -> right <= hi -> hi < length full ->
    interp_st ltu unit
      (swap_arr (E' := E0) (MkSTArray nat S nat base 0 hi) 0 left right) m
    ≈ Ret (add (base + right, 0%nat) (nth left full 0)
             (add (base + left, 0%nat) (nth right full 0) m), tt).
  Proof.
    intros base hi full left right m Hrep Hl Hr Hhl.
    unfold swap_arr.
    etransitivity; [ apply interp_st_bind_eutt |].
    match goal with |- ITree.bind (interp_st ltu nat ?rd ?mm) _ ≈ _ =>
      let H := fresh in
      assert (H : interp_st ltu nat rd mm ≈ Ret (mm, nth left full 0))
        by (apply interp_st_readArray; apply arr_lookup_rep; auto);
      rewrite H end.
    setoid_rewrite bind_Ret_l.
    etransitivity; [ apply interp_st_bind_eutt |].
    match goal with |- ITree.bind (interp_st ltu nat ?rd ?mm) _ ≈ _ =>
      let H := fresh in
      assert (H : interp_st ltu nat rd mm ≈ Ret (mm, nth right full 0))
        by (apply interp_st_readArray; apply arr_lookup_rep; auto);
      rewrite H end.
    setoid_rewrite bind_Ret_l.
    etransitivity; [ apply interp_st_bind_eutt |].
    match goal with |- ITree.bind (interp_st ltu unit ?wr ?mm) _ ≈ _ =>
      let H := fresh in
      assert (H : interp_st ltu unit wr mm
                  ≈ Ret (add (base + left, 0%nat) (nth right full 0) mm, tt))
        by (apply interp_st_writeArray; apply arr_key_val0; lia);
      rewrite H end.
    setoid_rewrite bind_Ret_l.
    match goal with |- interp_st ltu unit ?wr ?mm ≈ _ =>
      let H := fresh in
      assert (H : interp_st ltu unit wr mm
                  ≈ Ret (add (base + right, 0%nat) (nth left full 0) mm, tt))
        by (apply interp_st_writeArray; apply arr_key_val0; lia);
      rewrite H end.
    reflexivity.
  Qed.

  (* Pure model of the Lomuto scan loop. *)
  Fixpoint lomuto (full : list nat) (pv : nat) (is : list nat) (si : nat)
    : list nat * nat :=
    match is with
    | nil => (full, si)
    | i :: rest =>
        if Nat.leb (nth i full 0) pv
        then lomuto (list_swap full i si) pv rest (Datatypes.S si)
        else lomuto full pv rest si
    end.

  (* Swapping two in-bounds positions is a permutation. *)
  Lemma list_swap_perm : forall (l : list nat) i j,
    i < length l -> j < length l -> Permutation l (list_swap l i j).
  Proof.
    intros l i j Hi Hj.
    apply (proj2 (Permutation_nth l (list_swap l i j) 0)).
    split; [ rewrite list_swap_length; reflexivity | ].
    exists (fun x => if Nat.eqb x i then j else if Nat.eqb x j then i else x).
    split; [| split].
    - intros x Hx. destruct (Nat.eqb x i) eqn:E1; [ exact Hj |].
      destruct (Nat.eqb x j) eqn:E2; [ exact Hi | exact Hx ].
    - intros x y Hx Hy Heq.
      destruct (Nat.eqb x i) eqn:E1; destruct (Nat.eqb y i) eqn:F1;
      destruct (Nat.eqb x j) eqn:E2; destruct (Nat.eqb y j) eqn:F2;
      repeat match goal with
      | H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H
      | H : (_ =? _) = false |- _ => apply Nat.eqb_neq in H
      end; subst; try lia.
    - intros x Hx. unfold list_swap.
      destruct (Nat.eqb x i) eqn:E1.
      + apply Nat.eqb_eq in E1. subst x.
        destruct (Nat.eq_dec i j).
        * subst j. rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
        * rewrite nth_upd_neq by lia. rewrite nth_upd_eq by lia. reflexivity.
      + apply Nat.eqb_neq in E1. destruct (Nat.eqb x j) eqn:E2.
        * apply Nat.eqb_eq in E2. subst x.
          rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
        * apply Nat.eqb_neq in E2.
          rewrite nth_upd_neq by lia. rewrite nth_upd_neq by lia. reflexivity.
  Qed.

  (* The Lomuto scan only permutes the list (and preserves its length). *)
  Lemma lomuto_perm : forall is full pv si,
    (forall i, In i is -> i < length full) ->
    si + length is <= length full ->
    Permutation full (fst (lomuto full pv is si))
    /\ length (fst (lomuto full pv is si)) = length full.
  Proof.
    induction is as [|i rest IH]; intros full pv si Hin Hlen.
    - cbn [lomuto fst]. split; reflexivity.
    - cbn [lomuto]. cbn [length] in Hlen.
      assert (Hi : i < length full) by (apply Hin; left; reflexivity).
      destruct (Nat.leb (nth i full 0) pv) eqn:Hle.
      + assert (Hsi : si < length full) by lia.
        edestruct (IH (list_swap full i si) pv (Datatypes.S si)) as [Hp Hl].
        * intros x Hx. rewrite list_swap_length. apply Hin. right. exact Hx.
        * rewrite list_swap_length. lia.
        * rewrite list_swap_length in Hl. split.
          -- etransitivity; [ apply (list_swap_perm full i si Hi Hsi) | exact Hp ].
          -- exact Hl.
      + edestruct (IH full pv si) as [Hp Hl].
        * intros x Hx. apply Hin. right. exact Hx.
        * lia.
        * split; assumption.
  Qed.

  (* The Lomuto scan invariant: scanning the consecutive indices [cur .. cur+cnt)
     from store index [si], with the small region [lo,si) already <= pv and the
     big region [si,cur) already > pv, yields a store index [si'] with
     [lo,si') all <= pv and [si',cur+cnt) all > pv; only [lo,cur+cnt) is touched. *)
  Lemma lomuto_partition : forall cnt lo cur full pv si,
    lo <= si -> si <= cur -> cur + cnt <= length full ->
    (forall j, lo <= j -> j < si -> nth j full 0 <= pv) ->
    (forall j, si <= j -> j < cur -> pv < nth j full 0) ->
    let '(full', si') := lomuto full pv (seq cur cnt) si in
      si <= si'
      /\ si' <= cur + cnt
      /\ (forall j, lo <= j -> j < si' -> nth j full' 0 <= pv)
      /\ (forall j, si' <= j -> j < cur + cnt -> pv < nth j full' 0)
      /\ (forall j, j < lo \/ cur + cnt <= j -> nth j full' 0 = nth j full 0)
      /\ length full' = length full.
  Proof.
    induction cnt as [|cnt' IH];
      intros lo cur full pv si Hlosi Hsicur Hlen Hsmall Hbig.
    - cbn [seq lomuto].
      split; [lia|]. split; [lia|].
      split; [intros j Hlo Hj; apply Hsmall; lia|].
      split; [intros j Hs Hj; apply Hbig; lia|].
      split; [intros j Hj; reflexivity|]. reflexivity.
    - cbn [seq]. cbn [lomuto].
      assert (Hcur : cur < length full) by lia.
      assert (Hsi : si < length full) by lia.
      destruct (Nat.leb (nth cur full 0) pv) eqn:Hle.
      + apply Nat.leb_le in Hle.
        assert (P1 : lo <= Datatypes.S si) by lia.
        assert (P2 : Datatypes.S si <= Datatypes.S cur) by lia.
        assert (P3 : Datatypes.S cur + cnt' <= length (list_swap full cur si))
          by (rewrite list_swap_length; lia).
        assert (P4 : forall j, lo <= j -> j < Datatypes.S si ->
                     nth j (list_swap full cur si) 0 <= pv).
        { intros j Hlo Hj. unfold list_swap. destruct (Nat.eq_dec j si).
          - subst j. rewrite nth_upd_eq by (rewrite upd_length; lia). exact Hle.
          - rewrite nth_upd_neq by lia. rewrite nth_upd_neq by lia.
            apply Hsmall; lia. }
        assert (P5 : forall j, Datatypes.S si <= j -> j < Datatypes.S cur ->
                     pv < nth j (list_swap full cur si) 0).
        { intros j Hj1 Hj2. unfold list_swap. destruct (Nat.eq_dec j cur).
          - subst j. rewrite nth_upd_neq by lia.
            rewrite nth_upd_eq by lia. apply Hbig; lia.
          - rewrite nth_upd_neq by lia. rewrite nth_upd_neq by lia.
            apply Hbig; lia. }
        specialize (IH lo (Datatypes.S cur) (list_swap full cur si) pv
                       (Datatypes.S si) P1 P2 P3 P4 P5).
        set (res := lomuto (list_swap full cur si) pv (seq (Datatypes.S cur) cnt')
                           (Datatypes.S si)) in *.
        destruct res as [full' si'].
        destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
        split; [lia|]. split; [lia|]. split; [exact I3|].
        split; [intros j Hj1 Hj2; apply I4; lia|].
        split.
        { intros j Hj. rewrite I5 by lia. unfold list_swap.
          rewrite nth_upd_neq by lia. rewrite nth_upd_neq by lia. reflexivity. }
        rewrite I6. apply list_swap_length.
      + apply Nat.leb_gt in Hle.
        assert (P1 : lo <= si) by lia.
        assert (P2 : si <= Datatypes.S cur) by lia.
        assert (P3 : Datatypes.S cur + cnt' <= length full) by lia.
        assert (P4 : forall j, lo <= j -> j < si -> nth j full 0 <= pv)
          by (intros; apply Hsmall; lia).
        assert (P5 : forall j, si <= j -> j < Datatypes.S cur -> pv < nth j full 0).
        { intros j Hj1 Hj2. destruct (Nat.eq_dec j cur).
          - subst j. exact Hle.
          - apply Hbig; lia. }
        specialize (IH lo (Datatypes.S cur) full pv si P1 P2 P3 P4 P5).
        set (res := lomuto full pv (seq (Datatypes.S cur) cnt') si) in *.
        destruct res as [full' si'].
        destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
        split; [lia|]. split; [lia|]. split; [exact I3|].
        split; [intros j Hj1 Hj2; apply I4; lia|].
        split; [intros j Hj; rewrite I5 by lia; reflexivity|].
        exact I6.
  Qed.

  (* The scan loop's interp_st effect matches [lomuto] on the list model. *)
  Lemma interp_st_lomuto_loop :
    forall (is : list nat) base hi pv full si (m : @mem nat V),
      arr_rep m base full -> hi < length full ->
      (forall i, In i is -> i <= hi) -> si + length is <= Datatypes.S hi ->
      exists m',
        interp_st ltu nat
          (for_each_with (E' := E0) is si
             (fun storeIndex i =>
                val <- @readArray E0 nat _ _ _ _ 0 (MkSTArray nat S nat base 0 hi) i ;;
                if Nat.leb val pv
                then swap_arr (MkSTArray nat S nat base 0 hi) 0 i storeIndex ;;
                     Ret (Datatypes.S storeIndex)
                else Ret storeIndex)) m
        ≈ Ret (m', snd (lomuto full pv is si))
        /\ arr_rep m' base (fst (lomuto full pv is si)).
  Proof.
    induction is as [|i rest IH];
      intros base hi pv full si m Hrep Hhl Hin Hsi.
    - (* empty scan *)
      exists m. cbn [for_each_with lomuto fst snd]. split.
      + apply interp_st_Ret_eutt.
      + exact Hrep.
    - (* i :: rest *)
      assert (Hi : i <= hi) by (apply Hin; left; reflexivity).
      cbn [length] in Hsi.
      assert (Hsib : si <= hi) by lia.
      cbn [for_each_with lomuto].
      destruct (Nat.leb (nth i full 0) pv) eqn:Hle.
      + (* swapped; recurse on list_swap, S si *)
        edestruct (IH base hi pv (list_swap full i si) (Datatypes.S si)
                     (add (base + si, 0%nat) (nth i full 0)
                        (add (base + i, 0%nat) (nth si full 0) m)))
          as [m' [Hrun Hrep']].
        * apply arr_rep_swap; auto; lia.
        * unfold list_swap. rewrite !upd_length. lia.
        * intros x Hx. apply Hin; right; auto.
        * lia.
        * exists m'. split; [| exact Hrep'].
          (* reduce the body [val <- readArray i ;; swap ;; Ret (S si)] *)
          etransitivity; [ apply interp_st_bind_eutt |].
          match goal with |- ITree.bind (interp_st ltu nat ?b ?mm) _ ≈ _ =>
            assert (Hb : interp_st ltu nat b mm
                         ≈ Ret (add (base + si, 0%nat) (nth i full 0)
                                  (add (base + i, 0%nat) (nth si full 0) mm),
                                Datatypes.S si)) end.
          { change (V 0) with nat.
            etransitivity; [ apply interp_st_bind_eutt |].
            match goal with |- ITree.bind (interp_st ltu ?R ?rd ?mm) _ ≈ _ =>
              let Hr := fresh in
              assert (Hr : interp_st ltu R rd mm ≈ Ret (mm, nth i full 0))
                by (apply interp_st_readArray; apply arr_lookup_rep; auto; lia);
              rewrite Hr end.
            setoid_rewrite bind_Ret_l. rewrite Hle.
            etransitivity; [ apply interp_st_bind_eutt |].
            match goal with |- ITree.bind (interp_st ltu unit ?sw ?mm) _ ≈ _ =>
              let Hs := fresh in
              assert (Hs : interp_st ltu unit sw mm
                           ≈ Ret (add (base + si, 0%nat) (nth i full 0)
                                    (add (base + i, 0%nat) (nth si full 0) mm), tt))
                by (apply interp_st_swap_arr; auto; lia);
              rewrite Hs end.
            setoid_rewrite bind_Ret_l. apply interp_st_Ret_eutt. }
          rewrite Hb. setoid_rewrite bind_Ret_l. exact Hrun.
      + (* not swapped; recurse on full, si *)
        edestruct (IH base hi pv full si m) as [m' [Hrun Hrep']].
        * exact Hrep.
        * exact Hhl.
        * intros x Hx. apply Hin; right; auto.
        * lia.
        * exists m'. split; [| exact Hrep'].
          (* reduce the body [val <- readArray i ;; Ret si] *)
          etransitivity; [ apply interp_st_bind_eutt |].
          match goal with |- ITree.bind (interp_st ltu nat ?b ?mm) _ ≈ _ =>
            assert (Hb : interp_st ltu nat b mm ≈ Ret (mm, si)) end.
          { change (V 0) with nat.
            etransitivity; [ apply interp_st_bind_eutt |].
            match goal with |- ITree.bind (interp_st ltu ?R ?rd ?mm) _ ≈ _ =>
              let Hr := fresh in
              assert (Hr : interp_st ltu R rd mm ≈ Ret (mm, nth i full 0))
                by (apply interp_st_readArray; apply arr_lookup_rep; auto; lia);
              rewrite Hr end.
            setoid_rewrite bind_Ret_l. rewrite Hle. apply interp_st_Ret_eutt. }
          rewrite Hb. setoid_rewrite bind_Ret_l. exact Hrun.
  Qed.

  Transparent add lookup STRefToIx zero suc.

  (* The index range scanned by partition is exactly [seq lo (hi - lo)]. *)
  Lemma range_seq_sub : forall lo hi, lo < hi ->
    range lo (sub hi (suc zero)) = seq lo (hi - lo).
  Proof. intros lo hi H. cbn [range sub suc zero nat_ix]. f_equal. lia. Qed.

  (* Correctness of the in-place [partition]: it permutes the segment [lo,hi],
     leaves everything outside untouched, and returns a pivot position [p] with
     the standard partition invariant. *)
  Lemma interp_st_partition :
    forall (base hi_arr lo hi pividx : nat) (full : list nat) (m : @mem nat V),
      arr_rep m base full ->
      lo < hi -> hi <= hi_arr -> hi_arr < length full ->
      lo <= pividx -> pividx <= hi ->
      exists m' full' p,
        interp_st ltu nat
          (@partition nat S ltu _ _ E0 _ _ (MkSTArray nat S nat base 0 hi_arr) 0 lo hi pividx) m
        ≈ Ret (m', p)
        /\ arr_rep m' base full'
        /\ length full' = length full
        /\ Permutation full full'
        /\ (forall j, j < lo \/ hi < j -> nth j full' 0 = nth j full 0)
        /\ lo <= p /\ p <= hi
        /\ (forall j, lo <= j -> j < p -> nth j full' 0 <= nth p full' 0)
        /\ (forall j, p < j -> j <= hi -> nth p full' 0 <= nth j full' 0).
  Proof.
    intros base hi_arr lo hi pividx full m Hrep Hlohi Hhia Hlen Hlop Hpvh.
    assert (Hpivlt : pividx < length full) by lia.
    assert (Hhilt : hi < length full) by lia.
    remember (list_swap full pividx hi) as full_a eqn:Hfa.
    assert (Hlen_a : length full_a = length full)
      by (rewrite Hfa; apply list_swap_length).
    (* --- pure model of the scan --- *)
    pose proof (lomuto_partition (hi - lo) lo lo full_a (nth pividx full 0) lo) as Hlp.
    assert (Hpre3 : lo + (hi - lo) <= length full_a) by (rewrite Hlen_a; lia).
    specialize (Hlp (le_n _) (le_n _) Hpre3
                    ltac:(intros j A B; lia) ltac:(intros j A B; lia)).
    pose proof (lomuto_perm (seq lo (hi - lo)) full_a (nth pividx full 0) lo) as Hpb.
    assert (Hins : forall i, In i (seq lo (hi - lo)) -> i < length full_a)
      by (intros i Hi; apply in_seq in Hi; rewrite Hlen_a; lia).
    assert (Hsql : lo + length (seq lo (hi - lo)) <= length full_a)
      by (rewrite length_seq, Hlen_a; lia).
    specialize (Hpb Hins Hsql).
    destruct (lomuto full_a (nth pividx full 0) (seq lo (hi - lo)) lo)
      as [full_b storeIndex] eqn:ELB.
    cbn [fst snd] in Hlp, Hpb.
    destruct Hlp as (Hst1 & Hst2 & Hsmall_b & Hbig_b & Hunch_b & Hlenlp).
    destruct Hpb as (Hpermb & Hlen_b).
    assert (Hst2' : storeIndex <= hi) by lia.
    assert (Hstore_lt : storeIndex < length full_b)
      by (rewrite Hlen_b, Hlen_a; lia).
    assert (Hhi_ltb : hi < length full_b) by (rewrite Hlen_b, Hlen_a; lia).
    (* pivot value ends up at [storeIndex] after the final swap *)
    assert (Hnp : nth storeIndex (list_swap full_b storeIndex hi) 0 = nth pividx full 0).
    { rewrite nth_list_swap_left by exact Hstore_lt.
      rewrite (Hunch_b hi) by lia. rewrite Hfa.
      rewrite nth_list_swap_right by lia. reflexivity. }
    (* --- interp_st plumbing --- *)
    set (m_a := add (base + hi, 0%nat) (nth pividx full 0)
                  (add (base + pividx, 0%nat) (nth hi full 0) m)).
    assert (Hrep_a : arr_rep m_a base full_a)
      by (rewrite Hfa; apply arr_rep_swap; [exact Hrep | lia | lia]).
    edestruct (interp_st_lomuto_loop (seq lo (hi - lo)) base hi_arr
                 (nth pividx full 0) full_a lo m_a) as [m_loop [Hloop Hrep_loop]].
    { exact Hrep_a. }
    { rewrite Hlen_a. lia. }
    { intros i Hi. apply in_seq in Hi. lia. }
    { rewrite length_seq. lia. }
    rewrite ELB in Hloop, Hrep_loop. cbn [fst snd] in Hloop, Hrep_loop.
    (* assemble the whole interp equation *)
    assert (Hpart :
      interp_st ltu nat
        (@partition nat S ltu _ _ E0 _ _ (MkSTArray nat S nat base 0 hi_arr) 0 lo hi pividx) m
      ≈ Ret (add (base + hi, 0%nat) (nth storeIndex full_b 0)
               (add (base + storeIndex, 0%nat) (nth hi full_b 0) m_loop), storeIndex)).
    { unfold partition.
      (* normalise the index operations to plain [seq]/[S] *)
      cbn [range sub suc zero nat_ix].
      match goal with |- context[seq lo ?n] => replace n with (hi - lo) by lia end.
      (* read pivot *)
      etransitivity; [ apply interp_st_bind_eutt |]. change (V 0) with nat.
      match goal with |- ITree.bind (interp_st ltu ?R ?rd ?mm) _ ≈ _ =>
        assert (Hread : interp_st ltu R rd mm ≈ Ret (mm, nth pividx full 0))
          by (apply interp_st_readArray; apply arr_lookup_rep; [exact Hrep | lia | lia]);
        rewrite Hread end.
      setoid_rewrite bind_Ret_l.
      (* swap pivot to hi *)
      etransitivity; [ apply interp_st_bind_eutt |].
      match goal with |- ITree.bind (interp_st ltu unit ?sw ?mm) _ ≈ _ =>
        assert (Hsw1 : interp_st ltu unit sw mm ≈ Ret (m_a, tt))
          by (apply interp_st_swap_arr; [exact Hrep | lia | lia | lia]);
        rewrite Hsw1 end.
      setoid_rewrite bind_Ret_l.
      (* the scan loop (matched up to conversion to bridge the Ix instance) *)
      etransitivity; [ apply interp_st_bind_eutt |].
      match goal with |- ITree.bind (interp_st ltu nat ?loop ?mm) _ ≈ _ =>
        assert (Hl2 : interp_st ltu nat loop mm ≈ Ret (m_loop, storeIndex))
          by (exact Hloop) end.
      rewrite Hl2. setoid_rewrite bind_Ret_l.
      (* swap pivot to its final position *)
      etransitivity; [ apply interp_st_bind_eutt |].
      match goal with |- ITree.bind (interp_st ltu unit ?sw ?mm) _ ≈ _ =>
        assert (Hsw2 : interp_st ltu unit sw mm
                       ≈ Ret (add (base + hi, 0%nat) (nth storeIndex full_b 0)
                                (add (base + storeIndex, 0%nat) (nth hi full_b 0) mm), tt))
          by (apply interp_st_swap_arr; [exact Hrep_loop | lia | lia | lia]);
        rewrite Hsw2 end.
      setoid_rewrite bind_Ret_l.
      apply interp_st_Ret_eutt. }
    (* --- provide witnesses and discharge the properties --- *)
    eexists. exists (list_swap full_b storeIndex hi). exists storeIndex.
    split; [ exact Hpart |].
    split.
    { apply arr_rep_swap; [ exact Hrep_loop | exact Hstore_lt | exact Hhi_ltb ]. }
    split.
    { rewrite list_swap_length, Hlen_b, Hlen_a. reflexivity. }
    split.
    { etransitivity; [ apply (list_swap_perm full pividx hi); lia | ].
      rewrite <- Hfa.
      etransitivity; [ exact Hpermb | ].
      apply (list_swap_perm full_b storeIndex hi); [ exact Hstore_lt | exact Hhi_ltb ]. }
    split.
    { intros j Hj. rewrite nth_list_swap_other by lia.
      rewrite (Hunch_b j) by lia. rewrite Hfa.
      rewrite nth_list_swap_other by lia. reflexivity. }
    split; [ exact Hst1 |].
    split; [ exact Hst2' |].
    split.
    { intros j Hjlo Hjp. rewrite Hnp. rewrite nth_list_swap_other by lia.
      apply Hsmall_b; lia. }
    { intros j Hjp Hjhi. rewrite Hnp. destruct (Nat.eq_dec j hi).
      - subst j. rewrite nth_list_swap_right by exact Hhi_ltb.
        apply Nat.lt_le_incl. apply Hbig_b; lia.
      - rewrite nth_list_swap_other by lia.
        apply Nat.lt_le_incl. apply Hbig_b; lia. }
  Qed.

  (* ===================================================================== *)
  (* Unfolding the [rec]/[mrec] recursion of [quicksort_ST] to E0 level.    *)
  (* ===================================================================== *)

  Let ED := (callE (STArray nat S nat * nat * nat * nat) unit +' E0).

  Lemma interp_rec_bind {R Sr : Type}
    (t : itree ED R) (k : R -> itree ED Sr) :
    interp (recursive quicksort_ST_body) (ITree.bind t k)
    ≈ ITree.bind (interp (recursive quicksort_ST_body) t)
        (fun r => interp (recursive quicksort_ST_body) (k r)).
  Proof. unfold ED, E0, V, T, ltu. rewrite interp_bind. reflexivity. Qed.

  Lemma interp_rec_readArray (idx : nat) (arr : STArray nat S nat) (i : nat) :
    interp (recursive quicksort_ST_body) (readArray (E := ED) (idx := idx) arr i)
    ≈ readArray (E := E0) (idx := idx) arr i.
  Proof.
    unfold readArray, ED, E0, V, T, ltu. rewrite interp_trigger. cbn. reflexivity.
  Qed.

  Lemma interp_rec_writeArray (idx : nat) (arr : STArray nat S nat) (i v : nat) :
    interp (recursive quicksort_ST_body) (writeArray (E := ED) (idx := idx) arr i v)
    ≈ writeArray (E := E0) (idx := idx) arr i v.
  Proof.
    unfold writeArray, ED, E0, V, T, ltu. rewrite interp_trigger. cbn. reflexivity.
  Qed.

  Lemma interp_rec_ret {R} (x : R) :
    interp (recursive quicksort_ST_body) (Ret x : itree ED R) ≈ Ret x.
  Proof.
    unfold ED, E0, V, T, ltu. rewrite interp_ret. reflexivity.
  Qed.

  Lemma interp_rec_swap_arr (arr : STArray nat S nat) (arr_idx left right : nat) :
    interp (recursive quicksort_ST_body) (swap_arr (E' := ED) arr arr_idx left right)
    ≈ swap_arr (E' := E0) arr arr_idx left right.
  Proof.
    unfold swap_arr.
    rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_readArray | intros leftVal ].
    rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_readArray | intros rightVal ].
    rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_writeArray | intros _ ].
    apply interp_rec_writeArray.
  Qed.

  Lemma interp_rec_for_each_with {A B} (xs : list A) (v : B)
    (fED : B -> A -> itree ED B) (fE0 : B -> A -> itree E0 B) :
    (forall b a, interp (recursive quicksort_ST_body) (fED b a) ≈ fE0 b a) ->
    interp (recursive quicksort_ST_body) (for_each_with (E' := ED) xs v fED)
    ≈ for_each_with (E' := E0) xs v fE0.
  Proof.
    revert v. induction xs as [|h t IH]; intros v Hf.
    - cbn [for_each_with]. apply interp_rec_ret.
    - cbn [for_each_with].
      rewrite interp_rec_bind. apply eutt_eq_bind'.
      + apply Hf.
      + intros v'. apply IH. exact Hf.
  Qed.

  Lemma partition_interp_id :
    forall (arr : STArray nat S nat) (arr_idx l r pv : nat),
      interp (recursive quicksort_ST_body)
        (@partition nat S ltu _ _ ED _ _ arr arr_idx l r pv)
      ≈ @partition nat S ltu _ _ E0 _ _ arr arr_idx l r pv.
  Proof.
    intros. unfold partition.
    rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_readArray | intros pivotValue ].
    rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_swap_arr | intros _ ].
    rewrite interp_rec_bind. apply eutt_eq_bind'.
    { apply interp_rec_for_each_with. intros b a.
      rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_readArray | intros val ].
      destruct (Nat.leb val pivotValue).
      - cbn beta iota.
        rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_swap_arr | intros _ ].
        apply interp_rec_ret.
      - apply interp_rec_ret. }
    intros storeIndex.
    rewrite interp_rec_bind. apply eutt_eq_bind'; [ apply interp_rec_swap_arr | intros _ ].
    apply interp_rec_ret.
  Qed.

  (* E0-level unfolding of the [rec]/[mrec] recursion. *)
  Lemma quicksort_ST_unfold :
    forall (arr : STArray nat S nat) (arr_idx l r : nat),
      quicksort_ST arr arr_idx l r
      ≈ (if Nat.ltb (toNat l) (toNat r)
         then newPivot <- partition arr arr_idx l r
                            (fromNat (toNat l + (toNat r - toNat l) / 2)) ;;
              quicksort_ST arr arr_idx l (fromNat (toNat newPivot - 1)) ;;
              quicksort_ST arr arr_idx (fromNat (toNat newPivot + 1)) r
         else Ret tt).
  Proof.
    intros arr arr_idx l r.
    unfold quicksort_ST at 1.
    rewrite rec_as_interp.
    unfold quicksort_ST_body at 2.
    cbn match.
    destruct (Nat.ltb (toNat l) (toNat r)) eqn:Hlt.
    - rewrite interp_bind.
      apply eutt_eq_bind'.
      + apply partition_interp_id.
      + intros np.
        rewrite interp_bind.
        apply eutt_eq_bind'.
        * rewrite interp_recursive_call. unfold quicksort_ST. reflexivity.
        * intros _.
          rewrite interp_recursive_call. unfold quicksort_ST. reflexivity.
    - rewrite interp_ret. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* Segment machinery: permutation + pairwise-sortedness of a sub-range.   *)
  (* ===================================================================== *)

  Definition seg (l : list nat) (a b : nat) : list nat :=
    firstn (Datatypes.S b - a) (skipn a l).

  Lemma nth_seg : forall l a b k,
    k < Datatypes.S b - a -> nth k (seg l a b) 0 = nth (a + k) l 0.
  Proof.
    intros l a b k Hk. unfold seg. rewrite nth_firstn.
    destruct (k <? Datatypes.S b - a) eqn:E.
    - rewrite nth_skipn. reflexivity.
    - apply Nat.ltb_ge in E. lia.
  Qed.

  Lemma length_seg : forall l a b,
    b < length l -> length (seg l a b) = Datatypes.S b - a.
  Proof. intros l a b Hb. unfold seg. rewrite length_firstn, length_skipn. lia. Qed.

  Lemma seg_decomp : forall l a b, a <= Datatypes.S b ->
    l = firstn a l ++ seg l a b ++ skipn (Datatypes.S b) l.
  Proof.
    intros l a b Hab. unfold seg.
    transitivity (firstn a l ++ skipn a l); [ symmetry; apply firstn_skipn |].
    f_equal.
    transitivity (firstn (Datatypes.S b - a) (skipn a l)
                  ++ skipn (Datatypes.S b - a) (skipn a l));
      [ symmetry; apply firstn_skipn |].
    f_equal. rewrite skipn_skipn. f_equal. lia.
  Qed.

  Lemma seg_perm : forall full full' a b,
    Permutation full full' -> length full' = length full ->
    b < length full -> a <= Datatypes.S b ->
    (forall j, j < a \/ b < j -> nth j full' 0 = nth j full 0) ->
    Permutation (seg full a b) (seg full' a b).
  Proof.
    intros full full' a b Hperm Hlen Hb Hab Hunch.
    assert (Hpre : firstn a full = firstn a full').
    { apply nth_ext with (d := 0) (d' := 0).
      - rewrite !length_firstn. lia.
      - intros n Hn. rewrite length_firstn in Hn. rewrite !nth_firstn.
        destruct (n <? a) eqn:E; [| reflexivity].
        apply Nat.ltb_lt in E. symmetry. apply Hunch. left. lia. }
    assert (Hsuf : skipn (Datatypes.S b) full = skipn (Datatypes.S b) full').
    { apply nth_ext with (d := 0) (d' := 0).
      - rewrite !length_skipn. lia.
      - intros n Hn. rewrite length_skipn in Hn. rewrite !nth_skipn.
        symmetry. apply Hunch. right. lia. }
    pose proof (seg_decomp full a b Hab) as Df.
    pose proof (seg_decomp full' a b Hab) as Df'.
    rewrite Df, Df' in Hperm. rewrite <- Hpre in Hperm.
    apply Permutation_app_inv_l in Hperm. rewrite <- Hsuf in Hperm.
    apply Permutation_app_inv_r in Hperm. exact Hperm.
  Qed.

  (* A pointwise property over a segment is preserved by a permutation that
     leaves everything outside the segment fixed. *)
  Lemma seg_forall_perm : forall (P : nat -> Prop) full full' a b,
    Permutation full full' -> length full' = length full ->
    b < length full -> a <= Datatypes.S b ->
    (forall j, j < a \/ b < j -> nth j full' 0 = nth j full 0) ->
    (forall j, a <= j -> j <= b -> P (nth j full 0)) ->
    (forall j, a <= j -> j <= b -> P (nth j full' 0)).
  Proof.
    intros P full full' a b Hperm Hlen Hb Hab Hunch Hall j Hj1 Hj2.
    assert (Hjseg : nth j full' 0 = nth (j - a) (seg full' a b) 0)
      by (rewrite nth_seg by lia; f_equal; lia).
    rewrite Hjseg.
    assert (HIn : In (nth (j - a) (seg full' a b) 0) (seg full' a b))
      by (apply nth_In; rewrite length_seg by (rewrite Hlen; lia); lia).
    eapply Permutation_in in HIn;
      [| apply Permutation_sym; apply (seg_perm full full' a b Hperm Hlen Hb Hab Hunch)].
    apply In_nth with (d := 0) in HIn. destruct HIn as [k [Hk Hkeq]].
    rewrite length_seg in Hk by lia.
    rewrite <- Hkeq. rewrite nth_seg by lia. apply Hall; lia.
  Qed.

  (* Pairwise-sortedness of a sub-range. *)
  Definition SortedSeg (l : list nat) (lo hi : nat) : Prop :=
    forall a b, lo <= a -> a <= b -> b <= hi -> nth a l 0 <= nth b l 0.

  Lemma SortedSeg_StronglySorted : forall l,
    (forall i j, i <= j -> j < length l -> nth i l 0 <= nth j l 0) ->
    StronglySorted le l.
  Proof.
    induction l as [|x xs IH]; intros H.
    - constructor.
    - constructor.
      + apply IH. intros i j Hij Hjl.
        specialize (H (Datatypes.S i) (Datatypes.S j) ltac:(lia) ltac:(simpl; lia)).
        simpl in H. exact H.
      + apply Forall_forall. intros y Hy. apply In_nth with (d := 0) in Hy.
        destruct Hy as [k [Hk Hkeq]].
        specialize (H 0 (Datatypes.S k) ltac:(lia) ltac:(simpl; lia)).
        simpl in H. rewrite <- Hkeq. exact H.
  Qed.

  (* ===================================================================== *)
  (* In-place quicksort correctness: the segment [lo,hi] is sorted, the     *)
  (* whole array is permuted, and everything outside [lo,hi] is untouched.  *)
  (* Strong induction on the measure [d >= hi - lo].                        *)
  (* ===================================================================== *)
  Lemma quicksort_ST_segment : forall base d lo hi full m,
    arr_rep m base full -> hi < length full -> hi - lo <= d ->
    exists m' full',
      interp_st ltu unit
        (quicksort_ST (MkSTArray nat S nat base 0 (length full - 1)) 0 lo hi) m
        ≈ Ret (m', tt)
      /\ arr_rep m' base full'
      /\ length full' = length full
      /\ Permutation full full'
      /\ (forall j, j < lo \/ hi < j -> nth j full' 0 = nth j full 0)
      /\ SortedSeg full' lo hi
      /\ (hi <= lo -> full' = full).
  Proof.
    intros base. induction d as [|d IH]; intros lo hi full m Hrep Hhl Hd.
    - (* d = 0 forces hi <= lo *)
      exists m, full.
      rewrite quicksort_ST_unfold. cbn [toNat fromNat nat_ix].
      destruct (Nat.ltb lo hi) eqn:Hlt;
        [ apply Nat.ltb_lt in Hlt; exfalso; lia |].
      split; [ apply interp_st_Ret_eutt |]. split; [ exact Hrep |].
      split; [ reflexivity |]. split; [ apply Permutation_refl |].
      split; [ intros; reflexivity |].
      split; [ intros a b Ha Hab Hb; assert (a = b) by lia; subst b; apply Nat.le_refl |].
      intros; reflexivity.
    - destruct (le_gt_dec hi lo) as [Hle | Hgt].
      + (* hi <= lo: nothing to do *)
        exists m, full.
        rewrite quicksort_ST_unfold. cbn [toNat fromNat nat_ix].
        destruct (Nat.ltb lo hi) eqn:Hlt;
          [ apply Nat.ltb_lt in Hlt; exfalso; lia |].
        split; [ apply interp_st_Ret_eutt |]. split; [ exact Hrep |].
        split; [ reflexivity |]. split; [ apply Permutation_refl |].
        split; [ intros; reflexivity |].
        split; [ intros a b Ha Hab Hb; assert (a = b) by lia; subst b; apply Nat.le_refl |].
        intros; reflexivity.
      + (* lo < hi *)
        assert (Hlo_hi : lo < hi) by lia.
        assert (Hdiv : (hi - lo) / 2 <= hi - lo)
          by (apply Nat.Div0.div_le_upper_bound; lia).
        set (pividx := lo + (hi - lo) / 2).
        assert (Hpiv_lo : lo <= pividx) by (unfold pividx; lia).
        assert (Hpiv_hi : pividx <= hi) by (unfold pividx; lia).
        edestruct (interp_st_partition base (length full - 1) lo hi pividx full m)
          as (m1 & full1 & p & Hpart & Hrep1 & Hlen1 & Hperm1 & Hunch1 &
              Hp_lo & Hp_hi & Hleft & Hright).
        { exact Hrep. } { exact Hlo_hi. } { lia. } { lia. }
        { exact Hpiv_lo. } { exact Hpiv_hi. }
        edestruct (IH lo (p - 1) full1 m1)
          as (m2 & full2 & Hrun1 & Hrep2 & Hlen2 & Hperm2 & Hunch2 & Hsort2 & Hnoop1).
        { exact Hrep1. } { lia. } { lia. }
        edestruct (IH (p + 1) hi full2 m2)
          as (m3 & full3 & Hrun2 & Hrep3 & Hlen3 & Hperm3 & Hunch3 & Hsort3 & Hnoop2).
        { exact Hrep2. } { lia. } { lia. }
        (* run equation *)
        assert (Hrun : interp_st ltu unit
                  (quicksort_ST (MkSTArray nat S nat base 0 (length full - 1)) 0 lo hi) m
                ≈ Ret (m3, tt)).
        { rewrite quicksort_ST_unfold. cbn [toNat fromNat nat_ix].
          destruct (Nat.ltb lo hi) eqn:Hlt;
            [| apply Nat.ltb_ge in Hlt; exfalso; lia ].
          (* partition: reduce head via [eutt_eq_bind'] (universe-tolerant) *)
          etransitivity; [ apply interp_st_bind_eutt |].
          match goal with |- ITree.bind ?t ?k ≈ _ =>
            transitivity (ITree.bind (Ret (m1, p)) k);
              [ apply eutt_eq_bind'; [ exact Hpart | intros u; reflexivity ] |] end.
          setoid_rewrite bind_Ret_l.
          (* first recursive call *)
          etransitivity; [ apply interp_st_bind_eutt |].
          match goal with |- ITree.bind ?t ?k ≈ _ =>
            transitivity (ITree.bind (Ret (m2, tt)) k);
              [ apply eutt_eq_bind';
                [ rewrite Hlen1 in Hrun1; exact Hrun1 | intros u; reflexivity ] |] end.
          setoid_rewrite bind_Ret_l.
          (* second recursive call *)
          rewrite Hlen2, Hlen1 in Hrun2. exact Hrun2. }
        exists m3, full3.
        split; [ exact Hrun |]. split; [ exact Hrep3 |].
        split; [ rewrite Hlen3, Hlen2, Hlen1; reflexivity |].
        split; [ etransitivity; [ exact Hperm1 |];
                 etransitivity; [ exact Hperm2 | exact Hperm3 ] |].
        split.
        { intros j Hj. rewrite (Hunch3 j) by lia. rewrite (Hunch2 j) by lia.
          apply Hunch1; lia. }
        (* SortedSeg full3 lo hi *)
        remember (nth p full1 0) as pivot eqn:Hpv.
        assert (F2' : forall j, j <= p -> nth j full3 0 = nth j full2 0)
          by (intros j Hj; apply Hunch3; lia).
        assert (F1 : nth p full3 0 = pivot).
        { rewrite F2' by lia. rewrite Hpv.
          destruct (Nat.eq_dec p 0) as [Hp0 | Hpn0].
          - rewrite Hnoop1 by lia. reflexivity.
          - apply Hunch2. lia. }
        assert (F4 : forall j, lo <= j -> j < p -> nth j full3 0 <= pivot).
        { intros j Hjlo Hjp. rewrite F2' by lia.
          apply (seg_forall_perm (fun x => x <= pivot) full1 full2 lo (p - 1));
            [ exact Hperm2 | exact Hlen2 | lia | lia | exact Hunch2 | | lia | lia ].
          intros k Hk1 Hk2. apply Hleft; lia. }
        assert (F5 : forall j, p < j -> j <= hi -> pivot <= nth j full3 0).
        { intros j Hjp Hjhi.
          apply (seg_forall_perm (fun x => pivot <= x) full2 full3 (p + 1) hi);
            [ exact Hperm3 | exact Hlen3 | lia | lia | exact Hunch3 | | lia | lia ].
          intros k Hk1 Hk2. rewrite (Hunch2 k) by lia. apply Hright; lia. }
        split.
        { intros a b Ha Hab Hb.
          destruct (lt_eq_lt_dec a p) as [[Ha_lt | Ha_eq] | Ha_gt];
            destruct (lt_eq_lt_dec b p) as [[Hb_lt | Hb_eq] | Hb_gt].
          * rewrite (F2' a) by lia. rewrite (F2' b) by lia. apply Hsort2; lia.
          * subst b. rewrite F1. apply F4; lia.
          * apply Nat.le_trans with pivot; [ apply F4; lia | apply F5; lia ].
          * exfalso; lia.
          * subst a; subst b. apply Nat.le_refl.
          * subst a. rewrite F1. apply F5; lia.
          * exfalso; lia.
          * exfalso; lia.
          * apply Hsort3; lia. }
        intros Hcontra; exfalso; lia.
  Qed.

  Lemma map_nth_seq_gen : forall (l pre : list nat),
    List.map (fun p => nth p (pre ++ l) 0) (seq (length pre) (length l)) = l.
  Proof.
    induction l as [|a l IH]; intros pre; simpl.
    - reflexivity.
    - f_equal.
      + rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
      + specialize (IH (pre ++ [a])).
        rewrite <- app_assoc in IH. cbn [app] in IH.
        rewrite length_app in IH. cbn [length] in IH.
        replace (length pre + 1) with (Datatypes.S (length pre)) in IH by lia.
        exact IH.
  Qed.

  Lemma map_nth_seq : forall (l : list nat),
    List.map (fun p => nth p l 0) (seq 0 (length l)) = l.
  Proof. intro l. apply (map_nth_seq_gen l []). Qed.

  (* [getElems] reads the whole array back as the represented list. *)
  Lemma interp_st_getElems : forall base hi full (m : @mem nat V),
    arr_rep m base full -> length full = Datatypes.S hi ->
    interp_st ltu (list nat)
      (@getElems E0 nat _ _ _ _ 0 (MkSTArray nat S nat base 0 hi)) m
    ≈ Ret (m, full).
  Proof.
    intros base hi full m Hrep Hlen.
    unfold getElems, E0, V, T. rewrite interp_st_trigger.
    cbn -[arr_lookup range Nat.sub].
    match goal with |- context[?c (range 0 hi)] =>
      assert (Hgen : forall ps, (forall q, In q ps -> q <= hi) ->
               c ps = Some (List.map (fun q => nth q full 0) ps)) end.
    { intros ps. induction ps as [|q rest IHps]; intros Hall.
      - reflexivity.
      - cbn -[arr_lookup].
        match goal with |- context[?al] =>
          match al with
          | arr_lookup _ _ _ _ _ =>
            assert (Hal : al = Some (nth q full 0))
              by (apply arr_lookup_rep;
                  [ exact Hrep | apply Hall; left; reflexivity | lia ]);
            rewrite Hal
          end
        end.
        rewrite IHps by (intros q' Hq'; apply Hall; right; exact Hq').
        reflexivity. }
    rewrite Hgen by (intros q Hq; cbn [range nat_ix] in Hq; apply in_seq in Hq; lia).
    cbn [range nat_ix].
    match goal with |- context[seq 0 ?n] => replace n with (length full) by lia end.
    rewrite map_nth_seq. reflexivity.
  Qed.

  (* External model of the handler's list-array [fill] loop. *)
  Fixpoint fill_ext (es : list (V 0)) (m0 : @mem nat V) (k : nat) : @mem nat V * nat :=
    match es with
    | [] => (m0, k)
    | v :: rest => fill_ext rest (add (k, 0%nat) v m0) (Datatypes.S k)
    end.

  Lemma fill_ext_below : forall es (m0 : @mem nat V) k j,
    j < k -> lookup (j, 0%nat) (fst (fill_ext es m0 k)) = lookup (j, 0%nat) m0.
  Proof.
    induction es as [|v rest IH]; intros m0 k j Hj; cbn [fill_ext fst].
    - reflexivity.
    - rewrite IH by lia.
      apply (hmap_lookup_add_ne (j, 0%nat) (k, 0%nat) v m0). intros [=]; lia.
  Qed.

  Lemma fill_ext_at : forall es (m0 : @mem nat V) k i,
    i < length es ->
    lookup (k + i, 0%nat) (fst (fill_ext es m0 k)) = Some (nth i es 0).
  Proof.
    induction es as [|v rest IH]; intros m0 k i Hi; cbn [length] in Hi.
    - lia.
    - cbn [fill_ext fst]. destruct i as [|i'].
      + rewrite Nat.add_0_r.
        etransitivity;
          [ apply (fill_ext_below rest (add (k, 0%nat) v m0) (Datatypes.S k) k
                     ltac:(lia)) |].
        etransitivity; [ apply (hmap_lookup_add_eq (k, 0%nat) v m0) | reflexivity ].
      + cbn [nth]. replace (k + Datatypes.S i') with (Datatypes.S k + i') by lia.
        apply IH. lia.
  Qed.

  Lemma let_fst_Ret : forall (A : Type) (p : @mem nat V * nat) (X : A),
    (let '(mem', _) := p in Ret (mem', X))
    ≈ (Ret (fst p, X) : itree E0 (@mem nat V * A)).
  Proof. intros A [a b] X. reflexivity. Qed.

  (* [newListArray] on the empty store lays [xs] out at physical base 1. *)
  Lemma interp_st_newListArray : forall (lastIndex : nat) (xs : list nat),
    exists m0,
      interp_st ltu (STArray nat S nat)
        (@newListArray E0 nat _ _ _ _ 0 0 lastIndex xs) HMap.empty
      ≈ Ret (m0, MkSTArray nat S nat 1 0 lastIndex)
      /\ arr_rep m0 1 xs.
  Proof.
    intros lastIndex xs. eexists. split.
    - unfold newListArray, E0, V, T. rewrite interp_st_trigger.
      cbn -[HMap.add HMap.empty HMap.lookup].
      match goal with |- context[?F xs ?emp ?b] =>
        assert (HF : F = fill_ext) by reflexivity; rewrite HF;
        replace b with 1 by reflexivity end.
      match goal with |- (let '(mem', _) := ?p in _) ≈ _ =>
        rewrite (surjective_pairing p) end.
      reflexivity.
    - unfold arr_rep. intros k Hk. apply fill_ext_at. exact Hk.
  Qed.

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

(* ===================================================================== *)
(* Functional side: [quicksort_fun] returns a sorted permutation, and a   *)
(* sorted permutation is unique.                                           *)
(* ===================================================================== *)

Lemma filter_complement_perm (f : nat -> bool) (l : list nat) :
  Permutation l (List.filter f l ++ List.filter (fun x => negb (f x)) l).
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f a) eqn:Hfa; simpl.
  - apply perm_skip. exact IH.
  - etransitivity; [ apply perm_skip, IH |]. apply Permutation_middle.
Qed.

Lemma leb_negb_ltb : forall x p, (p <=? x) = negb (x <? p).
Proof.
  intros x p. destruct (p <=? x) eqn:E1; destruct (x <? p) eqn:E2; try reflexivity.
  - apply Nat.leb_le in E1; apply Nat.ltb_lt in E2; lia.
  - apply Nat.leb_gt in E1; apply Nat.ltb_ge in E2; lia.
Qed.

Lemma quicksort_fun_perm : forall l, Permutation l (quicksort_fun l).
Proof.
  intro l. funelim (quicksort_fun l); [ reflexivity |].
  assert (Hxs : Permutation xs (List.filter (fun x => x <? p) xs
                                ++ List.filter (fun x => p <=? x) xs)).
  { etransitivity; [ apply (filter_complement_perm (fun x => x <? p) xs) |].
    replace (List.filter (fun x => negb (x <? p)) xs)
      with (List.filter (fun x => p <=? x) xs);
      [ reflexivity | apply filter_ext; intros a; apply leb_negb_ltb ]. }
  etransitivity; [ apply perm_skip; exact Hxs |].
  transitivity (List.filter (fun x => x <? p) xs
                ++ p :: List.filter (fun x => p <=? x) xs).
  - apply Permutation_middle.
  - apply Permutation_app; [ exact H | apply perm_skip; exact H0 ].
Qed.

Lemma In_qf : forall x l, In x (quicksort_fun l) -> In x l.
Proof.
  intros x l H. apply Permutation_in with (quicksort_fun l);
    [ apply Permutation_sym, quicksort_fun_perm | exact H ].
Qed.

Lemma SSorted_app_middle : forall l1 l2 p,
  StronglySorted le l1 -> StronglySorted le l2 ->
  (forall x, In x l1 -> x <= p) -> (forall y, In y l2 -> p <= y) ->
  StronglySorted le (l1 ++ p :: l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 p H1 H2 Hl1 Hl2; simpl.
  - constructor; [ exact H2 | apply Forall_forall; exact Hl2 ].
  - apply StronglySorted_inv in H1 as [H1s H1f]. rewrite Forall_forall in H1f.
    constructor.
    + apply IH; auto. intros x Hx. apply Hl1. right. exact Hx.
    + apply Forall_forall. intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | Hy].
      * apply H1f. exact Hy.
      * destruct Hy as [Hy | Hy].
        -- subst y. apply Hl1. left. reflexivity.
        -- apply Nat.le_trans with p; [ apply Hl1; left; reflexivity | apply Hl2; exact Hy ].
Qed.

Lemma quicksort_fun_sorted : forall l, StronglySorted le (quicksort_fun l).
Proof.
  intro l. funelim (quicksort_fun l); [ constructor |].
  apply SSorted_app_middle; [ exact H | exact H0 | | ].
  - intros x Hx. apply In_qf, filter_In in Hx.
    destruct Hx as [_ Hlt]. apply Nat.ltb_lt in Hlt. lia.
  - intros y Hy. apply In_qf, filter_In in Hy.
    destruct Hy as [_ Hle]. apply Nat.leb_le in Hle. lia.
Qed.

Lemma sorted_perm_unique : forall l1 l2,
  StronglySorted le l1 -> StronglySorted le l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 H1 H2 Hp.
  - apply Permutation_nil in Hp. auto.
  - destruct l2 as [|b l2].
    + apply Permutation_sym, Permutation_nil in Hp. discriminate.
    + assert (Hin_b : In b (a :: l1))
        by (apply (Permutation_in b (Permutation_sym Hp)); left; reflexivity).
      assert (Hin_a : In a (b :: l2))
        by (apply (Permutation_in a Hp); left; reflexivity).
      apply StronglySorted_inv in H1 as [H1s H1f].
      apply StronglySorted_inv in H2 as [H2s H2f].
      rewrite Forall_forall in H1f, H2f.
      assert (Hab1 : a <= b)
        by (destruct Hin_b as [Heq | Hbin]; [ subst; reflexivity | apply H1f; exact Hbin ]).
      assert (Hab2 : b <= a)
        by (destruct Hin_a as [Heq | Hain]; [ subst; reflexivity | apply H2f; exact Hain ]).
      assert (a = b) by (apply Nat.le_antisymm; assumption). subst b.
      f_equal. apply IH; auto. apply Permutation_cons_inv with (a := a). exact Hp.
Qed.

(* [quicksort_ST_list] uses [length l - 1] (nat subtraction) for the top index,
   which underflows for the empty list, so the equivalence is stated for
   non-empty inputs. *)
Lemma qsort_fun_eq_qsort_ST : forall {S : Type} (l : list nat),
    Ret (quicksort_fun l) ≈ runST (S := S) (fun S0 => quicksort_ST_list l).
Proof.
  intros S l. destruct l as [| x l'].
  - (* empty list: [quicksort_ST_list []] returns [Ret []] directly *)
    assert (Hqf0 : quicksort_fun [] = [])
      by (apply Permutation_nil; apply Permutation_sym; apply quicksort_fun_perm).
    rewrite Hqf0. unfold runST. symmetry.
    etransitivity; [ eapply eutt_fmap; apply interp_st_Ret_eutt |].
    setoid_rewrite map_ret. cbn [snd]. reflexivity.
  - (* non-empty list *)
    assert (Hpos : 0 < length (x :: l')) by (simpl; lia).
    edestruct (interp_st_newListArray (S:=unit) (length (x :: l') - 1) (x :: l'))
      as (m0 & Hnew & Hrep0).
    edestruct (quicksort_ST_segment (S:=unit) 1 (length (x :: l') - 1) 0
                 (length (x :: l') - 1) (x :: l') m0)
      as (m1 & full1 & Hrun & Hrep1 & Hlenf1 & Hperm1 & Hunch1 & Hsort1 & _);
      [ exact Hrep0 | lia | lia | ].
    pose proof (interp_st_getElems (S:=unit) 1 (length (x :: l') - 1) full1 m1 Hrep1
                  ltac:(rewrite Hlenf1; lia)) as Hget.
    (* the whole [quicksort_ST_list] reduces to [Ret (m1, full1)] *)
    assert (Hqs : interp_st Nat.le (list nat)
                    (quicksort_ST_list (S:=unit) (x :: l')) HMap.empty
                  ≈ Ret (m1, full1)).
    { unfold quicksort_ST_list.
      etransitivity; [ apply interp_st_bind_eutt |].
      match goal with |- ITree.bind ?t ?k ≈ _ =>
        transitivity
          (ITree.bind (Ret (m0, MkSTArray nat unit nat 1 0 (length (x :: l') - 1))) k);
          [ apply eutt_eq_bind'; [ exact Hnew | intros u; reflexivity ] |] end.
      setoid_rewrite bind_Ret_l.
      etransitivity; [ apply interp_st_bind_eutt |].
      match goal with |- ITree.bind ?t ?k ≈ _ =>
        transitivity (ITree.bind (Ret (m1, tt)) k);
          [ apply eutt_eq_bind'; [ exact Hrun | intros u; reflexivity ] |] end.
      setoid_rewrite bind_Ret_l.
      etransitivity; [ apply interp_st_bind_eutt |].
      match goal with |- ITree.bind ?t ?k ≈ _ =>
        transitivity (ITree.bind (Ret (m1, full1)) k);
          [ apply eutt_eq_bind'; [ exact Hget | intros u; reflexivity ] |] end.
      setoid_rewrite bind_Ret_l. apply interp_st_Ret_eutt. }
    (* the ST result is [quicksort_fun (x :: l')] by uniqueness of sorted perms *)
    assert (Heq : full1 = quicksort_fun (x :: l')).
    { apply sorted_perm_unique.
      - apply SortedSeg_StronglySorted. intros i j Hij Hjl.
        apply Hsort1; [ lia | lia | rewrite Hlenf1 in Hjl; lia ].
      - apply quicksort_fun_sorted.
      - etransitivity;
          [ apply Permutation_sym; exact Hperm1 | apply quicksort_fun_perm ]. }
    unfold runST. symmetry.
    etransitivity; [ eapply eutt_fmap; exact Hqs |].
    setoid_rewrite map_ret. cbn [snd]. rewrite Heq. reflexivity.
Qed.

