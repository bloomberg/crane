(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Functional model of ST arrays of naturals indexed by [nat].

    An array [MkSTArray base 0 hi] whose cells [base .. base + hi] hold the
    list [full] is related to [full] by [arr_rep]; in-place writes and swaps
    are modelled by [upd] and [list_swap]. The [interp_st_*] lemmas give the
    effect of each array operation on the store. *)

From Stdlib Require Import
  Arith.PeanoNat
  Lia
  List
  Setoid
  Sorting.Permutation
.

From ExtLib Require Import
  Structures.Monad
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
  Monads.STMonadFacts
  Utils.HMap
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** Pure list update, modelling an in-place write. *)
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
  induction l as [|a l IHl]; intros i j v H; [ destruct j; reflexivity |].
  destruct i, j; simpl; try reflexivity; try lia. apply IHl; lia.
Qed.

(** Pure list swap, modelling [swapArray]. *)
Definition list_swap (l : list nat) (i j : nat) : list nat :=
  upd (upd l i (nth j l 0)) j (nth i l 0).

Lemma list_swap_length : forall l i j, length (list_swap l i j) = length l.
Proof. intros. unfold list_swap. rewrite !upd_length. reflexivity. Qed.

Lemma nth_list_swap_left : forall l i j,
  i < length l -> nth i (list_swap l i j) 0 = nth j l 0.
Proof.
  intros l i j Hi. unfold list_swap. destruct (Nat.eq_dec i j).
  - subst j. rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
  - rewrite nth_upd_neq, nth_upd_eq by lia. reflexivity.
Qed.

Lemma nth_list_swap_right : forall l i j,
  j < length l -> nth j (list_swap l i j) 0 = nth i l 0.
Proof.
  intros l i j Hj. unfold list_swap.
  rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
Qed.

Lemma nth_list_swap_other : forall l i j k,
  k <> i -> k <> j -> nth k (list_swap l i j) 0 = nth k l 0.
Proof. intros. unfold list_swap. rewrite !nth_upd_neq by lia. reflexivity. Qed.

(** Swapping two in-bounds positions is a permutation. *)
Lemma list_swap_perm : forall (l : list nat) i j,
  i < length l -> j < length l -> Permutation l (list_swap l i j).
Proof.
  intros l i j Hi Hj.
  apply (proj2 (Permutation_nth l (list_swap l i j) 0)).
  split; [ rewrite list_swap_length; reflexivity | ].
  exists (fun x => if Nat.eqb x i then j else if Nat.eqb x j then i else x).
  split; [| split].
  - intros x Hx. destruct (Nat.eqb x i); [ exact Hj |].
    destruct (Nat.eqb x j); [ exact Hi | exact Hx ].
  - intros x y Hx Hy Heq.
    destruct (Nat.eqb_spec x i), (Nat.eqb_spec y i),
             (Nat.eqb_spec x j), (Nat.eqb_spec y j); subst; lia.
  - intros x Hx.
    destruct (Nat.eqb_spec x i); [ subst; apply nth_list_swap_left; lia |].
    destruct (Nat.eqb_spec x j); [ subst; apply nth_list_swap_right; lia |].
    apply nth_list_swap_other; assumption.
Qed.

Lemma map_nth_seq_gen : forall (l pre : list nat),
  List.map (fun p => nth p (pre ++ l) 0) (seq (length pre) (length l)) = l.
Proof.
  induction l as [|a l IH]; intros pre; simpl; [ reflexivity |].
  f_equal.
  - rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
  - specialize (IH (pre ++ [a])).
    rewrite <- app_assoc, length_app, Nat.add_1_r in IH. exact IH.
Qed.

Lemma map_nth_seq : forall (l : list nat),
  List.map (fun p => nth p l 0) (seq 0 (length l)) = l.
Proof. intro l. apply (map_nth_seq_gen l []). Qed.

Section NatArrayModel.

  Let T := nat.
  Let ltu := Nat.le.
  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.
  Let V : T -> Type := fun _ => nat.
  Let E0 := (STEvent T S V) +' exceptE Err.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Opaque add lookup STRefToIx zero suc.

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

  (** Physical key of logical index [i] in an array with base/lo/hi. *)
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

  Lemma arr_key_val0 : forall (base hi i : nat),
    i <= hi ->
    @arr_key nat S ltu nat_ix (fun _ : nat => nat) 0 (MkSTArray nat S nat base 0 hi) i
    = Some (base + i).
  Proof. intros. rewrite arr_key_val by lia. f_equal. lia. Qed.

  (** Representation: physical cells [base .. base+|full|-1] (index 0) hold [full]. *)
  Definition arr_rep (m : @mem nat V) (base : nat) (full : list nat) : Prop :=
    forall k, k < length full -> lookup (base + k, 0%nat) m = Some (nth k full 0).

  Lemma arr_lookup_rep : forall base hi full i m,
    arr_rep m base full -> i <= hi -> hi < length full ->
    @arr_lookup nat S ltu nat_ix (fun _ : nat => nat) mem _ 0
       (MkSTArray nat S nat base 0 hi) i m
    = Some (nth i full 0).
  Proof.
    intros base hi full i m Hrep Hih Hhl. unfold arr_lookup.
    rewrite arr_key_val0 by lia. apply Hrep. lia.
  Qed.

  Lemma arr_rep_write : forall base full i v m,
    arr_rep m base full -> i < length full ->
    arr_rep (add (base + i, 0%nat) v m) base (upd full i v).
  Proof.
    intros base full i v m Hrep Hi k Hk. rewrite upd_length in Hk.
    destruct (Nat.eq_dec k i).
    - subst k. rewrite hmap_lookup_add_eq, nth_upd_eq by lia. reflexivity.
    - rewrite hmap_lookup_add_ne by (intros [=]; lia).
      rewrite nth_upd_neq by lia. apply Hrep. lia.
  Qed.

  Lemma arr_rep_swap : forall base full left right m,
    arr_rep m base full -> left < length full -> right < length full ->
    arr_rep (add (base + right, 0%nat) (nth left full 0)
              (add (base + left, 0%nat) (nth right full 0) m))
            base (list_swap full left right).
  Proof.
    intros. apply arr_rep_write; [ apply arr_rep_write | rewrite upd_length ]; auto.
  Qed.

  (** [swapArray] reads both cells, then writes them crossed. *)
  Lemma interp_st_swapArray : forall base hi full left right (m : @mem nat V),
    arr_rep m base full -> left <= hi -> right <= hi -> hi < length full ->
    interp_st ltu unit
      (@swapArray E0 nat S _ V _ 0 (MkSTArray nat S nat base 0 hi) left right) m
    ≈ Ret (add (base + right, 0%nat) (nth left full 0)
             (add (base + left, 0%nat) (nth right full 0) m), tt).
  Proof.
    intros. unfold swapArray.
    eapply interp_st_bind_Ret_l; [ apply interp_st_readArray, arr_lookup_rep; eauto |].
    eapply interp_st_bind_Ret_l; [ apply interp_st_readArray, arr_lookup_rep; eauto |].
    eapply interp_st_bind_Ret_l; [ apply interp_st_writeArray, arr_key_val0; lia |].
    apply interp_st_writeArray, arr_key_val0; lia.
  Qed.

  Transparent add lookup STRefToIx zero suc.

  (** [getElems] reads the whole array back as the represented list. *)
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
    { induction ps as [|q rest IHps]; intros Hall; [ reflexivity |].
      cbn -[arr_lookup].
      rewrite arr_lookup_rep with (full := full) by (auto with datatypes; lia).
      rewrite IHps by auto with datatypes. reflexivity. }
    rewrite Hgen by (intros q Hq; cbn [range nat_ix] in Hq; apply in_seq in Hq; lia).
    cbn [range nat_ix].
    replace (1 + hi - 0) with (length full) by lia.
    rewrite map_nth_seq. reflexivity.
  Qed.

  (** External model of the handler's list-array [fill] loop. *)
  Fixpoint fill_ext (es : list (V 0)) (m0 : @mem nat V) (k : nat) : @mem nat V * nat :=
    match es with
    | [] => (m0, k)
    | v :: rest => fill_ext rest (add (k, 0%nat) v m0) (Datatypes.S k)
    end.

  Lemma fill_ext_below : forall es (m0 : @mem nat V) k j,
    j < k -> lookup (j, 0%nat) (fst (fill_ext es m0 k)) = lookup (j, 0%nat) m0.
  Proof.
    induction es as [|v rest IH]; intros m0 k j Hj; cbn [fill_ext fst]; [ reflexivity |].
    rewrite IH by lia.
    apply (hmap_lookup_add_ne (j, 0%nat) (k, 0%nat) v m0). intros [=]; lia.
  Qed.

  Lemma fill_ext_at : forall es (m0 : @mem nat V) k i,
    i < length es ->
    lookup (k + i, 0%nat) (fst (fill_ext es m0 k)) = Some (nth i es 0).
  Proof.
    induction es as [|v rest IH]; intros m0 k i Hi; cbn [length] in Hi; [ lia |].
    cbn [fill_ext fst]. destruct i as [|i'].
    - rewrite Nat.add_0_r.
      rewrite (fill_ext_below rest (add (k, 0%nat) v m0) (Datatypes.S k) k) by lia.
      etransitivity; [ apply (hmap_lookup_add_eq (k, 0%nat) v m0) | reflexivity ].
    - cbn [nth]. replace (k + Datatypes.S i') with (Datatypes.S k + i') by lia.
      apply IH. lia.
  Qed.

  Lemma let_fst_Ret : forall (A : Type) (p : @mem nat V * nat) (X : A),
    (let '(mem', _) := p in Ret (mem', X))
    ≈ (Ret (fst p, X) : itree E0 (@mem nat V * A)).
  Proof. intros A [a b] X. reflexivity. Qed.

  (** [newListArray] on the empty store lays [xs] out at physical base 1. *)
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
    - intros k Hk. apply fill_ext_at. exact Hk.
  Qed.

End NatArrayModel.
