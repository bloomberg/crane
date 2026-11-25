(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [quicksort_ST_list] computes [quicksort_fun].

    The in-place sort is related to the list model of [STMonadArrayFacts]:
    [partition] permutes a segment around a pivot ([interp_st_partition]),
    and [quicksort_ST] sorts a segment and leaves the rest of the array
    untouched ([quicksort_ST_segment]). Both sorts return a sorted
    permutation of their input, and a sorted permutation is unique. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Compare_dec
  Lia
  List
  Setoid
  Sorting.Permutation
  Sorting.Sorted
.

From Equations Require Import Equations.

From ExtLib Require Import
  Structures.Functor
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
  Monads.STMonadArrayFacts
  Monads.STMonadFacts
  Utils.HMap
.

From CraneTestsMonadic.st_quicksort Require Import StQuicksort.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** Pure model of the Lomuto scan loop. *)
Fixpoint lomuto (full : list nat) (pv : nat) (is : list nat) (si : nat)
  : list nat * nat :=
  match is with
  | nil => (full, si)
  | i :: rest =>
      if Nat.leb (nth i full 0) pv
      then lomuto (list_swap full i si) pv rest (Datatypes.S si)
      else lomuto full pv rest si
  end.

(** The Lomuto scan only permutes the list (and preserves its length). *)
Lemma lomuto_perm : forall is full pv si,
  (forall i, In i is -> i < length full) ->
  si + length is <= length full ->
  Permutation full (fst (lomuto full pv is si))
  /\ length (fst (lomuto full pv is si)) = length full.
Proof.
  induction is as [|i rest IH]; intros full pv si Hin Hlen; cbn [lomuto fst].
  - split; reflexivity.
  - cbn [length] in Hlen.
    assert (Hi : i < length full) by (apply Hin; left; reflexivity).
    destruct (Nat.leb (nth i full 0) pv).
    + edestruct (IH (list_swap full i si) pv (Datatypes.S si)) as [Hp Hl];
        rewrite ?list_swap_length in *; auto with datatypes; try lia.
      split; [ etransitivity; [ apply (list_swap_perm full i si); lia | exact Hp ] | exact Hl ].
    + apply IH; auto with datatypes; lia.
Qed.

(** The Lomuto scan invariant: scanning the consecutive indices [cur .. cur+cnt)
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
    intros lo cur full pv si Hlosi Hsicur Hlen Hsmall Hbig; cbn [seq lomuto].
  - repeat split; intros; first [ lia | reflexivity | apply Hsmall; lia | apply Hbig; lia ].
  - destruct (Nat.leb_spec (nth cur full 0) pv) as [Hle | Hgt].
    + specialize (IH lo (Datatypes.S cur) (list_swap full cur si) pv (Datatypes.S si)).
      destruct (lomuto (list_swap full cur si) pv (seq (Datatypes.S cur) cnt')
                       (Datatypes.S si)) as [full' si'].
      destruct IH as (I1 & I2 & I3 & I4 & I5 & I6);
        rewrite ?list_swap_length; try lia.
      * intros j Hlo Hj. destruct (Nat.eq_dec j si).
        -- subst j. rewrite nth_list_swap_right by lia. exact Hle.
        -- rewrite nth_list_swap_other by lia. apply Hsmall; lia.
      * intros j Hj1 Hj2. destruct (Nat.eq_dec j cur).
        -- subst j. rewrite nth_list_swap_left by lia. apply Hbig; lia.
        -- rewrite nth_list_swap_other by lia. apply Hbig; lia.
      * repeat split; try lia; auto.
        -- intros j Hj1 Hj2. apply I4; lia.
        -- intros j Hj. rewrite I5, nth_list_swap_other by lia. reflexivity.
        -- rewrite I6. apply list_swap_length.
    + specialize (IH lo (Datatypes.S cur) full pv si).
      destruct (lomuto full pv (seq (Datatypes.S cur) cnt') si) as [full' si'].
      destruct IH as (I1 & I2 & I3 & I4 & I5 & I6); try lia.
      * intros; apply Hsmall; lia.
      * intros j Hj1 Hj2. destruct (Nat.eq_dec j cur); [ subst; lia | apply Hbig; lia ].
      * repeat split; try lia; auto.
        -- intros j Hj1 Hj2. apply I4; lia.
        -- intros j Hj. apply I5. lia.
Qed.

Section QuicksortProofs.

  Let T := nat.
  Let ltu := Nat.le.
  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.
  Let V : T -> Type := fun _ => nat.
  Let E0 := (STEvent T S V) +' exceptE Err.

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

  Lemma quicksort_ST_list2154 :
    burn 100 (runST (S := S) (fun S0 => quicksort_ST_list (S := S0) [2; 1; 5; 4]))
    = Ret [1; 2; 4; 5].
  Proof using Type. lazy. reflexivity. Qed.

  Lemma sort_list__long :
    burn 300 (runST (S := S) (fun S0 => quicksort_ST_list (S := S0) [8; 4; 6; 9; 7; 3; 1; 2; 5]))
    = Ret [1; 2; 3; 4; 5; 6; 7; 8; 9].
  Proof using Type. lazy. reflexivity. Qed.

  Opaque add lookup STRefToIx zero suc.

  (** The scan loop's [interp_st] effect matches [lomuto] on the list model. *)
  Lemma interp_st_lomuto_loop :
    forall (is : list nat) base hi pv full si (m : @mem nat V),
      arr_rep m base full -> hi < length full ->
      (forall i, In i is -> i <= hi) -> si + length is <= Datatypes.S hi ->
      exists m',
        interp_st ltu nat
          (for_each_with (E := E0) is si
             (fun storeIndex i =>
                val <- @readArray E0 nat _ _ _ _ 0 (MkSTArray nat S nat base 0 hi) i ;;
                if Nat.leb val pv
                then @swapArray E0 nat S _ V _ 0 (MkSTArray nat S nat base 0 hi) i storeIndex ;;
                     Ret (Datatypes.S storeIndex)
                else Ret storeIndex)) m
        ≈ Ret (m', snd (lomuto full pv is si))
        /\ arr_rep m' base (fst (lomuto full pv is si)).
  Proof.
    induction is as [|i rest IH];
      intros base hi pv full si m Hrep Hhl Hin Hsi; cbn [for_each_with lomuto].
    - exists m. split; [ apply interp_st_Ret_eutt | exact Hrep ].
    - assert (Hi : i <= hi) by (apply Hin; left; reflexivity).
      cbn [length] in Hsi.
      destruct (Nat.leb (nth i full 0) pv) eqn:Hle.
      + edestruct (IH base hi pv (list_swap full i si) (Datatypes.S si))
          as [m' [Hrun Hrep']];
          [ apply arr_rep_swap; eauto; lia | rewrite list_swap_length; lia
          | auto with datatypes | lia |].
        exists m'. split; [| exact Hrep'].
        eapply interp_st_bind_Ret_l; [| exact Hrun ].
        eapply interp_st_bind_Ret_l;
          [ apply interp_st_readArray, arr_lookup_rep; eauto; lia |].
        cbv beta. rewrite Hle.
        eapply interp_st_bind_Ret_l; [ apply interp_st_swapArray; eauto; lia |].
        apply interp_st_Ret_eutt.
      + edestruct (IH base hi pv full si m) as [m' [Hrun Hrep']];
          auto with datatypes; try lia.
        exists m'. split; [| exact Hrep'].
        eapply interp_st_bind_Ret_l; [| exact Hrun ].
        eapply interp_st_bind_Ret_l;
          [ apply interp_st_readArray, arr_lookup_rep; eauto; lia |].
        cbv beta. rewrite Hle. apply interp_st_Ret_eutt.
  Qed.

  Transparent add lookup STRefToIx zero suc.

  (** The index range scanned by partition is exactly [seq lo (hi - lo)]. *)
  Lemma range_seq_sub : forall lo hi, lo < hi ->
    range lo (sub hi (suc zero)) = seq lo (hi - lo).
  Proof. intros lo hi H. cbn [range sub suc zero nat_ix]. f_equal. lia. Qed.

  (** Correctness of the in-place [partition]: it permutes the segment [lo,hi],
      leaves everything outside untouched, and returns a pivot position [p] with
      the standard partition invariant. *)
  Lemma interp_st_partition :
    forall (base hi_arr lo hi pividx : nat) (full : list nat) (m : @mem nat V),
      arr_rep m base full ->
      lo < hi -> hi <= hi_arr -> hi_arr < length full ->
      lo <= pividx -> pividx <= hi ->
      exists m' full' p,
        interp_st ltu nat
          (partition (E' := E0) (MkSTArray nat S nat base 0 hi_arr) 0 lo hi pividx) m
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
    set (pv := nth pividx full 0).
    set (full_a := list_swap full pividx hi).
    assert (Hlen_a : length full_a = length full) by apply list_swap_length.
    (* pure model of the scan *)
    pose proof (lomuto_partition (hi - lo) lo lo full_a pv lo) as Hlp.
    pose proof (lomuto_perm (seq lo (hi - lo)) full_a pv lo) as Hpb.
    destruct (lomuto full_a pv (seq lo (hi - lo)) lo) as [full_b storeIndex] eqn:ELB.
    destruct Hlp as (Hst1 & Hst2 & Hsmall_b & Hbig_b & Hunch_b & Hlen_b); try lia.
    destruct Hpb as (Hpermb & _).
    { intros i Hi. apply in_seq in Hi. lia. }
    { rewrite length_seq. lia. }
    (* the pivot value ends up at [storeIndex] after the final swap *)
    assert (Hnp : nth storeIndex (list_swap full_b storeIndex hi) 0 = pv).
    { rewrite nth_list_swap_left, (Hunch_b hi) by lia.
      apply nth_list_swap_right. lia. }
    (* the scan loop on the store *)
    edestruct (interp_st_lomuto_loop (seq lo (hi - lo)) base hi_arr pv full_a lo
                 (add (base + hi, 0%nat) pv (add (base + pividx, 0%nat) (nth hi full 0) m)))
      as [m_loop [Hloop Hrep_loop]];
      [ apply arr_rep_swap; auto; lia | lia
      | intros i Hi; apply in_seq in Hi; lia | rewrite length_seq; lia |].
    rewrite ELB in Hloop, Hrep_loop. cbn [fst snd] in Hloop, Hrep_loop.
    cbn [fst] in Hpermb.
    eexists _, (list_swap full_b storeIndex hi), storeIndex.
    split.
    { unfold partition. cbn [range sub suc zero nat_ix].
      replace (1 + (hi - 1) - lo) with (hi - lo) by lia.
      eapply interp_st_bind_Ret_l;
        [ apply interp_st_readArray, arr_lookup_rep; eauto; lia |].
      eapply interp_st_bind_Ret_l; [ apply interp_st_swapArray; eauto; lia |].
      eapply interp_st_bind_Ret_l; [ exact Hloop |].
      eapply interp_st_bind_Ret_l; [ apply interp_st_swapArray; eauto; lia |].
      apply interp_st_Ret_eutt. }
    repeat split.
    - apply arr_rep_swap; auto; lia.
    - rewrite list_swap_length; lia.
    - etransitivity; [ apply (list_swap_perm full pividx hi); lia |].
      etransitivity; [ exact Hpermb |].
      apply list_swap_perm; lia.
    - intros j Hj. rewrite nth_list_swap_other, Hunch_b by lia.
      apply nth_list_swap_other; lia.
    - exact Hst1.
    - lia.
    - intros j Hjlo Hjp. rewrite Hnp, nth_list_swap_other by lia.
      apply Hsmall_b; lia.
    - intros j Hjp Hjhi. rewrite Hnp. apply Nat.lt_le_incl.
      destruct (Nat.eq_dec j hi).
      + subst j. rewrite nth_list_swap_right by lia. apply Hbig_b; lia.
      + rewrite nth_list_swap_other by lia. apply Hbig_b; lia.
  Qed.

  (** Segment machinery: permutation and pairwise sortedness of a sub-range. *)

  Definition seg (l : list nat) (a b : nat) : list nat :=
    firstn (Datatypes.S b - a) (skipn a l).

  Lemma nth_seg : forall l a b k,
    k < Datatypes.S b - a -> nth k (seg l a b) 0 = nth (a + k) l 0.
  Proof.
    intros l a b k Hk. unfold seg. rewrite nth_firstn.
    destruct (Nat.ltb_spec k (Datatypes.S b - a)); [| lia ].
    apply nth_skipn.
  Qed.

  Lemma length_seg : forall l a b,
    b < length l -> length (seg l a b) = Datatypes.S b - a.
  Proof. intros l a b Hb. unfold seg. rewrite length_firstn, length_skipn. lia. Qed.

  Lemma seg_decomp : forall l a b, a <= Datatypes.S b ->
    l = firstn a l ++ seg l a b ++ skipn (Datatypes.S b) l.
  Proof.
    intros l a b Hab. unfold seg.
    rewrite <- (firstn_skipn a l) at 1. f_equal.
    rewrite <- (firstn_skipn (Datatypes.S b - a) (skipn a l)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia.
  Qed.

  Lemma seg_perm : forall full full' a b,
    Permutation full full' -> length full' = length full ->
    b < length full -> a <= Datatypes.S b ->
    (forall j, j < a \/ b < j -> nth j full' 0 = nth j full 0) ->
    Permutation (seg full a b) (seg full' a b).
  Proof.
    intros full full' a b Hperm Hlen Hb Hab Hunch.
    assert (Hpre : firstn a full = firstn a full').
    { apply nth_ext with (d := 0) (d' := 0); rewrite ?length_firstn; [ lia |].
      intros n Hn. rewrite !nth_firstn.
      destruct (Nat.ltb_spec n a); [ symmetry; apply Hunch; lia | reflexivity ]. }
    assert (Hsuf : skipn (Datatypes.S b) full = skipn (Datatypes.S b) full').
    { apply nth_ext with (d := 0) (d' := 0); rewrite ?length_skipn; [ lia |].
      intros n Hn. rewrite !nth_skipn. symmetry. apply Hunch. lia. }
    rewrite (seg_decomp full a b Hab), (seg_decomp full' a b Hab), <- Hpre, <- Hsuf in Hperm.
    apply Permutation_app_inv_l, Permutation_app_inv_r in Hperm. exact Hperm.
  Qed.

  (** A pointwise property over a segment is preserved by a permutation that
      leaves everything outside the segment fixed. *)
  Lemma seg_forall_perm : forall (P : nat -> Prop) full full' a b,
    Permutation full full' -> length full' = length full ->
    b < length full -> a <= Datatypes.S b ->
    (forall j, j < a \/ b < j -> nth j full' 0 = nth j full 0) ->
    (forall j, a <= j -> j <= b -> P (nth j full 0)) ->
    (forall j, a <= j -> j <= b -> P (nth j full' 0)).
  Proof.
    intros P full full' a b Hperm Hlen Hb Hab Hunch Hall j Hj1 Hj2.
    replace (nth j full' 0) with (nth (j - a) (seg full' a b) 0)
      by (rewrite nth_seg by lia; f_equal; lia).
    assert (HIn : In (nth (j - a) (seg full' a b) 0) (seg full a b)).
    { eapply Permutation_in; [ symmetry; apply seg_perm; eauto |].
      apply nth_In. rewrite length_seg by lia. lia. }
    apply In_nth with (d := 0) in HIn. destruct HIn as [k [Hk <-]].
    rewrite length_seg in Hk by lia.
    rewrite nth_seg by lia. apply Hall; lia.
  Qed.

  (** Pairwise sortedness of a sub-range. *)
  Definition SortedSeg (l : list nat) (lo hi : nat) : Prop :=
    forall a b, lo <= a -> a <= b -> b <= hi -> nth a l 0 <= nth b l 0.

  Lemma SortedSeg_StronglySorted : forall l,
    (forall i j, i <= j -> j < length l -> nth i l 0 <= nth j l 0) ->
    StronglySorted le l.
  Proof.
    induction l as [|x xs IH]; intros H; constructor.
    - apply IH. intros i j Hij Hjl.
      apply (H (Datatypes.S i) (Datatypes.S j)); simpl; lia.
    - apply Forall_forall. intros y Hy. apply In_nth with (d := 0) in Hy.
      destruct Hy as [k [Hk <-]].
      apply (H 0 (Datatypes.S k)); simpl; lia.
  Qed.

  (** In-place quicksort correctness: the segment [lo,hi] is sorted, the
      whole array is permuted, and everything outside [lo,hi] is untouched.
      Induction on the fuel [S d], with [d >= hi - lo]. *)
  Lemma quicksort_ST_segment : forall base d lo hi full m,
    arr_rep m base full -> hi < length full -> hi - lo <= d ->
    exists m' full',
      interp_st ltu unit
        (quicksort_ST (Datatypes.S d) (MkSTArray nat S nat base 0 (length full - 1)) 0 lo hi) m
        ≈ Ret (m', tt)
      /\ arr_rep m' base full'
      /\ length full' = length full
      /\ Permutation full full'
      /\ (forall j, j < lo \/ hi < j -> nth j full' 0 = nth j full 0)
      /\ SortedSeg full' lo hi
      /\ (hi <= lo -> full' = full).
  Proof.
    intros base. induction d as [|d IH]; intros lo hi full m Hrep Hhl Hd;
      destruct (le_gt_dec hi lo) as [Hle | Hgt]; try lia.
    1, 2: (* hi <= lo: nothing to do *)
      exists m, full; split;
      [ cbn [quicksort_ST toNat fromNat nat_ix];
        destruct (Nat.ltb_spec lo hi); [ lia | apply interp_st_Ret_eutt ] |];
      repeat split; auto using Permutation_refl;
      intros a b Ha Hab Hb; replace b with a by lia; reflexivity.
    (* lo < hi *)
    set (pividx := lo + (hi - lo) / 2).
    assert (Hdiv : (hi - lo) / 2 <= hi - lo) by (apply Nat.Div0.div_le_upper_bound; lia).
    edestruct (interp_st_partition base (length full - 1) lo hi pividx full m)
      as (m1 & full1 & p & Hpart & Hrep1 & Hlen1 & Hperm1 & Hunch1 &
          Hp_lo & Hp_hi & Hleft & Hright); auto; try (unfold pividx; lia).
    edestruct (IH lo (p - 1) full1 m1)
      as (m2 & full2 & Hrun1 & Hrep2 & Hlen2 & Hperm2 & Hunch2 & Hsort2 & Hnoop1);
      auto; try lia.
    edestruct (IH (p + 1) hi full2 m2)
      as (m3 & full3 & Hrun2 & Hrep3 & Hlen3 & Hperm3 & Hunch3 & Hsort3 & Hnoop2);
      auto; try lia.
    rewrite Hlen1 in Hrun1. rewrite Hlen2, Hlen1 in Hrun2.
    exists m3, full3.
    (* the values around the pivot *)
    set (pivot := nth p full1 0).
    assert (F2' : forall j, j <= p -> nth j full3 0 = nth j full2 0)
      by (intros j Hj; apply Hunch3; lia).
    assert (F1 : nth p full3 0 = pivot).
    { rewrite F2' by lia.
      destruct (Nat.eq_dec p 0); [ rewrite Hnoop1 by lia | apply Hunch2; lia ].
      reflexivity. }
    assert (F4 : forall j, lo <= j -> j < p -> nth j full3 0 <= pivot).
    { intros j Hjlo Hjp. rewrite F2' by lia.
      apply (seg_forall_perm (fun x => x <= pivot) full1 full2 lo (p - 1));
        auto; try lia.
      intros k Hk1 Hk2. apply Hleft; lia. }
    assert (F5 : forall j, p < j -> j <= hi -> pivot <= nth j full3 0).
    { intros j Hjp Hjhi.
      apply (seg_forall_perm (fun x => pivot <= x) full2 full3 (p + 1) hi);
        auto; try lia.
      intros k Hk1 Hk2. rewrite (Hunch2 k) by lia. apply Hright; lia. }
    split.
    { cbn [quicksort_ST toNat fromNat nat_ix].
      destruct (Nat.ltb_spec lo hi); [| lia ].
      eapply interp_st_bind_Ret_l; [ exact Hpart |].
      eapply interp_st_bind_Ret_l; [ exact Hrun1 |].
      exact Hrun2. }
    repeat split.
    - exact Hrep3.
    - lia.
    - rewrite Hperm1, Hperm2. exact Hperm3.
    - intros j Hj. rewrite Hunch3, Hunch2, Hunch1 by lia. reflexivity.
    - intros a b Ha Hab Hb.
      destruct (lt_eq_lt_dec a p) as [[Ha_lt | ->] | Ha_gt];
        destruct (lt_eq_lt_dec b p) as [[Hb_lt | ->] | Hb_gt]; try lia.
      + rewrite !F2' by lia. apply Hsort2; lia.
      + rewrite F1. apply F4; lia.
      + transitivity pivot; [ apply F4 | apply F5 ]; lia.
      + rewrite F1. apply F5; lia.
      + apply Hsort3; lia.
    - lia.
  Qed.

End QuicksortProofs.

(** Functional side: [quicksort_fun] returns a sorted permutation, and a
    sorted permutation is unique. *)

Lemma filter_complement_perm (f : nat -> bool) (l : list nat) :
  Permutation l (List.filter f l ++ List.filter (fun x => negb (f x)) l).
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f a); simpl.
  - apply perm_skip. exact IH.
  - etransitivity; [ apply perm_skip, IH |]. apply Permutation_middle.
Qed.

Lemma leb_negb_ltb : forall x p, (p <=? x) = negb (x <? p).
Proof. intros x p. destruct (Nat.leb_spec p x), (Nat.ltb_spec x p); auto; lia. Qed.

Lemma quicksort_fun_perm : forall l, Permutation l (quicksort_fun l).
Proof.
  intro l. funelim (quicksort_fun l); [ reflexivity |].
  change ([p] ++ ?l) with (p :: l). rewrite <- Permutation_middle. apply perm_skip.
  rewrite (filter_complement_perm (fun x => x <? p) xs) at 1.
  replace (List.filter (fun x => negb (x <? p)) xs) with (List.filter (fun x => p <=? x) xs)
    by (apply filter_ext; intros; apply leb_negb_ltb).
  apply Permutation_app; assumption.
Qed.

Lemma In_qf : forall x l, In x (quicksort_fun l) -> In x l.
Proof. intros x l. apply Permutation_in. symmetry. apply quicksort_fun_perm. Qed.

Lemma SSorted_app_middle : forall l1 l2 p,
  StronglySorted le l1 -> StronglySorted le l2 ->
  (forall x, In x l1 -> x <= p) -> (forall y, In y l2 -> p <= y) ->
  StronglySorted le (l1 ++ p :: l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 p H1 H2 Hl1 Hl2; simpl.
  - constructor; [ exact H2 | apply Forall_forall; exact Hl2 ].
  - apply StronglySorted_inv in H1 as [H1s H1f]. rewrite Forall_forall in H1f.
    constructor; [ apply IH; auto with datatypes |].
    apply Forall_forall. intros y Hy. apply in_app_or in Hy.
    destruct Hy as [Hy | [<- | Hy]]; auto with datatypes.
    transitivity p; auto with datatypes.
Qed.

Lemma quicksort_fun_sorted : forall l, StronglySorted le (quicksort_fun l).
Proof.
  intro l. funelim (quicksort_fun l); [ constructor |].
  apply SSorted_app_middle; auto.
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
  - destruct l2 as [|b l2]; [ symmetry in Hp; apply Permutation_nil_cons in Hp; contradiction |].
    assert (Hin_b : In b (a :: l1)) by (rewrite Hp; left; reflexivity).
    assert (Hin_a : In a (b :: l2)) by (rewrite <- Hp; left; reflexivity).
    apply StronglySorted_inv in H1 as [H1s H1f].
    apply StronglySorted_inv in H2 as [H2s H2f].
    rewrite Forall_forall in H1f, H2f.
    assert (a = b) as <-.
    { destruct Hin_b as [-> | Hb]; [ reflexivity |].
      destruct Hin_a as [-> | Ha]; [ reflexivity |].
      apply Nat.le_antisymm; auto. }
    f_equal. apply IH; auto. eapply Permutation_cons_inv. exact Hp.
Qed.

Lemma qsort_fun_eq_qsort_ST : forall {S : Type} (l : list nat),
    Ret (quicksort_fun l) ≈ runST (S := S) (fun S0 => quicksort_ST_list l).
Proof.
  intros S l. symmetry. destruct l as [| x l'].
  - (* [quicksort_ST_list []] returns [Ret []] directly *)
    apply (runST_Ret _ HMap.empty). apply interp_st_Ret_eutt.
  - set (xs := x :: l').
    assert (Hpos : 0 < length xs) by (simpl; lia).
    assert (Hlen : length xs = Datatypes.S (length l')) by reflexivity.
    edestruct (interp_st_newListArray (S := unit) (length xs - 1) xs)
      as (m0 & Hnew & Hrep0).
    edestruct (quicksort_ST_segment (S := unit) 1 (length l') 0 (length xs - 1) xs m0)
      as (m1 & full1 & Hrun & Hrep1 & Hlenf1 & Hperm1 & Hunch1 & Hsort1 & _);
      auto; try lia.
    (* the ST result is [quicksort_fun xs] by uniqueness of sorted permutations *)
    replace (quicksort_fun xs) with full1.
    2: { apply sorted_perm_unique.
         - apply SortedSeg_StronglySorted. intros i j Hij Hjl. apply Hsort1; lia.
         - apply quicksort_fun_sorted.
         - rewrite <- Hperm1. apply quicksort_fun_perm. }
    apply (runST_Ret _ m1). unfold quicksort_ST_list, xs. fold xs.
    eapply interp_st_bind_Ret_l; [ exact Hnew |].
    eapply interp_st_bind_Ret_l; [ exact Hrun |].
    apply interp_st_getElems; auto. lia.
Qed.
