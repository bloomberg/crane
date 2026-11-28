(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Functional model of ST arrays of naturals.

    An array [ST.MkArrayLoc base n] whose cells [base .. base + n - 1] hold the
    list [full] is related to [full] by [arr_rep]; in-place writes and swaps
    are modelled by [upd] and [list_swap], and the array operations are
    [spec] rules over [arr_rep]. *)

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
  Monads.MonadFacts
  Monads.ST
  Monads.STFacts
  Monads.STSpec
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

(** An in-place write keeps the size. *)
Lemma upd_length : forall l i v, length (upd l i v) = length l.
Proof. induction l; intros [|i] v; simpl; auto. Qed.

(** The written position holds the new value. *)
Lemma nth_upd_eq : forall l i v, i < length l -> nth i (upd l i v) 0 = v.
Proof. induction l; intros [|i] v H; simpl in *; try lia; auto. apply IHl; lia. Qed.

(** Every other position is unchanged. *)
Lemma nth_upd_neq : forall l i j v, i <> j -> nth j (upd l i v) 0 = nth j l 0.
Proof.
  induction l as [|a l IHl]; intros i j v H; [ destruct j; reflexivity |].
  destruct i, j; simpl; try reflexivity; try lia. apply IHl; lia.
Qed.

(** Pure list swap, modelling [ST.swap_array]. *)
Definition list_swap (l : list nat) (i j : nat) : list nat :=
  upd (upd l i (nth j l 0)) j (nth i l 0).

(** A swap keeps the size. *)
Lemma list_swap_length : forall l i j, length (list_swap l i j) = length l.
Proof. intros. unfold list_swap. rewrite !upd_length. reflexivity. Qed.

(** After a swap, position [i] holds the old element at [j]. *)
Lemma nth_list_swap_left : forall l i j,
  i < length l -> nth i (list_swap l i j) 0 = nth j l 0.
Proof.
  intros l i j Hi. unfold list_swap. destruct (Nat.eq_dec i j).
  - subst j. rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
  - rewrite nth_upd_neq, nth_upd_eq by lia. reflexivity.
Qed.

(** After a swap, position [j] holds the old element at [i]. *)
Lemma nth_list_swap_right : forall l i j,
  j < length l -> nth j (list_swap l i j) 0 = nth i l 0.
Proof.
  intros l i j Hj. unfold list_swap.
  rewrite nth_upd_eq by (rewrite upd_length; lia). reflexivity.
Qed.

(** A swap leaves every other position alone. *)
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

(** Indexing past a prefix [pre] at every position of [l] rebuilds [l]. *)
Lemma map_nth_seq_gen : forall (l pre : list nat),
  List.map (fun p => nth p (pre ++ l) 0) (seq (length pre) (length l)) = l.
Proof.
  induction l as [|a l IH]; intros pre; simpl; [ reflexivity |].
  f_equal.
  - rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
  - specialize (IH (pre ++ [a])).
    rewrite <- app_assoc, length_app, Nat.add_1_r in IH. exact IH.
Qed.

(** Reading every index of a list in order rebuilds the list. *)
Lemma map_nth_seq : forall (l : list nat),
  List.map (fun p => nth p l 0) (seq 0 (length l)) = l.
Proof. intro l. apply (map_nth_seq_gen l []). Qed.

Section NatArrays.

  Context {E : Type -> Type} `{exceptE Err -< E}.
  (** The store holds only [nat]s. *)
  Notation V := (fun _ : nat => nat).

  (** The cells [base .. base + |full| - 1] hold [full]. *)
  Definition arr_rep (m : mem V) (base : nat) (full : list nat) : Prop :=
    forall k, k < length full -> read_at (V := V) (base + k) m = Some (nth k full 0).

  (** Writing cell [base + i] of a represented array represents [upd]. *)
  Lemma arr_rep_write : forall base full i v m,
    arr_rep m base full -> i < length full ->
    arr_rep (write_at (V := V) (base + i) v m) base (upd full i v).
  Proof.
    intros base full i v m Hrep Hi k Hk. rewrite upd_length in Hk.
    destruct (Nat.eq_dec k i) as [-> | Hne].
    - rewrite read_at_write_at_eq, nth_upd_eq by lia. reflexivity.
    - rewrite read_at_write_at_ne by lia. rewrite nth_upd_neq by lia. apply Hrep. lia.
  Qed.

  (** The two writes of [ST.swap_array] represent [list_swap]. *)
  Lemma arr_rep_swap : forall base full l r m,
    arr_rep m base full -> l < length full -> r < length full ->
    arr_rep (write_at (V := V) (base + r) (nth l full 0)
               (write_at (V := V) (base + l) (nth r full 0) m))
            base (list_swap full l r).
  Proof.
    intros. apply arr_rep_write; [ apply arr_rep_write | rewrite upd_length ]; auto.
  Qed.

  (** Reading index [i] returns element [i] of the represented list.  This
      and the next rules restate the array operations over [arr_rep]: what
      a program knows of an array is the list it represents. *)
  Lemma read_array_rep base n full i m (Q : mem V -> nat -> Prop) :
    arr_rep m base full -> length full = n -> i < n -> Q m (nth i full 0) ->
    spec (E := E) (ST.read_array (R := ST.model_refs) (V := V) (ST.MkArrayLoc base n) i) m Q.
  Proof.
    intros Hrep Hlen Hi HQ. eapply read_array; [ exact Hi | apply Hrep; lia | exact HQ ].
  Qed.

  (** Swapping two indices in range represents [list_swap]. *)
  Lemma swap_array_rep base n full l r m (Q : mem V -> unit -> Prop) :
    arr_rep m base full -> length full = n -> l < n -> r < n ->
    (forall m', arr_rep m' base (list_swap full l r) -> Q m' tt) ->
    spec (E := E) (ST.swap_array (R := ST.model_refs) (V := V) (ST.MkArrayLoc base n) l r) m Q.
  Proof.
    intros Hrep Hlen Hl Hr HQ. unfold ST.swap_array.
    apply spec_bind. eapply read_array_rep; [ eassumption | eassumption | exact Hl |].
    apply spec_bind. eapply read_array_rep; [ eassumption | eassumption | exact Hr |].
    apply spec_bind. eapply write_array; [ exact Hl |].
    eapply write_array; [ exact Hr |].
    apply HQ, arr_rep_swap; [ exact Hrep | lia | lia ].
  Qed.

  (** Reading back a represented array returns its list. *)
  Lemma array_to_list_rep base n full m (Q : mem V -> list nat -> Prop) :
    arr_rep m base full -> length full = n -> Q m full ->
    spec (E := E) (ST.array_to_list (R := ST.model_refs) (V := V) (ST.MkArrayLoc base n)) m Q.
  Proof.
    intros Hrep Hlen HQ. eapply array_to_list; [ exact Hlen | | exact HQ ].
    intros k Hk. rewrite Hrep by lia. symmetry. apply nth_error_nth'. lia.
  Qed.

  (** An array made from [xs] represents [xs]. *)
  Lemma array_of_list_rep xs m (Q : mem V -> ST.ArrayLoc nat -> Prop) :
    (forall base m', arr_rep m' base xs -> Q m' (ST.MkArrayLoc base (length xs))) ->
    spec (E := E) (ST.array_of_list (R := ST.model_refs) (V := V) xs) m Q.
  Proof.
    intros HQ. apply array_of_list. intros base m' Hcells. apply HQ.
    intros k Hk. rewrite Hcells by exact Hk. apply nth_error_nth'. exact Hk.
  Qed.

End NatArrays.
