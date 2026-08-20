(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia PeanoNat.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

(** A stack is just a [list], used as one half of a tape zipper. *)
Definition stack {A : Type} : Type := list A.
(** The empty stack. *)
Definition empty_stack {A : Type} : @stack A := [].

(** A tape is a zipper pair of optional-element stacks representing elements to the left and right of a cursor. *)
Definition tape {A : Type} : Type := (@stack (option A)) * (@stack (option A)).
(** The tape with no elements and cursor at position zero. *)
Definition empty_tape {A : Type} : (@tape A) := (empty_stack, empty_stack).

(** Total number of elements (left + right) stored in a tape. *)
Definition length_tape {A : Type} (T : @tape A) : nat :=
  match T with (X, Y) => length X + length Y end.

(** Helper that rewinds a tape by moving all left-stack elements onto the right stack. *)
Fixpoint reset_tape' {A : Type} (X Y : @stack (option A))
  : (@stack (option A)) * (@stack (option A)) :=
  match X with
  | [] => (X, Y)
  | x :: xs => reset_tape' xs (x :: Y)
  end.

(** Rewind a tape so the cursor is at position zero (left stack becomes empty). *)
Definition reset_tape {A : Type} (T : @tape A) : (@tape A) :=
  match T with
    (X, Y) => reset_tape' X Y
  end.

(** Helper that advances the tape cursor to index [i] and writes [x] at that position. *)
Fixpoint set_tape' {A : Type} (x : A) (i : nat) (T : @tape A) : @tape A :=
  match i with
  | 0 =>
    match T with
    | (xs, []) => (xs, [Some x])
    | (xs, y :: ys) => (xs, (Some x) :: ys) end
  | S n =>
    match T with
    | (xs, []) => set_tape' x n (None :: xs, [])
    | (xs, y :: ys) => set_tape' x n (y :: xs, ys)
    end
  end.

(** Write [x] at index [i] in tape [T], rewinding first so indexing is absolute. *)
Definition set_tape {A : Type} (x : A) (i : nat) (T : @tape A) : @tape A :=
  set_tape' x i (reset_tape T).

(** Helper that advances the cursor to index [i] from the current tape position and reads. *)
Fixpoint get_tape' {A : Type} (i : nat) (T : @tape A) : option A :=
  match i with
  | 0 =>
    match T with
    | (_, []) => None
    | (_, y :: ys) => y
    end
  | S n =>
    match T with
    | (_, []) => None
    | (xs, y :: ys) => get_tape' n (y :: xs, ys)
    end
  end.

(** Read the element at absolute index [i] in tape [T], rewinding first. *)
Definition get_tape {A : Type} (i : nat) (T : @tape A) : option A :=
  get_tape' i (reset_tape T).

(** After [reset_tape], the left stack is always empty; proved by induction on the original left stack. *)
Lemma reset_tape_empty : forall {A : Type} (T : @tape A) X Y,
    reset_tape T = (X, Y) -> X = [].
Proof.
  intros. destruct T. simpl in H.
  generalize dependent X. generalize dependent Y. generalize dependent s0.
  induction s; intros.
  - sis. inj_all. auto.
  - sis. eapply IHs; eauto.
Qed.


(** [get_tape'] ignores the left stack and reads position [n] from the right stack. *)
Lemma get_tape'_nth : forall {A : Type} (n : nat) (xs ys : @stack (option A)),
    get_tape' n (xs, ys) = nth n ys None.
Proof.
  induction n; destruct ys; simpl; auto.
Qed.

(** [reset_tape'] reverses the left stack onto the right stack. *)
Lemma reset_tape'_spec : forall {A : Type} (xs ys : @stack (option A)),
    reset_tape' xs ys = ([], rev xs ++ ys).
Proof.
  induction xs; intros; simpl.
  - auto.
  - rewrite IHxs. rewrite <- app_assoc. auto.
Qed.

(** [nth] at any index of the empty list returns the default. *)
Lemma nth_nil : forall {A : Type} (n : nat) (d : A), nth n [] d = d.
Proof. destruct n; reflexivity. Qed.

(** Appending [None] to a list does not change [nth] with default [None]. *)
Lemma nth_app_None : forall {A : Type} (l : list (option A)) (n : nat),
    nth n (l ++ [None]) None = nth n l None.
Proof.
  induction l as [|a l' IH].
  - destruct n; simpl; [| apply nth_nil]; reflexivity.
  - intros [|n]; simpl; [reflexivity | apply IH].
Qed.

(** [nth] at a position other than [length l] is unaffected by appending a single element. *)
Lemma nth_app_singleton : forall {A : Type} (l : list A) (a : A) (j : nat) (d : A),
    j <> length l -> nth j (l ++ [a]) d = nth j l d.
Proof.
  induction l as [|x l' IH]; intros a j d Hneq; destruct j; sis.
  - contradiction.
  - apply nth_nil.
  - reflexivity.
  - apply IH. lia.
Qed.

(** Replacing the element at position [length l] in [l ++ a :: r] leaves all other positions unchanged. *)
Lemma nth_app_cons_diff : forall {A : Type} (l : list A) (a b : A) (r : list A) (j : nat) (d : A),
    j <> length l -> nth j (l ++ a :: r) d = nth j (l ++ b :: r) d.
Proof.
  induction l as [|x l' IH]; intros a b r j d Hneq; destruct j; sis.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - apply IH. lia.
Qed.

(** Generalized: setting position [i] relative to [(xs, ys)] places [Some x] at
    absolute position [length xs + i] in the flattened tape. *)
Lemma set_tape'_nth_eq : forall {A : Type} (x : A) (i : nat)
    (xs ys xs' ys' : @stack (option A)),
    set_tape' x i (xs, ys) = (xs', ys') ->
    nth (length xs + i) (rev xs' ++ ys') None = Some x.
Proof.
  induction i; intros xs [|o ys0] xs' ys' Hset; simpl in Hset.
  - inv Hset. rewrite Nat.add_0_r. rewrite app_nth2 by (rewrite length_rev; lia).
    rewrite length_rev, Nat.sub_diag. auto.
  - inv Hset. rewrite Nat.add_0_r. rewrite app_nth2 by (rewrite length_rev; lia).
    rewrite length_rev, Nat.sub_diag. auto.
  - replace (length xs + S i) with (length (None :: xs) + i) by (simpl; lia).
    eapply IHi; eauto.
  - replace (length xs + S i) with (length (o :: xs) + i) by (simpl; lia).
    eapply IHi; eauto.
Qed.

(** Generalized: setting position [i] does not affect any other absolute position [j]. *)
Lemma set_tape'_nth_neq : forall {A : Type} (x : A) (i j : nat)
    (xs ys xs' ys' : @stack (option A)),
    set_tape' x i (xs, ys) = (xs', ys') ->
    j <> length xs + i ->
    nth j (rev xs' ++ ys') None = nth j (rev xs ++ ys) None.
Proof.
  induction i; intros j xs [|o ys0] xs' ys' Hset Hneq; simpl in Hset.
  - inv Hset. rewrite Nat.add_0_r in *. rewrite app_nil_r.
    apply nth_app_singleton. rewrite length_rev. auto.
  - inv Hset. rewrite Nat.add_0_r in *.
    apply nth_app_cons_diff. rewrite length_rev. auto.
  - transitivity (nth j (rev (None :: xs) ++ []) None).
    + eapply IHi; eauto. simpl. lia.
    + repeat rewrite app_nil_r.
      change (rev (None :: xs)) with (rev xs ++ [None]).
      apply nth_app_None.
  - transitivity (nth j (rev (o :: xs) ++ ys0) None).
    + eapply IHi; eauto. simpl. lia.
    + change (rev (o :: xs)) with (rev xs ++ [o]).
      rewrite <- app_assoc. reflexivity.
Qed.

(** Setting index [i] in a tape and reading it back yields [Some x]. *)
Lemma get_of_set_eq : forall {A : Type} (x : A) (i : nat) (T : @tape A),
    get_tape i (set_tape x i T) = Some x.
Proof.
  intros. unfold get_tape, set_tape. destruct T as [xs ys].
  simpl reset_tape. rewrite reset_tape'_spec.
  destruct (set_tape' x i ([], rev xs ++ ys)) as [a b] eqn:Eset.
  simpl reset_tape. rewrite reset_tape'_spec, get_tape'_nth.
  exact (set_tape'_nth_eq x i [] (rev xs ++ ys) a b Eset).
Qed.

(** Setting index [i] does not affect reading at a different index [j]. *)
Lemma get_of_set_neq : forall {A : Type} (x : A) (i j : nat) (T : @tape A),
    i <> j -> get_tape j (set_tape x i T) = get_tape j T.
Proof.
  intros. unfold get_tape, set_tape. destruct T as [xs ys].
  simpl reset_tape. rewrite reset_tape'_spec.
  destruct (set_tape' x i ([], rev xs ++ ys)) as [a b] eqn:Eset.
  simpl reset_tape. repeat rewrite reset_tape'_spec.
  repeat rewrite get_tape'_nth.
  apply (set_tape'_nth_neq x i j [] (rev xs ++ ys) a b Eset).
  simpl. intros C. apply H. auto.
Qed.

(** The empty tape contains [None] at every index. *)
Lemma get_empty_tape : forall {A : Type} (i : nat),
    @get_tape A i empty_tape = None.
Proof.
  intros. unfold get_tape, empty_tape. simpl.
  rewrite get_tape'_nth. apply nth_nil.
Qed.

(* Return left of the current tape pointer, update the tape pointer to point there *)
(** Return the element immediately left of the cursor and move the cursor there; returns [None] if at the start. *)
Definition get_left_tape {A : Type} (T : @tape A) :
  (option A) * @tape A :=
  match T with
  | ([], _) => (None, T)
  | (x :: xs, ys) => (x, (xs, x :: ys))
  end.

(** Return the element immediately right of the cursor and move the cursor there; returns [None] if at or past the end. *)
Definition get_right_tape {A : Type} (T : @tape A) :
  (option A) * @tape A :=
  match T with
  | (_, []) => (None, T)
  | (_, [y]) => (None, T)
  | (xs, y0 :: y1 :: ys) => (y1, (y0 :: xs, y1 :: ys))
  end.
