(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

(** Consolidated UNIQUE sorting algorithms and related operations. *)
Module LoopifySorting.

Fixpoint len_impl {A : Type} (l : list A) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_impl xs)
  end.

(* ========== INSERTION SORT ========== *)

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons x nil
  | cons h t => if Nat.leb x h then cons x l else cons h (insert x t)
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => insert x (insertion_sort xs)
  end.

(* ========== MERGE SORT ========== *)

Fixpoint split {A : Type} (l : list A) : (list A * list A) :=
  match l with
  | nil => (nil, nil)
  | cons x nil => (cons x nil, nil)
  | cons x (cons y rest) =>
    let '(l1, l2) := split rest in
    (cons x l1, cons y l2)
  end.

Fixpoint merge_fuel (fuel : nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons x xs, cons y ys =>
      if Nat.leb x y
      then cons x (merge_fuel f xs l2)
      else cons y (merge_fuel f l1 ys)
    end
  end.

Definition merge (l1 l2 : list nat) : list nat :=
  merge_fuel (Nat.add (len_impl l1) (len_impl l2)) l1 l2.

Fixpoint merge_sort_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons _ nil => l
    | _ =>
      let '(l1, l2) := split l in
      merge (merge_sort_fuel f l1) (merge_sort_fuel f l2)
    end
  end.

Definition merge_sort (l : list nat) : list nat :=
  merge_sort_fuel (len_impl l) l.

(* ========== QUICKSORT ========== *)

Fixpoint partition (pivot : nat) (l : list nat) : (list nat * list nat) :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    let '(lo, hi) := partition pivot xs in
    if Nat.leb x pivot
    then (cons x lo, hi)
    else (lo, cons x hi)
  end.

Fixpoint quicksort_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons pivot rest =>
      let '(lo, hi) := partition pivot rest in
      app (quicksort_fuel f lo) (cons pivot (quicksort_fuel f hi))
    end
  end.

Definition quicksort (l : list nat) : list nat :=
  quicksort_fuel (len_impl l) l.

(* ========== SORTING UTILITIES ========== *)

Fixpoint is_sorted_aux (prev : nat) (l : list nat) : bool :=
  match l with
  | nil => true
  | cons x xs =>
    if Nat.leb prev x then is_sorted_aux x xs else false
  end.

Definition is_sorted (l : list nat) : bool :=
  match l with
  | nil => true
  | cons x xs => is_sorted_aux x xs
  end.

(** [merge_by cmp] merges with custom comparator. *)
Fixpoint merge_by_fuel (fuel : nat) (cmp : nat -> nat -> bool)
                        (l1 l2 : list nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons x xs, cons y ys =>
      if cmp x y
      then cons x (merge_by_fuel f cmp xs l2)
      else cons y (merge_by_fuel f cmp l1 ys)
    end
  end.

Definition merge_by (cmp : nat -> nat -> bool) (l1 l2 : list nat) : list nat :=
  merge_by_fuel (Nat.add (len_impl l1) (len_impl l2)) cmp l1 l2.

(** [remove_duplicates] removes consecutive duplicates from sorted list. *)
Fixpoint remove_duplicates (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x (cons y ys as rest) =>
    if Nat.eqb x y
    then remove_duplicates rest
    else cons x (remove_duplicates rest)
  end.

(** [uniq_sorted] variant that preserves order. *)
Fixpoint uniq_sorted_aux (prev : nat) (seen : bool) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if seen then
      if Nat.eqb prev x
      then uniq_sorted_aux x true xs
      else cons x (uniq_sorted_aux x true xs)
    else cons x (uniq_sorted_aux x true xs)
  end.

Definition uniq_sorted (l : list nat) : list nat :=
  uniq_sorted_aux O false l.

End LoopifySorting.

Set Crane Loopify.
Crane Extraction "loopify_sorting" LoopifySorting.
