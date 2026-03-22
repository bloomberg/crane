(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Consolidated search and optimization algorithms. *)
Module LoopifySearch.

(** Internal helper: list length. *)
Fixpoint len_impl {A : Type} (l : list A) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_impl xs)
  end.

(* ========== OPTIMIZATION PROBLEMS ========== *)

(** [knapsack capacity items] solves 0/1 knapsack problem.
    Items are (weight, value) pairs. *)
Fixpoint knapsack_fuel (fuel : nat) (capacity : nat) (items : list (nat * nat)) : nat :=
  match fuel with
  | O => O
  | S f =>
    match items with
    | nil => O
    | cons (weight, value) rest =>
      if Nat.ltb capacity weight
      then knapsack_fuel f capacity rest
      else
        if Nat.leb (knapsack_fuel f capacity rest)
                   (Nat.add value (knapsack_fuel f (Nat.sub capacity weight) rest))
        then Nat.add value (knapsack_fuel f (Nat.sub capacity weight) rest)
        else knapsack_fuel f capacity rest
    end
  end.

Definition knapsack (capacity : nat) (items : list (nat * nat)) : nat :=
  knapsack_fuel (len_impl items) capacity items.

(** [majority l] finds majority element using Boyer-Moore algorithm.
    Returns (candidate, count). *)
Fixpoint majority (l : list nat) : (nat * nat) :=
  match l with
  | nil => (O, O)
  | cons x xs =>
    let '(cand, count) := majority xs in
    if Nat.eqb x cand then (cand, S count)
    else if Nat.ltb O count then (cand, Nat.sub count 1)
    else (x, 1)
  end.

(** [longest_increasing_subseq l] finds a longest increasing subsequence (greedy). *)
Fixpoint longest_increasing_subseq (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x (cons y rest as ys) =>
    if Nat.ltb x y
    then cons x (longest_increasing_subseq ys)
    else longest_increasing_subseq ys
  end.

(** [maximum_by cmp l] finds maximum element by custom comparator.
    cmp x y returns: 0 if x=y, 1 if x>y, 2 if x<y *)
Fixpoint maximum_by (cmp : nat -> nat -> nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => x
  | cons x xs =>
    let m := maximum_by cmp xs in
    if Nat.eqb (cmp x m) 1 then x else m
  end.

(** Helper for binary search: get nth element. *)
Fixpoint nth_impl (n : nat) (l : list nat) : nat :=
  match n, l with
  | O, cons x _ => x
  | S m, cons _ xs => nth_impl m xs
  | _, nil => O
  end.

(** Helper for binary search: take first k elements. *)
Fixpoint take_impl (k : nat) (l : list nat) : list nat :=
  match k, l with
  | O, _ => nil
  | S m, cons x xs => cons x (take_impl m xs)
  | _, nil => nil
  end.

(** Helper for binary search: drop first k elements. *)
Fixpoint drop_impl (k : nat) (l : list nat) : list nat :=
  match k, l with
  | O, l => l
  | S m, cons _ xs => drop_impl m xs
  | _, nil => nil
  end.

(** [binary_search_fuel target sorted_list] searches for target in sorted list.
    Returns true if found. *)
Fixpoint binary_search_fuel (fuel : nat) (target : nat) (l : list nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    let n := len_impl l in
    match n with
    | O => false
    | _ =>
      let mid := Nat.div n 2 in
      let mid_val := nth_impl mid l in
      if Nat.eqb target mid_val then true
      else if Nat.ltb target mid_val
      then binary_search_fuel f target (take_impl mid l)
      else binary_search_fuel f target (drop_impl (S mid) l)
    end
  end.

Definition binary_search (target : nat) (l : list nat) : bool :=
  binary_search_fuel (len_impl l) target l.

(** [longest_run l] finds the longest run of consecutive equal elements. *)
Fixpoint longest_run_aux (current_run best_run : list nat) (l : list nat) : list nat :=
  match l with
  | nil =>
    if Nat.leb (len_impl current_run) (len_impl best_run)
    then best_run
    else current_run
  | cons x nil =>
    let new_run := cons x current_run in
    if Nat.leb (len_impl new_run) (len_impl best_run)
    then best_run
    else new_run
  | cons x (cons y rest as ys) =>
    if Nat.eqb x y
    then longest_run_aux (cons x current_run) best_run ys
    else
      let new_run := cons x current_run in
      let new_best := if Nat.leb (len_impl new_run) (len_impl best_run) then best_run else new_run in
      longest_run_aux nil new_best ys
  end.

Definition longest_run (l : list nat) : list nat :=
  longest_run_aux nil nil l.

(* ========== SEQUENCE SEARCH ALGORITHMS ========== *)

(** [collatz n] computes Collatz sequence length (not the list). *)
Fixpoint collatz_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    if Nat.eqb n 1 then O
    else if Nat.eqb (Nat.modulo n 2) O
    then S (collatz_fuel f (Nat.div n 2))
    else S (collatz_fuel f (Nat.add (Nat.mul 3 n) 1))
  end.

Definition collatz (n : nat) : nat :=
  collatz_fuel 1000 n.

(** [lis l] simple longest increasing subsequence (greedy approach). *)
Fixpoint lis (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x (cons y rest as xs) =>
    if Nat.ltb x y
    then cons x (lis xs)
    else lis xs
  end.

(** [subset_sum target l] checks if any subset sums to target. *)
Fixpoint subset_sum_fuel (fuel : nat) (target : nat) (l : list nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    match l with
    | nil => Nat.eqb target O
    | cons x xs =>
      let without := subset_sum_fuel f target xs in
      if without then true
      else
        if Nat.leb x target
        then subset_sum_fuel f (Nat.sub target x) xs
        else false
    end
  end.

Definition subset_sum (target : nat) (l : list nat) : bool :=
  subset_sum_fuel (S (len_impl l)) target l.

(** Helper: filter predicate. *)
Fixpoint filter_impl (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p x
    then cons x (filter_impl p xs)
    else filter_impl p xs
  end.

(** [sieve l] removes multiples (simplified sieve of Eratosthenes). *)
Fixpoint sieve_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      cons x (sieve_fuel f (filter_impl (fun y => negb (Nat.eqb (Nat.modulo y x) O)) xs))
    end
  end.

Definition sieve (l : list nat) : list nat :=
  sieve_fuel (len_impl l) l.

(** Helper: check if element is in list. *)
Fixpoint elem_impl (x : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons y ys => if Nat.eqb x y then true else elem_impl x ys
  end.

(** [nub l] removes duplicates from list. *)
Fixpoint nub_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      if elem_impl x xs
      then nub_fuel f xs
      else cons x (nub_fuel f xs)
    end
  end.

Definition nub (l : list nat) : list nat :=
  nub_fuel (len_impl l) l.

(** [remove_duplicates l] removes all duplicate elements. *)
Fixpoint remove_duplicates_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      if elem_impl x xs
      then remove_duplicates_fuel f xs
      else cons x (remove_duplicates_fuel f (filter_impl (fun y => negb (Nat.eqb x y)) xs))
    end
  end.

Definition remove_duplicates (l : list nat) : list nat :=
  remove_duplicates_fuel (len_impl l) l.

(* ========== SORTING ALGORITHMS ========== *)

(** [quicksort l] sorts list using quicksort with filter-based partitioning. *)
Fixpoint quicksort_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let smaller := filter_impl (fun y => Nat.ltb y x) xs in
      let greater := filter_impl (fun y => Nat.leb x y) xs in
      app (quicksort_fuel f smaller) (cons x (quicksort_fuel f greater))
    end
  end.

Definition quicksort (l : list nat) : list nat :=
  quicksort_fuel (len_impl l) l.

(** Helper: split list into two roughly equal parts. *)
Fixpoint split_list (l : list nat) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons x nil => (cons x nil, nil)
  | cons x (cons y rest) =>
    let '(a, b) := split_list rest in
    (cons x a, cons y b)
  end.

(** Helper: merge two sorted lists with fuel. *)
Fixpoint merge_sorted_fuel (fuel : nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | O => app l1 l2
  | S f =>
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons x xs, cons y ys =>
      if Nat.leb x y
      then cons x (merge_sorted_fuel f xs l2)
      else cons y (merge_sorted_fuel f l1 ys)
    end
  end.

Definition merge_sorted (l1 l2 : list nat) : list nat :=
  merge_sorted_fuel (Nat.add (len_impl l1) (len_impl l2)) l1 l2.

(** [merge_sort l] sorts list using merge sort. *)
Fixpoint merge_sort_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons _ nil => l
    | _ =>
      let '(a, b) := split_list l in
      merge_sorted (merge_sort_fuel f a) (merge_sort_fuel f b)
    end
  end.

Definition merge_sort (l : list nat) : list nat :=
  merge_sort_fuel (len_impl l) l.

(* ========== PERMUTATIONS ========== *)

(** Helper: remove first occurrence of x from list. *)
Fixpoint remove_first (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons y ys =>
    if Nat.eqb x y then ys else cons y (remove_first x ys)
  end.

(** Helper: map function over list and concatenate results. *)
Fixpoint concat_map (f : nat -> list (list nat)) (l : list nat) : list (list nat) :=
  match l with
  | nil => nil
  | cons x xs => app (f x) (concat_map f xs)
  end.

(** Helper: map function that prepends element to each list. *)
Fixpoint map_cons (x : nat) (lsts : list (list nat)) : list (list nat) :=
  match lsts with
  | nil => nil
  | cons lst rest => cons (cons x lst) (map_cons x rest)
  end.

(** [perms_choices_fuel fuel choices orig] generates permutations by iterating
    over choices.  Single self-recursive function for full loopification.
    Match on [remaining] is hoisted out of let-binding. *)
Fixpoint perms_choices_fuel (fuel : nat) (choices orig : list nat)
                            : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    match choices with
    | nil => nil
    | cons x xs =>
      let remaining := remove_first x orig in
      match remaining with
      | nil =>
        app (map_cons x (cons nil nil))
                    (perms_choices_fuel f xs orig)
      | _ =>
        app (map_cons x (perms_choices_fuel f remaining remaining))
                    (perms_choices_fuel f xs orig)
      end
    end
  end.

(** [permutations_fuel fuel l] generates all permutations of list. *)
Definition permutations_fuel (fuel : nat) (l : list nat) : list (list nat) :=
  match l with
  | nil => cons nil nil
  | _ => perms_choices_fuel fuel l l
  end.

Definition permutations (l : list nat) : list (list nat) :=
  permutations_fuel (S (len_impl l)) l.

(* ========== SEARCH OPTIMIZATIONS ========== *)

(** [linear_search x l] finds index of first occurrence of x. *)
Fixpoint linear_search_aux (x : nat) (l : list nat) (idx : nat) : option nat :=
  match l with
  | nil => None
  | cons y ys =>
    if Nat.eqb x y then Some idx
    else linear_search_aux x ys (S idx)
  end.

Definition linear_search (x : nat) (l : list nat) : option nat :=
  linear_search_aux x l O.

(** [all_indices x l] finds all indices where x occurs. *)
Fixpoint all_indices_aux (x : nat) (l : list nat) (idx : nat) : list nat :=
  match l with
  | nil => nil
  | cons y ys =>
    if Nat.eqb x y
    then cons idx (all_indices_aux x ys (S idx))
    else all_indices_aux x ys (S idx)
  end.

Definition all_indices (x : nat) (l : list nat) : list nat :=
  all_indices_aux x l O.

(** [min_element l] finds minimum element in list. *)
Fixpoint min_element (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => x
  | cons x xs =>
    let min_rest := min_element xs in
    if Nat.leb x min_rest then x else min_rest
  end.

(** Binary tree for search operations. *)
Inductive btree : Type :=
| BLeaf : nat -> btree
| BNode : btree -> btree -> btree.

(** [or_search p t] searches tree with || recursion. *)
Fixpoint or_search (p : nat -> bool) (t : btree) : bool :=
  match t with
  | BLeaf x => p x
  | BNode l r => orb (or_search p l) (or_search p r)
  end.

(** [find_indices p l] finds all indices where predicate holds. *)
Fixpoint find_indices_aux (p : nat -> bool) (l : list nat) (idx : nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p x
    then cons idx (find_indices_aux p xs (S idx))
    else find_indices_aux p xs (S idx)
  end.

Definition find_indices (p : nat -> bool) (l : list nat) : list nat :=
  find_indices_aux p l O.

End LoopifySearch.

Set Crane Loopify.
Crane Extraction "loopify_search" LoopifySearch.
