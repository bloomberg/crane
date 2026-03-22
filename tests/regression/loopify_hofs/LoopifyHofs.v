(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyHofs.

(** [foldl1 f l] folds from left with no initial value. Returns 0 for empty list. *)
Fixpoint foldl1_aux {A : Type} (f : A -> A -> A) (acc : A) (l : list A) : A :=
  match l with
  | nil => acc
  | cons x xs => foldl1_aux f (f acc x) xs
  end.

Definition foldl1 {A : Type} (f : A -> A -> A) (default : A) (l : list A) : A :=
  match l with
  | nil => default
  | cons x xs => foldl1_aux f x xs
  end.

(** [forall_ p l] checks if all elements satisfy predicate p. *)
Fixpoint forall_ {A : Type} (p : A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | cons x xs => if p x then forall_ p xs else false
  end.

(** [exists_fn p l] checks if any element satisfies predicate p. *)
Fixpoint exists_fn {A : Type} (p : A -> bool) (l : list A) : bool :=
  match l with
  | nil => false
  | cons x xs => if p x then true else exists_fn p xs
  end.

(** [drop_while p l] drops elements while predicate holds. *)
Fixpoint drop_while {A : Type} (p : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => if p x then drop_while p xs else cons x xs
  end.

(** [take_while p l] takes elements while predicate holds. *)
Fixpoint take_while {A : Type} (p : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => if p x then cons x (take_while p xs) else nil
  end.

(** [flat_map f l] maps f and flattens results. *)
Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => app (f x) (flat_map f xs)
  end.

(** [all_pairs l1 l2] returns all pairs from two lists. *)
Fixpoint all_pairs {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  let fix pair_with x l :=
    match l with
    | nil => nil
    | cons y ys => cons (x, y) (pair_with x ys)
    end
  in
  match l1 with
  | nil => nil
  | cons x xs => app (pair_with x l2) (all_pairs xs l2)
  end.

(** [find_indices p l] finds all indices where p is true. *)
Fixpoint find_indices_aux (p : nat -> bool) (l : list nat) (i : nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p x
    then cons i (find_indices_aux p xs (S i))
    else find_indices_aux p xs (S i)
  end.

Definition find_indices (p : nat -> bool) (l : list nat) : list nat :=
  find_indices_aux p l O.

(** [delete_by eq x l] deletes first element equal to x. *)
Fixpoint delete_by (eq : nat -> nat -> bool) (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons y ys => if eq x y then ys else cons y (delete_by eq x ys)
  end.

(** [is_prefix_of l1 l2] checks if l1 is a prefix of l2. *)
Fixpoint is_prefix_of (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, _ => true
  | cons _ _, nil => false
  | cons x xs, cons y ys => if Nat.eqb x y then is_prefix_of xs ys else false
  end.

(** [lookup_all key l] finds all values associated with key in association list. *)
Fixpoint lookup_all (key : nat) (l : list (nat * nat)) : list nat :=
  match l with
  | nil => nil
  | cons (k, v) xs =>
    if Nat.eqb k key
    then cons v (lookup_all key xs)
    else lookup_all key xs
  end.

(* ========== SCAN & FOLD VARIANTS ========== *)

(** [scanl f acc l] scan from left with accumulator. *)
Fixpoint scanl (f : nat -> nat -> nat) (acc : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons acc nil
  | cons x xs => cons acc (scanl f (f acc x) xs)
  end.

(** [scanl1 f l] like scanl but no initial value, uses first element. *)
Fixpoint scanl1_fuel (fuel : nat) (f : nat -> nat -> nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S g =>
    match l with
    | nil => nil
    | cons x nil => cons x nil
    | cons x (cons y rest) =>
      cons x (scanl1_fuel g f (cons (f x y) rest))
    end
  end.

Definition scanl1 (f : nat -> nat -> nat) (l : list nat) : list nat :=
  scanl1_fuel (length l) f l.

(** [foldr1 f l] fold right with no initial value. *)
Fixpoint foldr1 (f : nat -> nat -> nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => x
  | cons x xs => f x (foldr1 f xs)
  end.

(** Helper: get head of list with default. *)
Fixpoint head_default (default : nat) (l : list nat) : nat :=
  match l with
  | nil => default
  | cons h _ => h
  end.

(** [scanr f acc l] scan from right. *)
Fixpoint scanr (f : nat -> nat -> nat) (acc : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons acc nil
  | cons x xs =>
    let rest := scanr f acc xs in
    let h := head_default acc rest in
    cons (f x h) rest
  end.

(** [scanr1 f l] scanr with no initial value. *)
Fixpoint scanr1 (f : nat -> nat -> nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x xs =>
    let rest := scanr1 f xs in
    let h := head_default x rest in
    cons (f x h) rest
  end.

(** [mapcat f l] maps f and concatenates results (concat_map). *)
Fixpoint mapcat {A : Type} (f : nat -> list A) (l : list nat) : list A :=
  match l with
  | nil => nil
  | cons x xs => app (f x) (mapcat f xs)
  end.

(** [map_maybe f l] maps f and filters out None results. *)
Fixpoint map_maybe (f : nat -> option nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    let rest := map_maybe f xs in
    match f x with
    | Some y => cons y rest
    | None => rest
    end
  end.

(** [bool_all p l] checks if all elements satisfy p (same as forall_). *)
Fixpoint bool_all (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | nil => true
  | cons x xs => andb (p x) (bool_all p xs)
  end.

(** [merge_by cmp l1 l2] merges two lists using comparison function. *)
Fixpoint merge_by_fuel (fuel : nat) (cmp : nat -> nat -> nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | O => l1
  | S f =>
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons x xs, cons y ys =>
      if Nat.leb (cmp x y) O
      then cons x (merge_by_fuel f cmp xs l2)
      else cons y (merge_by_fuel f cmp l1 ys)
    end
  end.

Definition merge_by (cmp : nat -> nat -> nat) (l1 l2 : list nat) : list nat :=
  merge_by_fuel (Nat.add (length l1) (length l2)) cmp l1 l2.

(** [max_by f l] finds element with maximum f value. *)
Fixpoint max_by (f : nat -> nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => f x
  | cons x xs =>
    let rest_max := max_by f xs in
    let fx := f x in
    if Nat.leb rest_max fx then fx else rest_max
  end.

(** [iterate f n x] generates [x, f(x), f(f(x)), ...] of length n. *)
Fixpoint iterate (f : nat -> nat) (n : nat) (x : nat) : list nat :=
  match n with
  | O => nil
  | S m => cons x (iterate f m (f x))
  end.

(** [maximum_by cmp l] finds maximum element by comparison function. *)
Fixpoint maximum_by (cmp : nat -> nat -> nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => x
  | cons x xs =>
    let m := maximum_by cmp xs in
    if Nat.leb O (cmp x m) then x else m
  end.

(** [fold_right f l acc] folds from the right. *)
Fixpoint fold_right (f : nat -> nat -> nat) (l : list nat) (acc : nat) : nat :=
  match l with
  | nil => acc
  | cons x xs => f x (fold_right f xs acc)
  end.

(** [partition p l] partitions list into (satisfies p, doesn't satisfy p). *)
Fixpoint partition (p : nat -> bool) (l : list nat) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    let '(yes, no) := partition p xs in
    if p x
    then (cons x yes, no)
    else (yes, cons x no)
  end.

(* ========== COMBINATORIAL GENERATORS ========== *)

(** [subsequences l] generates all subsequences of l: [1,2] -> [[],[1],[2],[1,2]]. *)
Fixpoint subsequences (l : list nat) : list (list nat) :=
  match l with
  | nil => cons nil nil
  | cons x xs =>
    let rest := subsequences xs in
    let fix map_cons_x lsts :=
      match lsts with
      | nil => nil
      | cons lst rest_lsts => cons (cons x lst) (map_cons_x rest_lsts)
      end
    in
    app rest (map_cons_x rest)
  end.

(** Helper: pair element with all elements in list. *)
Fixpoint pair_with_all (x : nat) (l : list nat) : list (nat * nat) :=
  match l with
  | nil => nil
  | cons y ys => cons (x, y) (pair_with_all x ys)
  end.

(** [cartesian l1 l2] computes cartesian product of two lists. *)
Fixpoint cartesian (l1 l2 : list nat) : list (nat * nat) :=
  match l1 with
  | nil => nil
  | cons x xs => app (pair_with_all x l2) (cartesian xs l2)
  end.

(** [longest_run l] finds the longest consecutive run of equal elements.
    Matches on recursive result to decide behavior. *)
Fixpoint longest_run_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x nil => cons x nil
    | cons x (cons y rest) =>
      if Nat.eqb x y then
        cons x (longest_run_fuel f (cons y rest))
      else
        let rec_result := longest_run_fuel f (cons y rest) in
        match rec_result with
        | nil => cons x nil
        | cons h _ =>
          if Nat.eqb x h then rec_result else rec_result
        end
    end
  end.

Definition longest_run (l : list nat) : list nat :=
  longest_run_fuel (length l) l.

(* ========== ADDITIONAL HOF PATTERNS ========== *)

(** [any p l] checks if any element satisfies predicate (same as exists_fn but different name). *)
Fixpoint any (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons x xs => if p x then true else any p xs
  end.

(** [all p l] checks if all elements satisfy predicate (same as forall_ but different name). *)
Fixpoint all (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | nil => true
  | cons x xs => if p x then all p xs else false
  end.

(** [filter_not p l] filters elements that don't satisfy predicate. *)
Fixpoint filter_not (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p x
    then filter_not p xs
    else cons x (filter_not p xs)
  end.

(** [span_split p l] splits at first element that doesn't satisfy p. *)
Fixpoint span_split (p : nat -> bool) (l : list nat) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    if p x
    then
      let '(taken, rest) := span_split p xs in
      (cons x taken, rest)
    else (nil, cons x xs)
  end.

(** [group_by_eq eq l] groups consecutive elements by equality function. *)
Fixpoint group_by_eq_fuel (fuel : nat) (eq : nat -> nat -> bool) (l : list nat) : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x nil => cons (cons x nil) nil
    | cons x (cons y rest as ys) =>
      if eq x y then
        match group_by_eq_fuel f eq ys with
        | nil => cons (cons x nil) nil
        | cons g gs => cons (cons x g) gs
        end
      else cons (cons x nil) (group_by_eq_fuel f eq ys)
    end
  end.

Definition group_by_eq (eq : nat -> nat -> bool) (l : list nat) : list (list nat) :=
  group_by_eq_fuel (length l) eq l.

(** [power_set l] generates all subsets. *)
Fixpoint power_set (l : list nat) : list (list nat) :=
  match l with
  | nil => cons nil nil
  | cons x xs =>
    let sub := power_set xs in
    let fix map_cons_x lsts :=
      match lsts with
      | nil => nil
      | cons lst rest => cons (cons x lst) (map_cons_x rest)
      end
    in
    app sub (map_cons_x sub)
  end.

(** [map_accum_l f acc l] maps with accumulator threading. *)
Fixpoint map_accum_l (f : nat -> nat -> nat * nat) (acc : nat) (l : list nat) : nat * list nat :=
  match l with
  | nil => (acc, nil)
  | cons x xs =>
    let '(acc', y) := f acc x in
    let '(acc'', ys) := map_accum_l f acc' xs in
    (acc'', cons y ys)
  end.

End LoopifyHofs.

Set Crane Loopify.
Crane Extraction "loopify_hofs" LoopifyHofs.
