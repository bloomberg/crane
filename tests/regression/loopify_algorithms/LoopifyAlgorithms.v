(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

(** Consolidated UNIQUE list/sequence algorithms. *)
Module LoopifyAlgorithms.

Fixpoint len_impl (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_impl xs)
  end.

(* ========== SEQUENCE TRANSFORMATIONS ========== *)

(** [sieve l] Sieve of Eratosthenes - filters out multiples. *)
Fixpoint sieve_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let fix filter_multiples p rest :=
        match rest with
        | nil => nil
        | cons y ys =>
          if Nat.eqb (Nat.modulo y p) O
          then filter_multiples p ys
          else cons y (filter_multiples p ys)
        end
      in cons x (sieve_fuel f (filter_multiples x xs))
    end
  end.

Definition sieve (l : list nat) : list nat :=
  sieve_fuel (len_impl l) l.

(** [run_length_encode l] encodes consecutive runs: [1,1,2,3,3,3] -> [(1,2),(2,1),(3,3)]. *)
Fixpoint run_length_encode (l : list nat) : list (nat * nat) :=
  match l with
  | nil => nil
  | cons x xs =>
    match run_length_encode xs with
    | nil => cons (x, 1) nil
    | cons (y, n) rest =>
      if Nat.eqb x y
      then cons (y, S n) rest
      else cons (x, 1) (cons (y, n) rest)
    end
  end.

(** [prefix_sums acc l] cumulative sums: [1,2,3] with acc=0 -> [0,1,3,6]. *)
Fixpoint prefix_sums (acc : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons acc nil
  | cons x xs => cons acc (prefix_sums (Nat.add acc x) xs)
  end.

(** [differences l] consecutive differences: [5,3,8,2] -> [-2,5,-6]. *)
Fixpoint differences (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x (cons y rest as ys) => cons (Nat.sub y x) (differences ys)
  end.

(** [rotate_left n l] rotates list left by n positions. *)
Fixpoint rotate_left_fuel (fuel : nat) (n : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    if Nat.leb n O then l
    else
      match l with
      | nil => nil
      | cons x xs => rotate_left_fuel f (Nat.sub n 1) (app xs (cons x nil))
      end
  end.

Definition rotate_left (n : nat) (l : list nat) : list nat :=
  rotate_left_fuel n n l.

(** [nub l] removes ALL duplicates (not just consecutive): [1,2,1,3,2] -> [1,2,3]. *)
Fixpoint nub_aux (l : list nat) (fuel : nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let fix filter_out val rest :=
        match rest with
        | nil => nil
        | cons y ys =>
          if Nat.eqb val y
          then filter_out val ys
          else cons y (filter_out val ys)
        end
      in cons x (nub_aux (filter_out x xs) f)
    end
  end.

Definition nub (l : list nat) : list nat :=
  nub_aux l (len_impl l).

(** Internal helpers for palindrome check. *)
Fixpoint rev_impl (acc : list nat) (l : list nat) : list nat :=
  match l with
  | nil => acc
  | cons x xs => rev_impl (cons x acc) xs
  end.

Fixpoint list_eq_impl (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons x xs, cons y ys => if Nat.eqb x y then list_eq_impl xs ys else false
  | _, _ => false
  end.

(** [is_palindrome l] checks if list reads same forwards and backwards. *)
Definition is_palindrome (l : list nat) : bool :=
  list_eq_impl l (rev_impl nil l).

(** [windows n l] sliding windows of size n: windows 2 [1,2,3,4] -> [[1,2],[2,3],[3,4]]. *)
Fixpoint take_impl (k : nat) (l : list nat) : list nat :=
  match k, l with
  | O, _ => nil
  | S m, cons x xs => cons x (take_impl m xs)
  | _, nil => nil
  end.

Fixpoint windows_aux (n : nat) (l : list nat) (fuel : nat) : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons _ rest =>
      if Nat.ltb (len_impl l) n then nil
      else cons (take_impl n l) (windows_aux n rest f)
    end
  end.

Definition windows (n : nat) (l : list nat) : list (list nat) :=
  windows_aux n l (S (len_impl l)).

(** [sliding_pairs l] returns consecutive pairs: [1,2,3,4] -> [(1,2),(2,3),(3,4)]. *)
Fixpoint sliding_pairs (l : list nat) : list (nat * nat) :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x (cons y rest as ys) => cons (x, y) (sliding_pairs ys)
  end.

(** [max_prefix_sum l] maximum sum of prefix (Kadane-like pattern). *)
Fixpoint max_prefix_sum (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let rest := max_prefix_sum xs in
    let sum := Nat.add x rest in
    if Nat.eqb rest O then O else if Nat.ltb rest sum then sum else rest
  end.

(** [weighted_sum i l] computes weighted sum with increasing index. *)
Fixpoint weighted_sum (i : nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs => Nat.add (Nat.mul i x) (weighted_sum (S i) xs)
  end.

(** [step_sum l] sums with conditional doubling for odd numbers. *)
Fixpoint step_sum (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let contribution := if Nat.eqb (Nat.modulo x 2) O then x else Nat.mul x 2 in
    Nat.add contribution (step_sum xs)
  end.

(** Helper: get head with default value. *)
Definition head_nat (d : nat) (l : list nat) : nat :=
  match l with
  | nil => d
  | cons h _ => h
  end.

(** [suffix_sums l] computes suffix sums (reverse of prefix sums). *)
Fixpoint suffix_sums (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    let rest := suffix_sums xs in
    cons (Nat.add x (head_nat O rest)) rest
  end.

End LoopifyAlgorithms.

Set Crane Loopify.
Crane Extraction "loopify_algorithms" LoopifyAlgorithms.
