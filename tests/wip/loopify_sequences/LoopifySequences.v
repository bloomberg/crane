(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifySequences.

(** [alternate_sum sign acc l] alternating sum with sign flip. *)
Fixpoint alternate_sum (sign : nat) (acc : nat) (l : list nat) : nat :=
  match l with
  | nil => acc
  | cons x xs =>
    let new_acc := if Nat.eqb sign 1 then Nat.add acc x else Nat.sub acc x in
    let new_sign := if Nat.eqb sign 1 then O else 1 in
    alternate_sum new_sign new_acc xs
  end.

(** [intercalate sep lists] inserts sep between lists and flattens. *)
Fixpoint intercalate {A : Type} (sep : list A) (lists : list (list A)) : list A :=
  match lists with
  | nil => nil
  | cons l nil => l
  | cons l rest => app l (app sep (intercalate sep rest))
  end.

(** [join_with sep l] joins list elements with separator. *)
Definition join_with {A : Type} (sep : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs =>
    let fix go rest :=
      match rest with
      | nil => nil
      | cons y ys => cons sep (cons y (go ys))
      end
    in cons x (go xs)
  end.

(** [transpose l] transposes a list of lists. *)
Fixpoint transpose_fuel {A : Type} (fuel : nat) (ll : list (list A)) : list (list A) :=
  match fuel with
  | O => nil
  | S f =>
    let fix all_nil l :=
      match l with
      | nil => true
      | cons xs xss =>
        match xs with
        | nil => all_nil xss
        | cons _ _ => false
        end
      end
    in
    if all_nil ll then nil
    else
      let fix heads l :=
        match l with
        | nil => nil
        | cons xs xss =>
          match xs with
          | nil => heads xss
          | cons y _ => cons y (heads xss)
          end
        end
      in
      let fix tails l :=
        match l with
        | nil => nil
        | cons xs xss =>
          match xs with
          | nil => tails xss
          | cons _ ys => cons ys (tails xss)
          end
        end
      in
      cons (heads ll) (transpose_fuel f (tails ll))
  end.

Definition transpose {A : Type} (ll : list (list A)) : list (list A) :=
  transpose_fuel 100 ll.

(** [collatz_list n] generates collatz sequence. *)
Fixpoint collatz_list_fuel (fuel : nat) (n : nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    if Nat.eqb n 1 then cons 1 nil
    else
      cons n
        (if Nat.eqb (Nat.modulo n 2) O
         then collatz_list_fuel f (Nat.div n 2)
         else collatz_list_fuel f (Nat.add (Nat.mul 3 n) 1))
  end.

Definition collatz_list (n : nat) : list nat :=
  collatz_list_fuel 1000 n.

(** [run_sum l] running sum (scanl for addition). *)
Fixpoint run_sum_aux (acc : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    let new_acc := Nat.add acc x in
    cons new_acc (run_sum_aux new_acc xs)
  end.

Definition run_sum (l : list nat) : list nat :=
  cons O (run_sum_aux O l).

(* ========== ADVANCED SEQUENCE OPERATIONS ========== *)

(** [rotate_left n l] rotates list left by n positions. *)
Fixpoint rotate_left_fuel (fuel : nat) (n : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    if Nat.eqb n O then l
    else
      match l with
      | nil => nil
      | cons x xs =>
        rotate_left_fuel f (Nat.sub n 1) (app xs (cons x nil))
      end
  end.

Definition rotate_left (n : nat) (l : list nat) : list nat :=
  rotate_left_fuel 100 n l.

(** [iterate f n x] generates [x, f x, f (f x), ...] of length n. *)
Fixpoint iterate (f : nat -> nat) (n : nat) (x : nat) : list nat :=
  match n with
  | O => nil
  | S m => cons x (iterate f m (f x))
  end.

(* ========== ACCUMULATOR & STRING OPERATIONS ========== *)

(** [sum_acc acc l] sum with accumulator. *)
Fixpoint sum_acc (acc : nat) (l : list nat) : nat :=
  match l with
  | nil => acc
  | cons x xs => sum_acc (Nat.add acc x) xs
  end.

(** [repeat_string s n] repeats string n times (using list as string). *)
Fixpoint repeat_string (s : list nat) (n : nat) : list nat :=
  match n with
  | O => nil
  | S m => app s (repeat_string s m)
  end.

(** [repeat_with_sep s sep n] repeats with separator. *)
Fixpoint repeat_with_sep (s sep : list nat) (n : nat) : list nat :=
  match n with
  | O => nil
  | S O => s
  | S m => app s (app sep (repeat_with_sep s sep m))
  end.

(** [string_chain s n] recursive string chain: s-chain(s, n-1)-end. *)
Fixpoint string_chain_fuel (fuel : nat) (s : list nat) (n : nat) (sep end_marker : list nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    if Nat.leb n O then nil
    else
      app s
        (app sep
          (app (string_chain_fuel f s (Nat.sub n 1) sep end_marker)
            (app sep end_marker)))
  end.

Definition string_chain (s : list nat) (n : nat) (sep end_marker : list nat) : list nat :=
  string_chain_fuel 1000 s n sep end_marker.

(** [split_by_sign l base pos neg] splits list based on base threshold. *)
Fixpoint split_by_sign (l : list nat) (base : nat) (pos neg : list nat) : list nat * list nat :=
  match l with
  | nil => (pos, neg)
  | cons x xs =>
    if Nat.leb base x
    then split_by_sign xs base (cons x pos) neg
    else split_by_sign xs base pos (cons x neg)
  end.

(** [differences l] computes differences between consecutive elements. *)
Fixpoint differences (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x (cons y _ as rest) =>
    cons (Nat.sub y x) (differences rest)
  end.

(** [replace_at idx value l] replaces element at index with value. *)
Fixpoint replace_at (idx value : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if Nat.eqb idx O
    then cons value xs
    else cons x (replace_at (Nat.sub idx 1) value xs)
  end.

(** [cycle n l] repeats list n times. *)
Fixpoint cycle (n : nat) (l : list nat) : list nat :=
  match n with
  | O => nil
  | S m =>
    match l with
    | nil => nil
    | _ => app l (cycle m l)
    end
  end.

(* ========== STRING-LIKE OPERATIONS (using lists) ========== *)

(** Helper: get first element. *)
Fixpoint first_elem (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x _ => x
  end.

(** Helper: get last element. *)
Fixpoint last_elem (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => x
  | cons _ xs => last_elem xs
  end.

(** Helper: remove first element. *)
Fixpoint tail_list (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ xs => xs
  end.

(** Helper: remove last element. *)
Fixpoint init_list (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x xs => cons x (init_list xs)
  end.

(** [is_palindrome s] checks if list is a palindrome. *)
Fixpoint is_palindrome_fuel (fuel : nat) (s : list nat) : bool :=
  match fuel with
  | O => true
  | S f =>
    let n := length s in
    match n with
    | O => true
    | S O => true
    | S (S m) =>
      if Nat.eqb (first_elem s) (last_elem s)
      then is_palindrome_fuel f (init_list (tail_list s))
      else false
    end
  end.

Definition is_palindrome (s : list nat) : bool :=
  is_palindrome_fuel 1000 s.

(** [string_subsequences s] generates all subsequences treating list as string. *)
Fixpoint string_subsequences (s : list nat) : list (list nat) :=
  match s with
  | nil => cons nil nil
  | cons c rest =>
    let sub_rest := string_subsequences rest in
    let fix map_prepend_c lsts :=
      match lsts with
      | nil => nil
      | cons lst lsts' => cons (cons c lst) (map_prepend_c lsts')
      end
    in
    app sub_rest (map_prepend_c sub_rest)
  end.

(** [run_length_groups l] groups consecutive runs into sublist lengths. *)
Fixpoint run_length_groups_aux (prev : nat) (count : nat) (l : list nat) : list nat :=
  match l with
  | nil => if Nat.eqb count O then nil else cons count nil
  | cons x xs =>
    if Nat.eqb prev x
    then run_length_groups_aux x (S count) xs
    else
      if Nat.eqb count O
      then run_length_groups_aux x 1 xs
      else cons count (run_length_groups_aux x 1 xs)
  end.

Definition run_length_groups (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => run_length_groups_aux x 1 xs
  end.

(** [is_prefix_of l1 l2] checks if l1 is a prefix of l2. *)
Fixpoint is_prefix_of (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, _ => true
  | _, nil => false
  | cons x xs, cons y ys =>
    if Nat.eqb x y then is_prefix_of xs ys else false
  end.

(** [lis l] longest increasing subsequence (greedy, not optimal). *)
Fixpoint lis (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ nil => l
  | cons x (cons y rest as ys) =>
    if Nat.ltb x y then cons x (lis ys) else lis ys
  end.

(** [take_while p l] takes elements while predicate holds. *)
Fixpoint take_while (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => if p x then cons x (take_while p xs) else nil
  end.

(** [drop_while p l] drops elements while predicate holds. *)
Fixpoint drop_while (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => if p x then drop_while p xs else cons x xs
  end.

(** Helper: check if element is in list. *)
Fixpoint elem (x : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons y ys => orb (Nat.eqb x y) (elem x ys)
  end.

(** Helper: filter list. *)
Fixpoint filter_ne (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons y ys => if Nat.eqb x y then filter_ne x ys else cons y (filter_ne x ys)
  end.

(** [nub l] removes duplicates from list. *)
Fixpoint nub_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x xs => cons x (nub_fuel f (filter_ne x xs))
    end
  end.

Definition nub (l : list nat) : list nat :=
  nub_fuel (length l) l.

(** [group l] groups consecutive equal elements. *)
Fixpoint group_fuel (fuel : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x nil => cons (cons x nil) nil
    | cons x (cons y rest as ys) =>
      if Nat.eqb x y then
        match group_fuel f ys with
        | nil => cons (cons x nil) nil
        | cons g gs => cons (cons x g) gs
        end
      else cons (cons x nil) (group_fuel f ys)
    end
  end.

Definition group (l : list nat) : list (list nat) :=
  group_fuel (length l) l.

(** Helper: get head with default. *)
Fixpoint head_or (default : nat) (l : list nat) : nat :=
  match l with
  | nil => default
  | cons h _ => h
  end.

(** [remove_if_sum_even l] removes elements where sum with next is even. *)
Fixpoint remove_if_sum_even (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    let next := head_or O xs in
    if Nat.eqb (Nat.modulo (Nat.add x next) 2) O
    then remove_if_sum_even xs
    else cons x (remove_if_sum_even xs)
  end.

(** [bool_all p l] checks if all elements satisfy predicate (forall with &&). *)
Fixpoint bool_all (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | nil => true
  | cons x xs => andb (p x) (bool_all p xs)
  end.

(** [run_length_encode l] encodes consecutive runs: [1,1,2,2,2] -> [(1,2),(2,3)]. *)
Fixpoint run_length_encode_fuel (fuel : nat) (l : list nat) : list (nat * nat) :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x nil => cons (x, 1) nil
    | cons x xs =>
      match run_length_encode_fuel f xs with
      | nil => cons (x, 1) nil
      | cons (y, n) rest =>
        if Nat.eqb x y
        then cons (y, S n) rest
        else cons (x, 1) (cons (y, n) rest)
      end
    end
  end.

Definition run_length_encode (l : list nat) : list (nat * nat) :=
  run_length_encode_fuel (length l) l.

(** [between lo hi l] filters elements in range [lo, hi]. *)
Fixpoint between (lo hi : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if andb (Nat.leb lo x) (Nat.leb x hi)
    then cons x (between lo hi xs)
    else between lo hi xs
  end.

End LoopifySequences.

Set Crane Loopify.
Crane Extraction "loopify_sequences" LoopifySequences.
