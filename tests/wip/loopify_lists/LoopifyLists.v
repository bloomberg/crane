(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Consolidated UNIQUE list operations - no stdlib duplicates.
    Tests loopification on domain-specific list algorithms. *)
Module LoopifyLists.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(* ========== UNIQUE LIST ALGORITHMS (not in stdlib) ========== *)

(** [stutter l] duplicates each element: [1,2] -> [1,1,2,2]. *)
Fixpoint stutter {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => cons x (cons x (stutter xs))
  end.

(** [snoc l x] appends x at the end (reverse cons). *)
Fixpoint snoc {A : Type} (l : list A) (x : A) : list A :=
  match l with
  | nil => cons x nil
  | cons h t => cons h (snoc t x)
  end.

(** [intersperse sep l] inserts separator between elements. *)
Fixpoint intersperse {A : Type} (sep : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x xs => cons x (cons sep (intersperse sep xs))
  end.

(** [replicate n x] creates n copies of x. *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => nil
  | S m => cons x (replicate m x)
  end.

(** [replicate_list n l] repeats list l n times. *)
Fixpoint replicate_list {A : Type} (n : nat) (l : list A) : list A :=
  let fix app l1 l2 :=
    match l1 with
    | nil => l2
    | cons x xs => cons x (app xs l2)
    end
  in
  match n with
  | O => nil
  | S m => app l (replicate_list m l)
  end.

(** [init_list n f] generates [f 0, f 1, ..., f (n-1)]. *)
Fixpoint init_list {A : Type} (n : nat) (f : nat -> A) : list A :=
  let fix go i :=
    match i with
    | O => nil
    | S j => cons (f (Nat.sub n i)) (go j)
    end
  in go n.

(** [range start count] generates [start, start+1, ..., start+count-1]. *)
Fixpoint range (start count : nat) : list nat :=
  match count with
  | O => nil
  | S c => cons start (range (S start) c)
  end.

(** [tails l] returns all suffixes. *)
Fixpoint tails {A : Type} (l : list A) : list (list A) :=
  match l with
  | nil => cons nil nil
  | cons _ xs => cons l (tails xs)
  end.

(** [inits l] returns all prefixes (complex recursion pattern). *)
Fixpoint inits {A : Type} (l : list A) : list (list A) :=
  match l with
  | nil => cons nil nil
  | cons x xs =>
    cons nil
      (let fix map_cons ys :=
        match ys with
        | nil => nil
        | cons z zs => cons (cons x z) (map_cons zs)
        end
       in map_cons (inits xs))
  end.

(** [scanl f acc l] returns intermediate fold results. *)
Fixpoint scanl {A B : Type} (f : B -> A -> B) (acc : B) (l : list A) : list B :=
  match l with
  | nil => cons acc nil
  | cons x xs =>
    let new_acc := f acc x in
    cons acc (scanl f new_acc xs)
  end.

(** [group_by eq l] groups consecutive equal elements. *)
Fixpoint group_by_aux {A : Type} (eq : A -> A -> bool) (prev : A) (acc : list A) (l : list A) : list (list A) :=
  match l with
  | nil => cons acc nil
  | cons x xs =>
    if eq prev x
    then group_by_aux eq x (cons x acc) xs
    else cons acc (group_by_aux eq x (cons x nil) xs)
  end.

Definition group_by {A : Type} (eq : A -> A -> bool) (l : list A) : list (list A) :=
  match l with
  | nil => nil
  | cons x xs => group_by_aux eq x (cons x nil) xs
  end.

(** [chunks_of n l] splits into chunks of size n. *)
Fixpoint chunks_of_aux {A : Type} (n : nat) (l : list A) (fuel : nat) : list (list A) :=
  match fuel with
  | O => nil
  | S f =>
    let fix take k lst :=
      match k, lst with
      | O, _ => nil
      | S m, cons x xs => cons x (take m xs)
      | _, nil => nil
      end
    in
    let fix drop k lst :=
      match k, lst with
      | O, l => l
      | S m, cons _ xs => drop m xs
      | _, nil => nil
      end
    in
    match l with
    | nil => nil
    | _ =>
      let chunk := take n l in
      let rest := drop n l in
      match chunk with
      | nil => nil
      | _ => cons chunk (chunks_of_aux n rest f)
      end
    end
  end.

Definition chunks_of {A : Type} (n : nat) (l : list A) : list (list A) :=
  let fix length l :=
    match l with
    | nil => O
    | cons _ xs => S (length xs)
    end
  in
  chunks_of_aux n l (S (length l)).

(* ========== CONDITIONAL OPERATIONS ========== *)

(** [step_sum l] sums with conditional contributions: even values as-is, odd doubled. *)
Fixpoint step_sum (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let contribution :=
      if Nat.eqb (Nat.modulo x 2) O
      then x
      else Nat.mul x 2
    in Nat.add contribution (step_sum xs)
  end.

(** [sum_abs l] sums absolute values (using monus for nat). *)
Fixpoint sum_abs (l : list nat) (base : nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let abs_val := if Nat.leb base x then Nat.sub x base else Nat.sub base x in
    Nat.add abs_val (sum_abs xs base)
  end.

(** [four_elem l] multi-case pattern matching on list structure. *)
Fixpoint four_elem (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ nil => 1
  | cons _ (cons _ nil) => 2
  | cons _ (cons _ (cons _ nil)) => 3
  | cons a (cons b (cons c (cons d rest))) =>
    Nat.add (Nat.add a b) (Nat.add (Nat.add c d) (four_elem rest))
  end.

(* ========== FILTERING & COUNTING ========== *)

(** [between lo hi l] filters elements in range [lo, hi]. *)
Fixpoint between (lo hi : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if andb (Nat.leb lo x) (Nat.leb x hi)
    then cons x (between lo hi xs)
    else between lo hi xs
  end.

(** [count_matching p l] counts elements satisfying predicate. *)
Fixpoint count_matching (p : nat -> bool) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    if p x
    then S (count_matching p xs)
    else count_matching p xs
  end.

(** [categorize k l] categorizes elements: 1 for <k, 2 for =k, 3 for >k. *)
Fixpoint categorize (k : nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let score :=
      if Nat.ltb k x then 3
      else if Nat.eqb x k then 2
      else 1
    in Nat.add score (categorize k xs)
  end.

(* ========== AGGREGATIONS ========== *)

(** [max_prefix_sum l] maximum prefix sum (Kadane-like). *)
Fixpoint max_prefix_sum (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let rest := max_prefix_sum xs in
    let sum := Nat.add x rest in
    if Nat.leb O sum then sum else O
  end.

(** [pairwise_sum l] sums consecutive pairs: [1,2,3,4] -> [3,7]. *)
Fixpoint pairwise_sum (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x (cons y rest) =>
    cons (Nat.add x y) (pairwise_sum rest)
  end.

(** [weighted_sum i l] weighted sum with increasing weights. *)
Fixpoint weighted_sum (i : nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    Nat.add (Nat.mul i x) (weighted_sum (S i) xs)
  end.

(* ========== ZIPPING & PAIRING ========== *)

(** [zip_with f l1 l2] zips two lists with a function. *)
Fixpoint zip_with {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | nil, _ => nil
  | _, nil => nil
  | cons x xs, cons y ys => cons (f x y) (zip_with f xs ys)
  end.

(** [zip_longest l1 l2 def] zips with default for mismatched lengths. *)
Fixpoint zip_longest_aux {A : Type} (fuel : nat) (l1 l2 : list A) (default : A) : list (A * A) :=
  match fuel with
  | O => nil
  | S f =>
    match l1, l2 with
    | nil, nil => nil
    | cons x xs, nil => cons (x, default) (zip_longest_aux f xs nil default)
    | nil, cons y ys => cons (default, y) (zip_longest_aux f nil ys default)
    | cons x xs, cons y ys => cons (x, y) (zip_longest_aux f xs ys default)
    end
  end.

Definition zip_longest {A : Type} (l1 l2 : list A) (default : A) : list (A * A) :=
  let fix length l :=
    match l with
    | nil => O
    | cons _ xs => S (length xs)
    end
  in
  let len := Nat.add (length l1) (length l2) in
  zip_longest_aux (S len) l1 l2 default.

(** [sliding_pairs l] returns consecutive pairs: [1,2,3] -> [(1,2),(2,3)]. *)
Fixpoint sliding_pairs {A : Type} (l : list A) : list (A * A) :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons a (cons b rest as xs) =>
    cons (a, b) (sliding_pairs xs)
  end.

(* ========== PARTITIONING ========== *)

(** [partition3 p q l] partitions into 3 groups based on 2 predicates. *)
Fixpoint partition3 (p q : nat -> bool) (l : list nat) : (list nat * list nat * list nat) :=
  match l with
  | nil => (nil, nil, nil)
  | cons x xs =>
    let '(as_, bs, cs) := partition3 p q xs in
    if p x then (cons x as_, bs, cs)
    else if q x then (as_, cons x bs, cs)
    else (as_, bs, cons x cs)
  end.

(* ========== ADVANCED OPERATIONS ========== *)

(** [transpose m] transposes a matrix (list of lists). *)
Fixpoint transpose_fuel {A : Type} (fuel : nat) (m : list (list A)) : list (list A) :=
  match fuel with
  | O => nil
  | S f =>
    let fix map_head l :=
      match l with
      | nil => nil
      | cons nil _ => nil
      | cons (cons h _) rest => cons h (map_head rest)
      end
    in
    let fix map_tail l :=
      match l with
      | nil => nil
      | cons nil _ => nil
      | cons (cons _ t) rest => cons t (map_tail rest)
      end
    in
    match m with
    | nil => nil
    | cons nil _ => nil
    | _ =>
      let heads := map_head m in
      let tails := map_tail m in
      match heads with
      | nil => nil
      | _ => cons heads (transpose_fuel f tails)
      end
    end
  end.

Definition transpose {A : Type} (m : list (list A)) : list (list A) :=
  transpose_fuel 100 m.

(** [map_accum_l f acc l] maps with accumulator from left. *)
Fixpoint map_accum_l {A B C : Type} (f : C -> A -> C * B) (acc : C) (l : list A) : C * list B :=
  match l with
  | nil => (acc, nil)
  | cons x xs =>
    let '(acc', y) := f acc x in
    let '(acc'', ys) := map_accum_l f acc' xs in
    (acc'', cons y ys)
  end.

(** [prefix_sums acc l] returns all prefix sums: [1,2,3] -> [0,1,3,6]. *)
Fixpoint prefix_sums (acc : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons acc nil
  | cons x xs =>
    cons acc (prefix_sums (Nat.add acc x) xs)
  end.

(** [uniq_sorted l] removes consecutive duplicates from sorted list. *)
Fixpoint uniq_sorted (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x (cons y rest as xs) =>
    if Nat.eqb x y then uniq_sorted xs
    else cons x (uniq_sorted xs)
  end.

(** Helper: take first n elements. *)
Fixpoint take_n (n : nat) (l : list nat) : list nat :=
  match n, l with
  | O, _ => nil
  | S m, cons x xs => cons x (take_n m xs)
  | _, nil => nil
  end.

(** Helper: list length. *)
Fixpoint len_list (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_list xs)
  end.

(** [windows n l] returns all sliding windows of size n. *)
Fixpoint windows_aux (fuel : nat) (n : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons _ rest =>
      if Nat.ltb (len_list l) n then nil
      else
        let window := take_n n l in
        match window with
        | nil => nil
        | _ => cons window (windows_aux f n rest)
        end
    end
  end.

Definition windows (n : nat) (l : list nat) : list (list nat) :=
  windows_aux (S (len_list l)) n l.

(** [is_prefix_of l1 l2] checks if l1 is a prefix of l2. *)
Fixpoint is_prefix_of (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, _ => true
  | cons _ _, nil => false
  | cons x xs, cons y ys =>
    if Nat.eqb x y then is_prefix_of xs ys else false
  end.

(** [lookup_all key l] finds all values for key in association list. *)
Fixpoint lookup_all (key : nat) (l : list (nat * nat)) : list nat :=
  match l with
  | nil => nil
  | cons (k, v) rest =>
    if Nat.eqb k key
    then cons v (lookup_all key rest)
    else lookup_all key rest
  end.

(** [delete_by eq x l] deletes first element equal to x by custom equality. *)
Fixpoint delete_by (eq : nat -> nat -> bool) (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons y ys =>
    if eq x y then ys else cons y (delete_by eq x ys)
  end.

(** [find_indices p l] returns list of indices where predicate holds. *)
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

(** [member x l] checks if x is in the list. *)
Fixpoint member (x : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons y ys => if Nat.eqb x y then true else member x ys
  end.

(** [product l] multiplies all elements in the list. *)
Fixpoint product (l : list nat) : nat :=
  match l with
  | nil => 1
  | cons x xs => Nat.mul x (product xs)
  end.

(** [sum_list l] sums all elements in the list. *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs => Nat.add x (sum_list xs)
  end.

(** [flatten l] flattens a list of lists. *)
Fixpoint flatten {A : Type} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons xs xss =>
    let fix app l1 l2 :=
      match l1 with
      | nil => l2
      | cons y ys => cons y (app ys l2)
      end
    in app xs (flatten xss)
  end.

(** [flatten_nested l] alternative flatten with different pattern: flattens one level at a time.
    Pattern: [] :: rest -> flatten rest, (x :: xs) :: rest -> x :: flatten (xs :: rest). *)
Fixpoint flatten_nested_fuel (fuel : nat) (l : list (list nat)) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons nil rest => flatten_nested_fuel f rest
    | cons (cons x xs) rest => cons x (flatten_nested_fuel f (cons xs rest))
    end
  end.

Fixpoint sum_list_lengths (l : list (list nat)) : nat :=
  match l with
  | nil => O
  | cons xs xss => Nat.add (len_list xs) (sum_list_lengths xss)
  end.

Definition flatten_nested (l : list (list nat)) : list nat :=
  flatten_nested_fuel (S (sum_list_lengths l)) l.

(* ========== ADDITIONAL OPERATIONS ========== *)

(** [compress l] removes consecutive duplicates: [1,1,2,2,2,3] -> [1,2,3]. *)
Fixpoint compress (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x nil => cons x nil
  | cons x (cons y rest as xs) =>
    if Nat.eqb x y
    then compress xs
    else cons x (compress xs)
  end.

(** [group_pairs l] groups consecutive elements into pairs: [1,2,3,4] -> [(1,2),(3,4)]. *)
Fixpoint group_pairs (l : list nat) : list (nat * nat) :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x (cons y rest) =>
    cons (x, y) (group_pairs rest)
  end.

(** [swizzle l] separates elements by position: [1,2,3,4] -> ([1,3],[2,4]). *)
Fixpoint swizzle (l : list nat) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    let '(odds, evens) := swizzle xs in
    (cons x evens, odds)
  end.

(** [index_of_aux x l i] finds first index of x in l starting from i. *)
Fixpoint index_of_aux (x : nat) (l : list nat) (i : nat) : nat :=
  match l with
  | nil => O
  | cons y ys =>
    if Nat.eqb x y
    then i
    else index_of_aux x ys (S i)
  end.

Definition index_of (x : nat) (l : list nat) : nat :=
  index_of_aux x l O.

(** [interleave l1 l2] interleaves two lists: [1,2] [3,4] -> [1,3,2,4]. *)
Fixpoint interleave (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | cons x xs, cons y ys =>
    cons x (cons y (interleave xs ys))
  end.

(** [lookup key l] finds value for key in association list. *)
Fixpoint lookup (key : nat) (l : list (nat * nat)) : nat :=
  match l with
  | nil => O
  | cons (k, v) rest =>
    if Nat.eqb k key then v else lookup key rest
  end.

(** [group l] groups consecutive equal elements: [1,1,2,2,2,3] -> [[1,1],[2,2,2],[3]]. *)
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
  group_fuel (S (len_list l)) l.

(** Internal helper: reverse a list. *)
Fixpoint rev_helper (acc : list nat) (l : list nat) : list nat :=
  match l with
  | nil => acc
  | cons x xs => rev_helper (cons x acc) xs
  end.

(** [reverse_insert x l] inserts x and reverses at each step. *)
Fixpoint reverse_insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons x nil
  | cons h t =>
    rev_helper nil (cons h (reverse_insert x t))
  end.

(** Internal helper: append lists. *)
Fixpoint app_helper (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app_helper xs l2)
  end.

(** [double_append l1 l2] appends with doubling: [1,2] [3] -> [1,3,3,3,3]. *)
Fixpoint double_append (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | cons h t =>
    let rest := double_append t l2 in
    cons h (app_helper rest rest)
  end.

(** [remove_if_sum_even l] removes element if sum with next is even. *)
Fixpoint remove_if_sum_even (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    match xs with
    | nil => cons x nil
    | cons h _ =>
      if Nat.eqb (Nat.modulo (Nat.add x h) 2) O
      then remove_if_sum_even xs
      else cons x (remove_if_sum_even xs)
    end
  end.

(** [split_at n l] splits list at index n into (prefix, suffix). *)
Fixpoint split_at (n : nat) (l : list nat) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    if Nat.eqb n O
    then (nil, l)
    else
      let '(a, b) := split_at (Nat.sub n 1) xs in
      (cons x a, b)
  end.

(** [span p l] splits list at first element not satisfying p. *)
Fixpoint span (p : nat -> bool) (l : list nat) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    if p x
    then
      let '(a, b) := span p xs in
      (cons x a, b)
    else (nil, l)
  end.

(** [unzip l] splits list of pairs into two lists. *)
Fixpoint unzip (l : list (nat * nat)) : list nat * list nat :=
  match l with
  | nil => (nil, nil)
  | cons (a, b) rest =>
    let '(xs, ys) := unzip rest in
    (cons a xs, cons b ys)
  end.

(** [nth n l default] returns nth element or default if out of bounds. *)
Fixpoint nth (n : nat) (l : list nat) (default : nat) : nat :=
  match l with
  | nil => default
  | cons x xs =>
    if Nat.eqb n O
    then x
    else nth (Nat.sub n 1) xs default
  end.

(** [last l default] returns last element or default if empty. *)
Fixpoint last (l : list nat) (default : nat) : nat :=
  match l with
  | nil => default
  | cons x nil => x
  | cons _ xs => last xs default
  end.

(** [drop n l] drops first n elements. *)
Fixpoint drop (n : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ xs =>
    if Nat.eqb n O
    then l
    else drop (Nat.sub n 1) xs
  end.

(** [init l] returns all but last element. *)
Fixpoint init (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons _ nil => nil
  | cons x xs => cons x (init xs)
  end.

(** [count x l] counts occurrences of x in l. *)
Fixpoint count (x : nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons y ys =>
    if Nat.eqb x y
    then S (count x ys)
    else count x ys
  end.

(** [maximum l] finds maximum element (returns 0 for empty list). *)
Fixpoint maximum (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => x
  | cons x xs =>
    let max_rest := maximum xs in
    if Nat.leb max_rest x then x else max_rest
  end.

(** [minmax l] finds both minimum and maximum in one pass. *)
Fixpoint minmax (l : list nat) : nat * nat :=
  match l with
  | nil => (O, O)
  | cons x nil => (x, x)
  | cons x xs =>
    let '(lo, hi) := minmax xs in
    ((if Nat.leb x lo then x else lo), (if Nat.leb hi x then x else hi))
  end.

(** Helper for rotate_left. *)
Fixpoint rotate_left_fuel (fuel : nat) (n : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    if Nat.eqb n O then l
    else match l with
    | nil => nil
    | cons x xs => rotate_left_fuel f (Nat.sub n 1) (app_helper xs (cons x nil))
    end
  end.

(** [rotate_left n l] rotates list left by n positions: rotate 2 [1,2,3,4] -> [3,4,1,2]. *)
Definition rotate_left (n : nat) (l : list nat) : list nat :=
  rotate_left_fuel (S n) n l.

(** [intercalate sep lists] joins lists with separator: intercalate [0] [[1,2],[3,4]] -> [1,2,0,3,4]. *)
Fixpoint intercalate (sep : list nat) (lists : list (list nat)) : list nat :=
  match lists with
  | nil => nil
  | cons x nil => x
  | cons x xs => app_helper x (app_helper sep (intercalate sep xs))
  end.

(** [majority l] finds majority element using Boyer-Moore voting algorithm.
    Returns (candidate, count). *)
Fixpoint majority (l : list nat) : nat * nat :=
  match l with
  | nil => (O, O)
  | cons x nil => (x, 1)
  | cons x xs =>
    let '(cand, cnt) := majority xs in
    if Nat.eqb x cand then (cand, S cnt)
    else if Nat.eqb cnt O then (x, 1)
    else (cand, Nat.sub cnt 1)
  end.

(** [zip3 l1 l2 l3] zips three lists into triples. *)
Fixpoint zip3 (l1 l2 l3 : list nat) : list (nat * nat * nat) :=
  match l1, l2, l3 with
  | cons x xs, cons y ys, cons z zs => cons (x, y, z) (zip3 xs ys zs)
  | _, _, _ => nil
  end.

(** [sum_and_count l] returns both sum and count in one pass. *)
Fixpoint sum_and_count (l : list nat) : nat * nat :=
  match l with
  | nil => (O, O)
  | cons x xs =>
    let '(s, c) := sum_and_count xs in
    (Nat.add x s, S c)
  end.

(** [elem_at n l] returns element at index n (like nth but with different name). *)
Fixpoint elem_at (n : nat) (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons x xs =>
    if Nat.eqb n O then Some x else elem_at (Nat.sub n 1) xs
  end.

End LoopifyLists.

Set Crane Loopify.
Crane Extraction "loopify_lists" LoopifyLists.
