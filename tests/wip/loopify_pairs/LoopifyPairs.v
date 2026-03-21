(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Consolidated UNIQUE pair/tuple operations. *)
Module LoopifyPairs.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(* ========== UNIQUE PAIR OPERATIONS ========== *)

(** [partition p l] splits into (satisfies p, doesn't satisfy p). *)
Fixpoint partition {A : Type} (p : A -> bool) (l : list A) : (list A * list A) :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    let '(yes, no) := partition p xs in
    if p x then (cons x yes, no) else (yes, cons x no)
  end.

(** [unzip l] splits list of nat pairs into pair of lists. *)
Fixpoint unzip (l : list (nat * nat)) : (list nat * list nat) :=
  match l with
  | nil => (nil, nil)
  | cons (x, y) rest =>
    let '(xs, ys) := unzip rest in
    (cons x xs, cons y ys)
  end.

(** [zip] combines two lists into pairs. *)
Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1, l2 with
  | cons x xs, cons y ys => cons (x, y) (zip xs ys)
  | _, _ => nil
  end.

(** [zip3] combines three lists. *)
Fixpoint zip3 {A B C : Type} (l1 : list A) (l2 : list B) (l3 : list C)
    : list (A * (B * C)) :=
  match l1, l2, l3 with
  | cons x xs, cons y ys, cons z zs =>
    cons (x, (y, z)) (zip3 xs ys zs)
  | _, _, _ => nil
  end.

(** [split_at n l] splits at position n. *)
Fixpoint split_at {A : Type} (n : nat) (l : list A) : (list A * list A) :=
  match n, l with
  | O, _ => (nil, l)
  | S _, nil => (nil, nil)
  | S m, cons x xs =>
    let '(taken, rest) := split_at m xs in
    (cons x taken, rest)
  end.

(** [swizzle] separates into even/odd positions. *)
Fixpoint swizzle {A : Type} (l : list A) : (list A * list A) :=
  match l with
  | nil => (nil, nil)
  | cons x nil => (cons x nil, nil)
  | cons x (cons y rest) =>
    let '(evens, odds) := swizzle rest in
    (cons x evens, cons y odds)
  end.

(** [span p l] splits at first element not satisfying p. *)
Fixpoint span {A : Type} (p : A -> bool) (l : list A) : (list A * list A) :=
  match l with
  | nil => (nil, nil)
  | cons x xs =>
    if p x
    then
      let '(ys, zs) := span p xs in
      (cons x ys, zs)
    else (nil, cons x xs)
  end.

(** [partition3 pivot l] three-way partition around pivot. *)
Fixpoint partition3 (pivot : nat) (l : list nat)
    : (list nat * (list nat * list nat)) :=
  match l with
  | nil => (nil, (nil, nil))
  | cons x xs =>
    let '(lt, (eq, gt)) := partition3 pivot xs in
    if Nat.ltb x pivot then (cons x lt, (eq, gt))
    else if Nat.eqb x pivot then (lt, (cons x eq, gt))
    else (lt, (eq, cons x gt))
  end.

(* ========== TUPLE AGGREGATIONS ========== *)

(** [min_max l] finds both min and max in one pass. *)
Fixpoint min_max (l : list nat) : (nat * nat) :=
  match l with
  | nil => (O, O)
  | cons x nil => (x, x)
  | cons x xs =>
    let '(mn, mx) := min_max xs in
    (if Nat.leb x mn then x else mn, if Nat.leb mx x then x else mx)
  end.

(** [sum_and_count] computes both in one pass. *)
Fixpoint sum_and_count (l : list nat) : (nat * nat) :=
  match l with
  | nil => (O, O)
  | cons x xs =>
    let '(s, c) := sum_and_count xs in
    (Nat.add x s, S c)
  end.

(** [sum_prod_count] triple accumulator. *)
Fixpoint sum_prod_count (l : list nat) : (nat * (nat * nat)) :=
  match l with
  | nil => (O, (1, O))
  | cons x xs =>
    let '(s, (p, c)) := sum_prod_count xs in
    (Nat.add x s, (Nat.mul x p, S c))
  end.

(** [mapAccumL f acc l] map with accumulator threading. *)
Fixpoint mapAccumL (f : nat -> nat -> (nat * nat)) (acc : nat)
                    (l : list nat) : (nat * list nat) :=
  match l with
  | nil => (acc, nil)
  | cons x xs =>
    let '(acc', y) := f acc x in
    let '(final_acc, ys) := mapAccumL f acc' xs in
    (final_acc, cons y ys)
  end.

(** [lookup_all key l] finds all values associated with key. *)
Fixpoint lookup_all (key : nat) (l : list (nat * nat)) : list nat :=
  match l with
  | nil => nil
  | cons (k, v) xs =>
    if Nat.eqb k key
    then cons v (lookup_all key xs)
    else lookup_all key xs
  end.

(** [swap_pairs l] swaps elements in each pair. *)
Fixpoint swap_pairs (l : list (nat * nat)) : list (nat * nat) :=
  match l with
  | nil => nil
  | cons (a, b) xs => cons (b, a) (swap_pairs xs)
  end.

End LoopifyPairs.

Set Crane Loopify.
Crane Extraction "loopify_pairs" LoopifyPairs.
