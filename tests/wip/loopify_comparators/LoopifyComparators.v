From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyComparators.

(* Comparison-based operations *)

(* Maximum by comparison *)
Fixpoint maximum_by (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let m := maximum_by xs in
    if m <? x then x else m
  end.

(* Minimum by comparison *)
Fixpoint minimum_by (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let m := minimum_by xs in
    if x <? m then x else m
  end.

(* Merge with fuel for non-structural recursion *)
Fixpoint merge_by_fuel (fuel : nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: xs, y :: ys =>
      if x <=? y then x :: merge_by_fuel fuel' xs l2
      else y :: merge_by_fuel fuel' l1 ys
    end
  end.

Definition merge_by (l1 l2 : list nat) : list nat :=
  let len1 := length l1 in
  let len2 := length l2 in
  merge_by_fuel (len1 + len2) l1 l2.

(* Insert into sorted list *)
Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert_sorted x t
  end.

(* Insertion sort *)
Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => insert_sorted x (insertion_sort xs)
  end.

(* Is sorted *)
Fixpoint is_sorted_fuel (fuel : nat) (l : list nat) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
    match l with
    | [] => true
    | [_] => true
    | x :: y :: rest => if x <=? y then is_sorted_fuel fuel' (y :: rest) else false
    end
  end.

Definition is_sorted (l : list nat) : bool :=
  let len := length l in
  is_sorted_fuel len l.

End LoopifyComparators.

Set Crane Loopify.
Crane Extraction "loopify_comparators" LoopifyComparators.
