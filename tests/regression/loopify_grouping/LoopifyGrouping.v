From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyGrouping.

(* Grouping and deduplication operations *)

(* Helper: prepend element to first group if they match, else start new group *)
Definition prepend_to_groups (x : nat) (same : bool) (groups : list (list nat)) : list (list nat) :=
  if same then
    match groups with
    | [] => [[x]]
    | g :: gs => (x :: g) :: gs
    end
  else [x] :: groups.

(* Group consecutive equal elements *)
Fixpoint group_fuel (fuel : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | [x] => [[x]]
    | x :: y :: rest =>
      let rec_result := group_fuel fuel' (y :: rest) in
      prepend_to_groups x (x =? y) rec_result
    end
  end.

Definition group (l : list nat) : list (list nat) :=
  group_fuel (length l) l.

(* Check if element is in list *)
Fixpoint elem (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: ys => if x =? y then true else elem x ys
  end.

(* Remove duplicates (keep first occurrence) *)
Fixpoint nub (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    let rest := nub xs in
    if elem x rest then rest else x :: rest
  end.

(* Remove all occurrences of element *)
Fixpoint remove_elem (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | y :: ys => if x =? y then remove_elem x ys else y :: remove_elem x ys
  end.

(* Partition into three lists based on comparison *)
Fixpoint partition3 (pivot : nat) (l : list nat) : list nat * list nat * list nat :=
  match l with
  | [] => ([], [], [])
  | x :: xs =>
    let '(less, equal, greater) := partition3 pivot xs in
    if x <? pivot then (x :: less, equal, greater)
    else if pivot <? x then (less, equal, x :: greater)
    else (less, x :: equal, greater)
  end.

(* Count occurrences of element *)
Fixpoint count_elem (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: ys => if x =? y then 1 + count_elem x ys else count_elem x ys
  end.

(* Group pairs - consecutive pairs *)
Fixpoint group_pairs (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | [_] => []
  | x :: xs =>
    match xs with
    | [] => []
    | y :: rest => (x, y) :: group_pairs rest
    end
  end.

End LoopifyGrouping.

Set Crane Loopify.
Crane Extraction "loopify_grouping" LoopifyGrouping.
