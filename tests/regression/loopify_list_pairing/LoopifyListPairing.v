From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListPairing.

(* List pairing, zipping, and partitioning operations *)

(* Unzip - split list of pairs *)
Fixpoint unzip (l : list (nat * nat)) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | (a, b) :: rest =>
    let '(xs, ys) := unzip rest in
    (a :: xs, b :: ys)
  end.

(* Swizzle - split into odd/even positions *)
Fixpoint swizzle (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    let '(odds, evens) := swizzle xs in
    (x :: evens, odds)
  end.

(* Partition - split by predicate *)
Fixpoint partition (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    let '(yes, no) := partition xs in
    if (x mod 2) =? 0 then (x :: yes, no)
    else (yes, x :: no)
  end.

(* Zip longest - zip with default values *)
Fixpoint zip_longest_fuel (fuel : nat) (l1 l2 : list nat) (default : nat) : list (nat * nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l1, l2 with
    | [], [] => []
    | x :: xs, [] => (x, default) :: zip_longest_fuel fuel' xs [] default
    | [], y :: ys => (default, y) :: zip_longest_fuel fuel' [] ys default
    | x :: xs, y :: ys => (x, y) :: zip_longest_fuel fuel' xs ys default
    end
  end.

Definition zip_longest (l1 l2 : list nat) (default : nat) : list (nat * nat) :=
  let len1 := length l1 in
  let len2 := length l2 in
  let maxlen := if len1 <? len2 then len2 else len1 in
  zip_longest_fuel maxlen l1 l2 default.

(* ZipWith - zip with function *)
Fixpoint zipWith (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x + y) :: zipWith xs ys
  end.

(* Split even/odd *)
Fixpoint split_even_odd (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    let '(evens, odds) := split_even_odd xs in
    if (x mod 2) =? 0 then (x :: evens, odds)
    else (evens, x :: odds)
  end.

End LoopifyListPairing.

Set Crane Loopify.
Crane Extraction "loopify_list_pairing" LoopifyListPairing.
