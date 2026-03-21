From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyAdvancedLists.

(* Product of all elements in a list *)
Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | x :: xs => x * product xs
  end.

(* Remove consecutive duplicates *)
Fixpoint compress (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    match xs with
    | [] => [x]
    | y :: rest =>
      if Nat.eqb x y then compress xs
      else x :: compress xs
    end
  end.

(* Sum adjacent pairs [1;2;3;4] -> [3;7] *)
Fixpoint pairwise_sum (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    match xs with
    | [] => []
    | y :: rest => (x + y) :: pairwise_sum rest
    end
  end.

(* Group list into pairs [1;2;3;4] -> [(1,2);(3,4)] *)
Fixpoint group_pairs (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | x :: xs =>
    match xs with
    | [] => []
    | y :: rest => (x, y) :: group_pairs rest
    end
  end.

(* Interleave two lists [1;2;3] [10;20;30] -> [1;10;2;20;3;30] *)
Fixpoint interleave (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  end.

(* Concatenate nested list of lists *)
Fixpoint concat_lists (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | l :: rest => l ++ concat_lists rest
  end.

(* Map a function that returns a list and flatten results *)
Fixpoint flat_map (f : nat -> list nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => f x ++ flat_map f xs
  end.

(* All elements satisfy predicate *)
Fixpoint all_satisfy (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => p x && all_satisfy p xs
  end.

(* Any element satisfies predicate *)
Fixpoint any_satisfy (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => p x || any_satisfy p xs
  end.

(* Find first element satisfying predicate *)
Fixpoint find_first (p : nat -> bool) (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some x else find_first p xs
  end.

End LoopifyAdvancedLists.

Set Crane Loopify.
Crane Extraction "loopify_advanced_lists" LoopifyAdvancedLists.
