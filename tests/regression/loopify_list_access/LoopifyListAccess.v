From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListAccess.

(* List element access and lookup operations *)

(* Nth element (0-indexed) *)
Fixpoint nth (n : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if n =? 0 then x else nth (n - 1) xs
  end.

(* Last element *)
Fixpoint last (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | _ :: xs => last xs
  end.

(* Index of first occurrence *)
Fixpoint index_of_aux (x : nat) (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | y :: ys => if x =? y then idx else index_of_aux x ys (idx + 1)
  end.

Definition index_of (x : nat) (l : list nat) : nat :=
  index_of_aux x l 0.

(* Member check *)
Fixpoint member (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: ys => if x =? y then true else member x ys
  end.

(* Lookup in association list *)
Fixpoint lookup (key : nat) (l : list (nat * nat)) : nat :=
  match l with
  | [] => 0
  | (k, v) :: rest => if k =? key then v else lookup key rest
  end.

(* Lookup all values for a key *)
Fixpoint lookup_all (key : nat) (l : list (nat * nat)) : list nat :=
  match l with
  | [] => []
  | (k, v) :: xs =>
    if k =? key then v :: lookup_all key xs
    else lookup_all key xs
  end.

(* Find first element satisfying predicate *)
Fixpoint find (p : nat -> bool) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if p x then x else find p xs
  end.

(* Count occurrences of element *)
Fixpoint count (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: ys => if x =? y then 1 + count x ys else count x ys
  end.

(* Count elements matching predicate *)
Fixpoint count_matching (p : nat -> bool) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if p x then 1 + count_matching p xs else count_matching p xs
  end.

(* Check if element at index equals value *)
Fixpoint elem_at_eq (idx val : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs =>
    if idx =? 0 then x =? val
    else elem_at_eq (idx - 1) val xs
  end.

(* Get element at index, or default *)
Fixpoint nth_default (n : nat) (default : nat) (l : list nat) : nat :=
  match l with
  | [] => default
  | x :: xs => if n =? 0 then x else nth_default (n - 1) default xs
  end.

End LoopifyListAccess.

Set Crane Loopify.
Crane Extraction "loopify_list_access" LoopifyListAccess.
