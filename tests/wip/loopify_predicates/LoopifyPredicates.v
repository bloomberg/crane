From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyPredicates.

(* List operations based on predicates *)

(* Take while predicate holds *)
Fixpoint take_while (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if p x then x :: take_while p xs else []
  end.

(* Drop while predicate holds *)
Fixpoint drop_while (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if p x then drop_while p xs else l
  end.

(* Span - split at first element not satisfying predicate *)
Fixpoint span (p : nat -> bool) (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    if p x then
      let '(yes, no) := span p xs in
      (x :: yes, no)
    else
      ([], l)
  end.

(* Break - opposite of span *)
Fixpoint break_at (p : nat -> bool) (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    if p x then
      ([], l)
    else
      let '(before, after) := break_at p xs in
      (x :: before, after)
  end.

(* Filter - keep elements satisfying predicate *)
Fixpoint filter (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if p x then x :: filter p xs else filter p xs
  end.

(* Reject - opposite of filter *)
Fixpoint reject (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if p x then reject p xs else x :: reject p xs
  end.

(* All elements satisfy predicate *)
Fixpoint forall_pred (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => p x && forall_pred p xs
  end.

(* Any element satisfies predicate *)
Fixpoint exists_pred (p : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => p x || exists_pred p xs
  end.

(* Find index of first element satisfying predicate *)
Fixpoint find_index_aux (p : nat -> bool) (l : list nat) (idx : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some idx else find_index_aux p xs (idx + 1)
  end.

Definition find_index (p : nat -> bool) (l : list nat) : option nat :=
  find_index_aux p l 0.

(* Find all indices of elements satisfying predicate *)
Fixpoint find_indices_aux (p : nat -> bool) (l : list nat) (idx : nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    if p x then idx :: find_indices_aux p xs (idx + 1)
    else find_indices_aux p xs (idx + 1)
  end.

Definition find_indices (p : nat -> bool) (l : list nat) : list nat :=
  find_indices_aux p l 0.

(* Delete first element satisfying predicate *)
Fixpoint delete_by (eq : nat -> nat -> bool) (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | y :: ys => if eq x y then ys else y :: delete_by eq x ys
  end.

(* Remove all elements equal to x *)
Fixpoint remove_all (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | y :: ys => if x =? y then remove_all x ys else y :: remove_all x ys
  end.

End LoopifyPredicates.

Set Crane Loopify.
Crane Extraction "loopify_predicates" LoopifyPredicates.
