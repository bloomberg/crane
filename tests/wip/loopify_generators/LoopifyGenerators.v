(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

(** Consolidated list generator functions. *)
Module LoopifyGenerators.

(* ========== GENERATORS ========== *)

(** [cycle n l] repeats the list n times: cycle 2 [1,2] -> [1,2,1,2]. *)
Fixpoint cycle (n : nat) (l : list nat) : list nat :=
  match n with
  | O => nil
  | S m => app l (cycle m l)
  end.

(** [iterate f n x] applies f repeatedly n times: iterate (+1) 3 5 -> [5,6,7]. *)
Fixpoint iterate (f : nat -> nat) (n : nat) (x : nat) : list nat :=
  match n with
  | O => nil
  | S m => cons x (iterate f m (f x))
  end.

(** [zip_with f l1 l2] zips with a combining function. *)
Fixpoint zip_with (f : nat -> nat -> nat) (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | nil, _ => nil
  | _, nil => nil
  | cons x xs, cons y ys => cons (f x y) (zip_with f xs ys)
  end.

(** [zip_longest l1 l2 default] zips, using default for missing elements. *)
Fixpoint zip_longest_aux (l1 l2 : list nat) (default : nat) (fuel : nat) : list (nat * nat) :=
  match fuel with
  | O => nil
  | S f =>
    match l1, l2 with
    | nil, nil => nil
    | cons x xs, nil => cons (x, default) (zip_longest_aux xs nil default f)
    | nil, cons y ys => cons (default, y) (zip_longest_aux nil ys default f)
    | cons x xs, cons y ys => cons (x, y) (zip_longest_aux xs ys default f)
    end
  end.

Fixpoint len_impl (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_impl xs)
  end.

Definition zip_longest (l1 l2 : list nat) (default : nat) : list (nat * nat) :=
  zip_longest_aux l1 l2 default (Nat.add (len_impl l1) (len_impl l2)).

(** [build_list n] builds tree-like list structure: build_list(4) -> [2,4,2]. *)
Fixpoint build_list_fuel (fuel : nat) (n : nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match n with
    | O => nil
    | S O => cons 1 nil
    | S (S m as n') =>
      let half := Nat.div n' 2 in
      let half_result := build_list_fuel f half in
      app half_result (cons n' half_result)
    end
  end.

Definition build_list (n : nat) : list nat :=
  build_list_fuel 100 n.

(** [take n l] returns first n elements. *)
Fixpoint take (n : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if Nat.eqb n O
    then nil
    else cons x (take (Nat.sub n 1) xs)
  end.

(** [repeat x n] creates list with n copies of x. *)
Fixpoint repeat (x : nat) (n : nat) : list nat :=
  match n with
  | O => nil
  | S m => cons x (repeat x m)
  end.

(** [unfold f n init] unfolds a list from seed value. *)
Fixpoint unfold_fuel (fuel : nat) (f : nat -> nat * nat) (n : nat) (seed : nat) : list nat :=
  match fuel with
  | O => nil
  | S g =>
    if Nat.eqb n O
    then nil
    else
      let '(val, next_seed) := f seed in
      cons val (unfold_fuel g f (Nat.sub n 1) next_seed)
  end.

Definition unfold (f : nat -> nat * nat) (n : nat) (seed : nat) : list nat :=
  unfold_fuel 100 f n seed.

(* ========== ADDITIONAL GENERATORS ========== *)

(** [tabulate n f] generates [f 0, f 1, ..., f (n-1)] (same as init_list but different naming). *)
Fixpoint tabulate (n : nat) (f : nat -> nat) : list nat :=
  let fix go i :=
    match i with
    | O => nil
    | S j => cons (f (Nat.sub n i)) (go j)
    end
  in go n.

(** Helper: replicate single element n times. *)
Fixpoint replicate_single (x : nat) (n : nat) : list nat :=
  match n with
  | O => nil
  | S m => cons x (replicate_single x m)
  end.

(** [replicate_each n l] replicates each element n times: replicate_each 2 [1,2] -> [1,1,2,2]. *)
Fixpoint replicate_each (n : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => app (replicate_single x n) (replicate_each n xs)
  end.

End LoopifyGenerators.

Set Crane Loopify.
Crane Extraction "loopify_generators" LoopifyGenerators.
