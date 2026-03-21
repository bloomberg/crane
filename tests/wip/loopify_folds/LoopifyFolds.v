From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyFolds.

(* Fold and scan operations - fundamental list combinators *)

(* Fold left - tail recursive accumulation *)
Fixpoint fold_left (f : nat -> nat -> nat) (acc : nat) (l : list nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => fold_left f (f acc x) xs
  end.

(* Fold right - non-tail recursive *)
Fixpoint fold_right (f : nat -> nat -> nat) (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => f x (fold_right f xs acc)
  end.

(* Scan left - fold with intermediate results *)
Fixpoint scanl (f : nat -> nat -> nat) (acc : nat) (l : list nat) : list nat :=
  match l with
  | [] => [acc]
  | x :: xs => acc :: scanl f (f acc x) xs
  end.

(* Scan right - fold right with intermediate results *)
Fixpoint scanr (f : nat -> nat -> nat) (acc : nat) (l : list nat) : list nat :=
  match l with
  | [] => [acc]
  | x :: xs =>
    match scanr f acc xs with
    | [] => [acc]  (* Should not happen *)
    | y :: _ as rest => f x y :: rest
    end
  end.

(* Fold left starting from first element *)
Fixpoint foldl1_fuel (fuel : nat) (f : nat -> nat -> nat) (l : list nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match l with
    | [] => 0
    | [x] => x
    | x :: y :: rest => foldl1_fuel fuel' f (f x y :: rest)
    end
  end.

Definition foldl1 (f : nat -> nat -> nat) (l : list nat) : nat :=
  foldl1_fuel (length l) f l.

(* Fold right starting from last element *)
Fixpoint foldr1 (f : nat -> nat -> nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => f x (foldr1 f xs)
  end.

(* Map and accumulate *)
Fixpoint map_accum (f : nat -> nat -> nat * nat) (acc : nat) (l : list nat) : nat * list nat :=
  match l with
  | [] => (acc, [])
  | x :: xs =>
    let '(acc', y) := f acc x in
    let '(final_acc, ys) := map_accum f acc' xs in
    (final_acc, y :: ys)
  end.

(* Iterate with accumulator *)
Fixpoint iterate_accum (f : nat -> nat) (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: iterate_accum f n' (f x)
  end.

(* Unfold - generate list from seed *)
Fixpoint unfold_fuel (fuel : nat) (f : nat -> nat * nat) (seed : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    let '(x, next_seed) := f seed in
    x :: unfold_fuel fuel' f next_seed
  end.

Definition unfold (n : nat) (f : nat -> nat * nat) (seed : nat) : list nat :=
  unfold_fuel n f seed.

End LoopifyFolds.

Set Crane Loopify.
Crane Extraction "loopify_folds" LoopifyFolds.
