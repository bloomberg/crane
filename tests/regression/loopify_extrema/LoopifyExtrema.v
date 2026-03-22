From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyExtrema.

(* Extrema and comparison operations *)

(* Maximum element *)
Fixpoint maximum (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let max_rest := maximum xs in
    if max_rest <? x then x else max_rest
  end.

(* Minimum element *)
Fixpoint minimum (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let min_rest := minimum xs in
    if x <? min_rest then x else min_rest
  end.

(* Min and max in single pass *)
Fixpoint minmax (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | [x] => (x, x)
  | x :: xs =>
    let '(lo, hi) := minmax xs in
    (min x lo, max x hi)
  end.

(* Maximum by function *)
Fixpoint max_by (f : nat -> nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => f x
  | x :: xs =>
    let rest_max := max_by f xs in
    let fx := f x in
    if rest_max <? fx then fx else rest_max
  end.

(* Minimum by function *)
Fixpoint min_by (f : nat -> nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => f x
  | x :: xs =>
    let rest_min := min_by f xs in
    let fx := f x in
    if fx <? rest_min then fx else rest_min
  end.

(* Argmax - element that maximizes function *)
Fixpoint argmax (f : nat -> nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let rest_best := argmax f xs in
    let fx := f x in
    let f_rest := f rest_best in
    if f_rest <? fx then x else rest_best
  end.

(* Argmin - element that minimizes function *)
Fixpoint argmin (f : nat -> nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let rest_best := argmin f xs in
    let fx := f x in
    let f_rest := f rest_best in
    if fx <? f_rest then x else rest_best
  end.

(* Compare lists lexicographically *)
Fixpoint lex_compare (l1 l2 : list nat) : nat :=
  match l1, l2 with
  | [], [] => 0  (* equal *)
  | [], _ => 1   (* l1 < l2 *)
  | _, [] => 2   (* l1 > l2 *)
  | x :: xs, y :: ys =>
    if x <? y then 1
    else if y <? x then 2
    else lex_compare xs ys
  end.

(* All elements equal *)
Fixpoint all_equal (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: rest =>
      if x =? y then all_equal xs
      else false
    end
  end.

(* Is list sorted *)
Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: rest =>
      if x <=? y then is_sorted xs
      else false
    end
  end.

(* Compare adjacent elements *)
Fixpoint adjacent_all (p : nat -> nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: rest =>
      if p x y then adjacent_all p xs
      else false
    end
  end.

End LoopifyExtrema.

Set Crane Loopify.
Crane Extraction "loopify_extrema" LoopifyExtrema.
