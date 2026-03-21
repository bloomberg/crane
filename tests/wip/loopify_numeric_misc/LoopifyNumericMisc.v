From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyNumericMisc.

(* Miscellaneous numeric operations *)

(* Sum of absolute values *)
Fixpoint sum_abs (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_abs xs
  end.

(* Alternating operations - add if even, double and add if odd *)
Fixpoint alternating_ops (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    if (S n') mod 2 =? 0 then
      S n' + alternating_ops n'
    else
      (S n') * 2 + alternating_ops n'
  end.

(* Count even numbers *)
Fixpoint count_even (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if x mod 2 =? 0 then 1 + count_even xs else count_even xs
  end.

(* Count odd numbers *)
Fixpoint count_odd (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if x mod 2 =? 1 then 1 + count_odd xs else count_odd xs
  end.

(* Product of list *)
Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | x :: xs => x * product xs
  end.

(* Sum of squares *)
Fixpoint sum_of_squares (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x * x + sum_of_squares xs
  end.

(* Max of two numbers *)
Definition max_two (a b : nat) : nat :=
  if a <? b then b else a.

(* Maximum in list *)
Fixpoint list_max (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => max_two x (list_max xs)
  end.

(* Minimum in list *)
Fixpoint list_min (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs =>
    let min_rest := list_min xs in
    if x <? min_rest then x else min_rest
  end.

End LoopifyNumericMisc.

Set Crane Loopify.
Crane Extraction "loopify_numeric_misc" LoopifyNumericMisc.
