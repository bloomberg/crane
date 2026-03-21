From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyScans.

(* Scan and accumulator-based operations *)

(* Scan left - running accumulation *)
Fixpoint scanl (acc : nat) (l : list nat) : list nat :=
  match l with
  | [] => [acc]
  | x :: xs => acc :: scanl (acc + x) xs
  end.

(* Scan left with multiplication *)
Fixpoint scanl_mult (acc : nat) (l : list nat) : list nat :=
  match l with
  | [] => [acc]
  | x :: xs => acc :: scanl_mult (acc * x) xs
  end.

(* Running maximum *)
Fixpoint running_max (current : nat) (l : list nat) : list nat :=
  match l with
  | [] => [current]
  | x :: xs =>
    let new_max := if current <? x then x else current in
    current :: running_max new_max xs
  end.

(* Running minimum *)
Fixpoint running_min (current : nat) (l : list nat) : list nat :=
  match l with
  | [] => [current]
  | x :: xs =>
    let new_min := if x <? current then x else current in
    current :: running_min new_min xs
  end.

(* Pairwise differences with accumulator *)
Fixpoint pairwise_diff (prev : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    let diff := if x <? prev then
                  let sub := prev - x in
                  if prev <? sub then 0 else sub
                else
                  let sub := x - prev in
                  if x <? sub then 0 else sub in
    diff :: pairwise_diff x xs
  end.

(* Accumulate with condition *)
Fixpoint accumulate_if_even (acc : nat) (l : list nat) : list nat :=
  match l with
  | [] => [acc]
  | x :: xs =>
    if (x mod 2) =? 0 then
      acc :: accumulate_if_even (acc + x) xs
    else
      acc :: accumulate_if_even acc xs
  end.

End LoopifyScans.

Set Crane Loopify.
Crane Extraction "loopify_scans" LoopifyScans.
