From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifySearchOpt.

(* Search and optimization algorithms *)

(* Longest increasing subsequence (greedy) *)
Fixpoint lis (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    match xs with
    | [] => [x]
    | y :: rest =>
      if x <? y then x :: lis xs
      else lis xs
    end
  end.

(* Longest run of consecutive equal elements *)
Fixpoint longest_run_fuel (fuel : nat) (current best : list nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => best
  | S fuel' =>
    match l with
    | [] =>
      let len_curr := length current in
      let len_best := length best in
      if len_best <? len_curr then current else best
    | x :: xs =>
      match current with
      | [] => longest_run_fuel fuel' [x] best xs
      | y :: _ =>
        if x =? y then
          longest_run_fuel fuel' (x :: current) best xs
        else
          let len_curr := length current in
          let len_best := length best in
          let new_best := if len_best <? len_curr then current else best in
          longest_run_fuel fuel' [x] new_best xs
      end
    end
  end.

Definition longest_run (l : list nat) : list nat :=
  longest_run_fuel (length l) [] [] l.

(* Knapsack 0/1 problem *)
Fixpoint knapsack_fuel (fuel : nat) (capacity : nat) (items : list (nat * nat)) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match items with
    | [] => 0
    | (weight, value) :: rest =>
      if capacity <? weight then knapsack_fuel fuel' capacity rest
      else max (knapsack_fuel fuel' capacity rest)
               (value + knapsack_fuel fuel' (capacity - weight) rest)
    end
  end.

Definition knapsack (capacity : nat) (items : list (nat * nat)) : nat :=
  knapsack_fuel (length items * capacity) capacity items.

(* Subset sum - check if any subset sums to target *)
Fixpoint subset_sum_fuel (fuel : nat) (target : nat) (l : list nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    match l with
    | [] => target =? 0
    | x :: xs =>
      if target <? x then subset_sum_fuel fuel' target xs
      else subset_sum_fuel fuel' target xs ||
           subset_sum_fuel fuel' (target - x) xs
    end
  end.

Definition subset_sum (target : nat) (l : list nat) : bool :=
  subset_sum_fuel (length l * target) target l.

(* Majority element (Boyer-Moore) *)
Fixpoint majority (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | x :: xs =>
    let '(cand, count) := majority xs in
    if x =? cand then (cand, count + 1)
    else if 0 <? count then (cand, count - 1)
    else (x, 1)
  end.

(* Binary search (assumes sorted list) *)
Fixpoint binary_search_fuel (fuel : nat) (target : nat) (l : list nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    match l with
    | [] => false
    | _ =>
      let len := length l in
      if len <=? 1 then
        match l with
        | [x] => x =? target
        | _ => false
        end
      else
        let mid := len / 2 in
        let mid_val := (fix nth n xs :=
          match n, xs with
          | 0, y :: _ => y
          | S n', _ :: ys => nth n' ys
          | _, [] => 0
          end) mid l in
        let left := (fix take n xs :=
          match n, xs with
          | 0, _ => []
          | S n', y :: ys => y :: take n' ys
          | _, [] => []
          end) mid l in
        let right := (fix drop n xs :=
          match n, xs with
          | 0, ys => ys
          | S n', _ :: ys => drop n' ys
          | _, [] => []
          end) (mid + 1) l in
        if target <? mid_val then binary_search_fuel fuel' target left
        else if mid_val <? target then binary_search_fuel fuel' target right
        else true
    end
  end.

Definition binary_search (target : nat) (l : list nat) : bool :=
  binary_search_fuel (length l) target l.

End LoopifySearchOpt.

Set Crane Loopify.
Crane Extraction "loopify_search_opt" LoopifySearchOpt.
