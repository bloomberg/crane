From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifySpecialRecursion.

(* Special recursion patterns and corner cases *)

(* Collect sorted - extract values from tree in sorted order *)
Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

(* Process twice - recursive result used twice *)
Fixpoint process_twice_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | x :: xs =>
      let first := process_twice_fuel fuel' xs in
      let second := process_twice_fuel fuel' first in
      x :: second
    end
  end.

Definition process_twice (l : list nat) : list nat :=
  process_twice_fuel (length l * length l) l.

(* Double append - result appended to itself *)
Fixpoint double_append (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | h :: t =>
    let rest := double_append t l2 in
    h :: app rest rest
  end.

(* Remove if sum with next is even *)
Fixpoint remove_if_sum_even (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    let next_val := match xs with [] => 0 | h :: _ => h end in
    if (x + next_val) mod 2 =? 0 then
      remove_if_sum_even xs
    else
      x :: remove_if_sum_even xs
  end.

(* Reverse insert - insert in reverse order *)
Fixpoint reverse_insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: ys =>
    if y <? x then y :: reverse_insert x ys
    else x :: l
  end.

(* Nested apply - apply function n times *)
Fixpoint nest_apply (n : nat) (f : nat -> nat) (x : nat) : nat :=
  match n with
  | 0 => x
  | S n' => f (nest_apply n' f x)
  end.

Fixpoint collect_sorted (t : tree) : list nat :=
  match t with
  | Leaf => []
  | Node l x r => app (collect_sorted l) (x :: collect_sorted r)
  end.

(* Sum at odd indices *)
Fixpoint sum_odd_indices_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | x :: xs =>
    if idx mod 2 =? 1 then
      x + sum_odd_indices_aux xs (idx + 1)
    else
      sum_odd_indices_aux xs (idx + 1)
  end.

Definition sum_odd_indices (l : list nat) : nat :=
  sum_odd_indices_aux l 0.

(* Categorize by range *)
Fixpoint categorize_by (k : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs =>
    if k <? x then 3 + categorize_by k xs
    else if x =? k then 2 + categorize_by k xs
    else 1 + categorize_by k xs
  end.

(* Between - filter elements in range *)
Fixpoint between (lo hi : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    if lo <=? x then
      if x <=? hi then
        x :: between lo hi xs
      else
        between lo hi xs
    else
      between lo hi xs
  end.

(* Merge levels - merge nested list of lists *)
Fixpoint merge_levels (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | l :: rest => app l (merge_levels rest)
  end.

End LoopifySpecialRecursion.

Set Crane Loopify.
Crane Extraction "loopify_special_recursion" LoopifySpecialRecursion.
