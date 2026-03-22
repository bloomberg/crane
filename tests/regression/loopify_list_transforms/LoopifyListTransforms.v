From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListTransforms.

(* List transformation and accumulator patterns *)

(* Run-length encoding *)
Fixpoint run_length_encode (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | [x] => [(x, 1)]
  | x :: xs =>
    match run_length_encode xs with
    | [] => [(x, 1)]
    | (y, n) :: rest =>
      if x =? y then (y, n + 1) :: rest
      else (x, 1) :: (y, n) :: rest
    end
  end.

(* Prefix sums with accumulator *)
Fixpoint prefix_sums (acc : nat) (l : list nat) : list nat :=
  match l with
  | [] => [acc]
  | x :: xs => acc :: prefix_sums (acc + x) xs
  end.

(* Sliding pairs - consecutive pairs *)
Fixpoint sliding_pairs_fuel (fuel : nat) (l : list nat) : list (nat * nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | a :: xs =>
      match xs with
      | [] => []
      | b :: _ => (a, b) :: sliding_pairs_fuel fuel' xs
      end
    end
  end.

Definition sliding_pairs (l : list nat) : list (nat * nat) :=
  let len := length l in
  sliding_pairs_fuel len l.

(* Helper: absolute difference *)
Definition abs_diff (x y : nat) : nat :=
  if y <? x then x - y else y - x.

(* Differences between consecutive elements *)
Fixpoint differences_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | x :: xs =>
      match xs with
      | [] => []
      | y :: _ => abs_diff x y :: differences_fuel fuel' xs
      end
    end
  end.

Definition differences (l : list nat) : list nat :=
  let len := length l in
  differences_fuel len l.

(* Helper: take first n elements *)
Fixpoint take (n : nat) (l : list nat) : list nat :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | S n', x :: xs => x :: take n' xs
  end.

(* Helper: drop first n elements *)
Fixpoint drop (n : nat) (l : list nat) : list nat :=
  match n, l with
  | 0, rest => rest
  | _, [] => []
  | S n', _ :: xs => drop n' xs
  end.

(* Split list into chunks of size n *)
Fixpoint chunks_of_fuel (fuel : nat) (n : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    if n <=? 0 then []
    else
      match l with
      | [] => []
      | _ => take n l :: chunks_of_fuel fuel' n (drop n l)
      end
  end.

Definition chunks_of (n : nat) (l : list nat) : list (list nat) :=
  let len := length l in
  chunks_of_fuel len n l.

(* Rotate list left by n positions *)
Fixpoint rotate_left_fuel (fuel : nat) (n : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => l
  | S fuel' =>
    if n <=? 0 then l
    else
      match l with
      | [] => []
      | x :: xs =>
        let rotated := app xs [x] in
        rotate_left_fuel fuel' (n - 1) rotated
      end
  end.

Definition rotate_left (n : nat) (l : list nat) : list nat :=
  let len := length l in
  rotate_left_fuel (n + 1) n l.

(* Remove consecutive duplicates from sorted list *)
Fixpoint uniq_sorted_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | x :: xs =>
      match xs with
      | [] => [x]
      | y :: _ =>
        if x =? y then uniq_sorted_fuel fuel' xs
        else x :: uniq_sorted_fuel fuel' xs
      end
    end
  end.

Definition uniq_sorted (l : list nat) : list nat :=
  let len := length l in
  uniq_sorted_fuel len l.

(* Step sum - conditional transformation before recursion *)
Fixpoint step_sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs =>
    let contribution := if (x mod 2) =? 0 then x else x * 2 in
    contribution + step_sum xs
  end.

End LoopifyListTransforms.

Set Crane Loopify.
Crane Extraction "loopify_list_transforms" LoopifyListTransforms.
