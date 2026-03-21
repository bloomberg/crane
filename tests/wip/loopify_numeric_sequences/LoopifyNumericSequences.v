From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyNumericSequences.

(* Advanced numeric sequences and algorithms *)

(* Collatz sequence length *)
Fixpoint collatz_length_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    if n <=? 1 then 0
    else if n mod 2 =? 0 then 1 + collatz_length_fuel fuel' (n / 2)
    else 1 + collatz_length_fuel fuel' (3 * n + 1)
  end.

Definition collatz_length (n : nat) : nat :=
  collatz_length_fuel (n * 100) n.

(* Collatz sequence as list *)
Fixpoint collatz_sequence_fuel (fuel : nat) (n : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    if n <=? 1 then [1]
    else if n mod 2 =? 0 then n :: collatz_sequence_fuel fuel' (n / 2)
    else n :: collatz_sequence_fuel fuel' (3 * n + 1)
  end.

Definition collatz_sequence (n : nat) : list nat :=
  collatz_sequence_fuel (n * 100) n.

(* Tribonacci - sum of three previous *)
Fixpoint tribonacci_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    if n <=? 0 then 0
    else if n =? 1 then 0
    else if n =? 2 then 1
    else tribonacci_fuel fuel' (n - 1) + tribonacci_fuel fuel' (n - 2) +
         tribonacci_fuel fuel' (n - 3)
  end.

Definition tribonacci (n : nat) : nat :=
  tribonacci_fuel (n * 3) n.

(* Staircase - ways to climb n stairs (1, 2, or 3 steps) *)
Fixpoint staircase_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
    if n <=? 0 then 1
    else if n =? 1 then 1
    else staircase_fuel fuel' (n - 1) + staircase_fuel fuel' (n - 2) +
         staircase_fuel fuel' (n - 3)
  end.

Definition staircase (n : nat) : nat :=
  staircase_fuel (n * 3) n.

(* Church encoding - apply function n times *)
Fixpoint church (n : nat) (f : nat -> nat) (x : nat) : nat :=
  match n with
  | 0 => x
  | S n' => church n' f (f x)
  end.

(* Digit sum *)
Fixpoint digitsum_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    if n <=? 0 then 0
    else (n mod 10) + digitsum_fuel fuel' (n / 10)
  end.

Definition digitsum (n : nat) : nat :=
  digitsum_fuel (n + 1) n.

(* Decimal to binary (as number) *)
Fixpoint dec_to_bin_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    if n <=? 0 then 0
    else (n mod 2) + 10 * dec_to_bin_fuel fuel' (n / 2)
  end.

Definition dec_to_bin (n : nat) : nat :=
  dec_to_bin_fuel (n + 1) n.

(* Alternating sum: a - b + c - d + ... *)
Fixpoint alternate_sum (sign : bool) (acc : nat) (l : list nat) : nat :=
  match l with
  | [] => acc
  | x :: xs =>
    if sign then alternate_sum false (acc + x) xs
    else if x <=? acc then alternate_sum true (acc - x) xs
    else alternate_sum true 0 xs
  end.

(* Perfect number check - sum of divisors *)
Fixpoint sum_divisors_aux (n d : nat) : nat :=
  match d with
  | 0 => 0
  | S d' =>
    if n mod d =? 0 then d + sum_divisors_aux n d'
    else sum_divisors_aux n d'
  end.

Definition sum_divisors (n : nat) : nat :=
  if n <=? 1 then 0
  else sum_divisors_aux n (n - 1).

End LoopifyNumericSequences.

Set Crane Loopify.
Crane Extraction "loopify_numeric_sequences" LoopifyNumericSequences.
