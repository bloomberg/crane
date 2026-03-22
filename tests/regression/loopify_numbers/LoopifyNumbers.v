(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Consolidated UNIQUE numeric algorithms - no basic arithmetic.
    Tests loopification on number theory and recursive sequences. *)
Module LoopifyNumbers.

(* ========== RECURSIVE SEQUENCES ========== *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S m => Nat.mul n (factorial m)
  end.

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => O
  | S O => 1
  | S (S m as n') => Nat.add (fib n') (fib m)
  end.

Fixpoint tribonacci_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match n with
    | O => O
    | S O => O
    | S (S O) => 1
    | S (S (S m)) =>
      Nat.add (tribonacci_fuel f (S (S m)))
        (Nat.add (tribonacci_fuel f (S m)) (tribonacci_fuel f m))
    end
  end.

Definition tribonacci (n : nat) : nat :=
  tribonacci_fuel 100 n.

(* ========== NUMBER THEORY ========== *)

Fixpoint gcd_fuel (fuel : nat) (a b : nat) : nat :=
  match fuel with
  | O => a
  | S f =>
    match b with
    | O => a
    | _ => gcd_fuel f b (Nat.modulo a b)
    end
  end.

Definition gcd (a b : nat) : nat :=
  gcd_fuel (Nat.add a b) a b.

Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => O
  | S n', S k' => Nat.add (binomial n' k') (binomial n' k)
  end.

Fixpoint pascal (row col : nat) : nat :=
  match col with
  | O => 1
  | S c =>
    match row with
    | O => O
    | S r => Nat.add (pascal r c) (pascal r (S c))
    end
  end.

Fixpoint ackermann_fuel (fuel : nat) (m n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match m with
    | O => S n
    | S m' =>
      match n with
      | O => ackermann_fuel f m' 1
      | S n' => ackermann_fuel f m' (ackermann_fuel f m n')
      end
    end
  end.

Definition ack (m n : nat) : nat :=
  ackermann_fuel 1000 m n.

(* ========== COLLATZ & DIGIT OPERATIONS ========== *)

Fixpoint collatz_length_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    if Nat.eqb n 1 then O
    else if Nat.eqb (Nat.modulo n 2) O
    then S (collatz_length_fuel f (Nat.div n 2))
    else S (collatz_length_fuel f (Nat.add (Nat.mul 3 n) 1))
  end.

Definition collatz_length (n : nat) : nat :=
  collatz_length_fuel 1000 n.

Fixpoint digitsum_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match n with
    | O => O
    | _ => Nat.add (Nat.modulo n 10) (digitsum_fuel f (Nat.div n 10))
    end
  end.

Definition digitsum (n : nat) : nat :=
  digitsum_fuel 100 n.

Fixpoint dec_to_bin_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match n with
    | O => O
    | _ =>
      let digit := Nat.modulo n 2 in
      let rest := dec_to_bin_fuel f (Nat.div n 2) in
      Nat.add digit (Nat.mul 10 rest)
    end
  end.

Definition dec_to_bin (n : nat) : nat :=
  dec_to_bin_fuel 100 n.

(* ========== SUMS WITH PATTERNS ========== *)

Fixpoint sum_to (n : nat) : nat :=
  match n with
  | O => O
  | S m => Nat.add n (sum_to m)
  end.

Fixpoint sum_squares (n : nat) : nat :=
  match n with
  | O => O
  | S m => Nat.add (Nat.mul n n) (sum_squares m)
  end.

Fixpoint alternating_sum (sign : bool) (acc : nat) (n : nat) : nat :=
  match n with
  | O => acc
  | S m =>
    let new_acc :=
      if sign then Nat.add acc n else Nat.sub acc n
    in
    alternating_sum (negb sign) new_acc m
  end.

(* ========== STAIRCASE (multi-recursion) ========== *)

Fixpoint staircase_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match n with
    | O => 1
    | S O => 1
    | S (S O) => 2
    | S (S (S m)) =>
      Nat.add (staircase_fuel f (S (S m)))
        (Nat.add (staircase_fuel f (S m)) (staircase_fuel f m))
    end
  end.

Definition staircase (n : nat) : nat :=
  staircase_fuel 100 n.

(* ========== HIGHER-ORDER PATTERNS ========== *)

(** [church n f x] applies function [f] to [x] exactly [n] times.
    Tests recursive higher-order function application. *)
Fixpoint church (n : nat) (f : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S m => church m f (f x)
  end.

(** [iterate_pred n] applies predecessor [n] times, starting from [n].
    Tests church-style iteration with concrete function. *)
Fixpoint iterate_pred (n : nat) : nat :=
  church n (fun x => match x with O => O | S m => m end) n.

(** [nest_apply n f x] nests function application: f(f(...f(x))).
    Similar to church but emphasizes nested call structure. *)
Fixpoint nest_apply (n : nat) (f : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S O => f x
  | S (S m as n') => f (nest_apply n' f x)
  end.

(** [sum_while_positive n] sums numbers from [n] down to 0, but only positive ones.
    Tests conditional accumulation in recursion. *)
Fixpoint sum_while_positive (n : nat) : nat :=
  match n with
  | O => O
  | S m => Nat.add n (sum_while_positive m)
  end.

(** [count_down_by k n] counts down from [n] by steps of [k].
    Tests recursion with non-standard step size. *)
Fixpoint count_down_by_fuel (fuel k n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match n with
    | O => 1
    | _ => if Nat.ltb n k then 1
          else S (count_down_by_fuel f k (Nat.sub n k))
    end
  end.

Definition count_down_by (k n : nat) : nat :=
  count_down_by_fuel 100 k n.

(** [mixed_arith n] combines multiplication and addition in recursion. *)
Fixpoint mixed_arith_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => 1
  | S f =>
    match n with
    | O => 1
    | S O => 1
    | S (S O) => 1
    | S (S (S m as n')) =>
      Nat.add (Nat.mul (mixed_arith_fuel f n') (mixed_arith_fuel f m))
              (mixed_arith_fuel f (if Nat.eqb m O then O else Nat.sub m 1))
    end
  end.

Definition mixed_arith (n : nat) : nat :=
  mixed_arith_fuel 1000 n.

(* ========== MUTUAL RECURSION ========== *)

(** [is_even n] checks if n is even (mutually recursive with is_odd). *)
Fixpoint is_even_fuel (fuel : nat) (n : nat) : bool :=
  match fuel with
  | O => true
  | S f =>
    if Nat.eqb n O then true
    else is_odd_fuel f (Nat.sub n 1)
  end

(** [is_odd n] checks if n is odd (mutually recursive with is_even). *)
with is_odd_fuel (fuel : nat) (n : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if Nat.eqb n O then false
    else is_even_fuel f (Nat.sub n 1)
  end.

Definition is_even (n : nat) : bool :=
  is_even_fuel 1000 n.

Definition is_odd (n : nat) : bool :=
  is_odd_fuel 1000 n.

(* ========== POWER & EXPONENTIATION ========== *)

(** [power b e] computes b^e. *)
Fixpoint power (b e : nat) : nat :=
  match e with
  | O => 1
  | S e' => Nat.mul b (power b e')
  end.

(** [power_mod b e m] computes (b^e) mod m efficiently. *)
Fixpoint power_mod_fuel (fuel : nat) (b e m : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    if Nat.eqb e O then 1
    else if Nat.eqb (Nat.modulo e 2) O
    then
      let half := power_mod_fuel f b (Nat.div e 2) m in
      Nat.modulo (Nat.mul half half) m
    else
      let half := power_mod_fuel f b (Nat.div e 2) m in
      Nat.modulo (Nat.mul b (Nat.mul half half)) m
  end.

Definition power_mod (b e m : nat) : nat :=
  power_mod_fuel 1000 b e m.

(** [sum_divisors n] sums all divisors of n (excluding n itself). *)
Fixpoint sum_divisors_aux (n k : nat) : nat :=
  match k with
  | O => O
  | S O => O
  | S k' =>
    if Nat.eqb (Nat.modulo n k) O
    then Nat.add k (sum_divisors_aux n k')
    else sum_divisors_aux n k'
  end.

Definition sum_divisors (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S _ as n') => sum_divisors_aux n' (Nat.sub n' 1)
  end.

(* ========== ALTERNATING SUM MUTUAL RECURSION ========== *)

(** [sum_odd_indices l] and [sum_even_indices l] are mutually recursive.
    sum_odd_indices adds elements at odd positions (0, 2, 4...).
    sum_even_indices processes even positions (1, 3, 5...) by calling sum_odd_indices. *)
Fixpoint sum_odd_indices_fuel (fuel : nat) (l : list nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match l with
    | nil => O
    | cons x xs => Nat.add x (sum_even_indices_fuel f xs)
    end
  end

with sum_even_indices_fuel (fuel : nat) (l : list nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match l with
    | nil => O
    | cons _ xs => sum_odd_indices_fuel f xs
    end
  end.

Definition sum_odd_indices (l : list nat) : nat :=
  sum_odd_indices_fuel (length l) l.

Definition sum_even_indices (l : list nat) : nat :=
  sum_even_indices_fuel (length l) l.

(** [collatz_list n] generates collatz sequence as a list. *)
Fixpoint collatz_list_fuel (fuel : nat) (n : nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    if Nat.eqb n 1 then cons 1 nil
    else if Nat.eqb (Nat.modulo n 2) O
    then cons n (collatz_list_fuel f (Nat.div n 2))
    else if Nat.eqb (Nat.modulo n 3) O
    then cons n (collatz_list_fuel f (Nat.div n 3))
    else cons n (collatz_list_fuel f (Nat.add (Nat.mul 3 n) 1))
  end.

Definition collatz_list (n : nat) : list nat :=
  collatz_list_fuel 1000 n.

(** [sum_divisible_by k n] sums all numbers from 1 to n divisible by k. *)
Fixpoint sum_divisible_by (k n : nat) : nat :=
  match n with
  | O => O
  | S m =>
    if Nat.eqb (Nat.modulo n k) O
    then Nat.add n (sum_divisible_by k m)
    else sum_divisible_by k m
  end.

End LoopifyNumbers.

Set Crane Loopify.
Crane Extraction "loopify_numbers" LoopifyNumbers.
