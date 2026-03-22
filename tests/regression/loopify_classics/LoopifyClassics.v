From Stdlib Require Import Nat.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyClassics.

(* Classic recursive numeric functions *)

(* Factorial: n! *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

(* Fibonacci sequence *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

(* Ackermann function - nested recursion *)
Fixpoint ack_fuel (fuel : nat) (m n : nat) : nat :=
  match fuel with
  | 0 => n + 1
  | S fuel' =>
    if m =? 0 then n + 1
    else if n =? 0 then ack_fuel fuel' (m - 1) 1
    else
      let inner := ack_fuel fuel' m (n - 1) in
      ack_fuel fuel' (m - 1) inner
  end.

Definition ack (m n : nat) : nat :=
  ack_fuel (100 * (m + 1) * (n + 1)) m n.

(* Binomial coefficient C(n,k) *)
Fixpoint binomial_fuel (fuel : nat) (n k : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
    if orb (k =? 0) (k =? n) then 1
    else binomial_fuel fuel' (n - 1) (k - 1) + binomial_fuel fuel' (n - 1) k
  end.

Definition binomial (n k : nat) : nat :=
  binomial_fuel (n * k) n k.

(* Pascal's triangle *)
Fixpoint pascal_fuel (fuel : nat) (row col : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
    if orb (col =? 0) (col =? row) then 1
    else pascal_fuel fuel' (row - 1) (col - 1) + pascal_fuel fuel' (row - 1) col
  end.

Definition pascal (row col : nat) : nat :=
  pascal_fuel (row * col) row col.

(* Greatest common divisor *)
Fixpoint gcd_fuel (fuel : nat) (a b : nat) : nat :=
  match fuel with
  | 0 => a
  | S fuel' =>
    if b =? 0 then a
    else gcd_fuel fuel' b (a mod b)
  end.

Definition gcd (a b : nat) : nat :=
  gcd_fuel (a + b) a b.

(* Power function *)
Fixpoint power (base exp : nat) : nat :=
  match exp with
  | 0 => 1
  | S exp' => base * power base exp'
  end.

(* Sum from 1 to n *)
Fixpoint sum_to (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_to n'
  end.

(* Sum of squares from 1 to n *)
Fixpoint sum_squares (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n * n + sum_squares n'
  end.

End LoopifyClassics.

Set Crane Loopify.
Crane Extraction "loopify_classics" LoopifyClassics.
