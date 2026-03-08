(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test anonymous/local fixpoints *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module AnonFixpoint.

(* Anonymous fixpoint in a let binding *)
Definition sum_to (n : nat) : nat :=
  let fix go (m : nat) (acc : nat) : nat :=
    match m with
    | O => acc
    | S p => go p (Nat.add m acc)
    end
  in go n 0.

(* Anonymous fixpoint in function body *)
Definition factorial (n : nat) : nat :=
  (fix fact (m : nat) : nat :=
    match m with
    | O => 1
    | S p => Nat.mul m (fact p)
    end) n.

(* Nested anonymous fixpoints *)
Definition double_sum (n : nat) : nat :=
  let fix outer (m : nat) : nat :=
    match m with
    | O => 0
    | S p =>
      let fix inner (k : nat) : nat :=
        match k with
        | O => 0
        | S q => Nat.add 1 (inner q)
        end
      in Nat.add (inner m) (outer p)
    end
  in outer n.

(* Anonymous fixpoint with multiple arguments *)
Definition gcd (a b : nat) : nat :=
  (fix go (fuel : nat) (x y : nat) : nat :=
    match fuel with
    | O => x
    | S f =>
      match y with
      | O => x
      | S _ => go f y (Nat.modulo x y)
      end
    end) (Nat.add a b) a b.

Definition test_shadow (n : nat) : nat :=
   let foo := n + n in
   let bar := (fix foo (n : nat) : nat :=
                 match n with
                 | O => O
                 | S n' => S (foo n')
                 end) in
   bar foo.

(* Test values *)
Definition test_sum_5 := sum_to 5.        (* 5+4+3+2+1 = 15 *)
Definition test_sum_0 := sum_to 0.        (* 0 *)
Definition test_fact_5 := factorial 5.    (* 120 *)
Definition test_fact_0 := factorial 0.    (* 1 *)
Definition test_double := double_sum 3.  (* 1 + (1+1) + (1+1+1) = 6 *)
Definition test_gcd := gcd (Nat.mul 4 3) (Nat.mul 2 3). (* gcd(12,6) = 6 *)

End AnonFixpoint.

Crane Extraction "anon_fixpoint" AnonFixpoint.
