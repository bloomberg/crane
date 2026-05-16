(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: let-fix list params that are only structurally consumed
   should be passed by const-ref, not by value.
   Params consumed into constructors must stay by-value for moves. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixByrefListParam.

(* Case 1: xs is only destructured, tail passed to recursion.
   Generated C++ currently: List<unsigned int> xs  (by value -- copies tail)
   Optimal:                 const List<unsigned int>& xs  (zero copies) *)
Definition count_elements (l : list nat) : nat :=
  let fix go (xs : list nat) : nat :=
    match xs with
    | [] => 0
    | _ :: rest => 1 + go rest
    end
  in go l.

(* Case 2: xs is borrowed (destructured), acc is a scalar.
   xs -> const-ref, acc -> by value (scalar, cheap to copy) *)
Definition sum_with_acc (l : list nat) : nat :=
  let fix go (xs : list nat) (acc : nat) : nat :=
    match xs with
    | [] => acc
    | x :: rest => go rest (acc + x)
    end
  in go l 0.

(* === Test values === *)

Definition test_count : nat := count_elements [1; 2; 3; 4; 5].
Definition test_sum : nat := sum_with_acc [10; 20; 30].

End LetFixByrefListParam.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_byref_list_param" LetFixByrefListParam.
