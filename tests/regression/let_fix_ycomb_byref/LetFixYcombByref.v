(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Non-escaping let-fix uses Y-combinator with [&] capture. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixYcombByref.

(* List processing with accumulator *)
Definition sum_list (l : list nat) : nat :=
  let fix go (xs : list nat) (acc : nat) : nat :=
    match xs with
    | [] => acc
    | x :: rest => go rest (acc + x)
    end
  in go l 0.

(* Multiple list params *)
Definition zip_sum (l1 l2 : list nat) : list nat :=
  let fix go (xs ys : list nat) : list nat :=
    match xs, ys with
    | x :: xs', y :: ys' => (x + y) :: go xs' ys'
    | _, _ => []
    end
  in go l1 l2.

(* Scalar param only — no const-ref needed *)
Definition countdown (n : nat) : list nat :=
  let fix go (k : nat) : list nat :=
    match k with
    | 0 => []
    | S k' => k :: go k'
    end
  in go n.

(* === Test values === *)

Definition test_sum : nat := sum_list [1; 2; 3; 4; 5].
Definition test_zip : list nat := zip_sum [1; 2; 3] [10; 20; 30].
Definition test_countdown : list nat := countdown 3.

End LetFixYcombByref.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_ycomb_byref" LetFixYcombByref.
