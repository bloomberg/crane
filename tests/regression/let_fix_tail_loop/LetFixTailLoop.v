(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: tail-recursive let-fix should ideally be loopified into a
   while-loop instead of generating recursive lambda calls.
   Currently Crane loopifies top-level Fixpoints but not let-fix. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixTailLoop.

(* Tail-recursive sum via let-fix.
   Currently generates: auto go_impl = [](auto& _self, ...) { ... _self(...) }
   Optimal:  while(true) { ... } with a frame struct, no function-call overhead *)
Definition sum_list (l : list nat) : nat :=
  let fix go (xs : list nat) (acc : nat) : nat :=
    match xs with
    | [] => acc
    | x :: rest => go rest (acc + x)
    end
  in go l 0.

(* Tail-recursive length via let-fix *)
Definition length_list (l : list nat) : nat :=
  let fix go (xs : list nat) (n : nat) : nat :=
    match xs with
    | [] => n
    | _ :: rest => go rest (1 + n)
    end
  in go l 0.

(* === Test values === *)

Definition test_sum : nat := sum_list [1; 2; 3; 4; 5].
Definition test_len : nat := length_list [10; 20; 30; 40].

End LetFixTailLoop.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_tail_loop" LetFixTailLoop.
