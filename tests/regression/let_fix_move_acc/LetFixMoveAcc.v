(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: let-fix with an owned accumulator param should std::move
   the accumulator on its last use (e.g. into a constructor call).
   Currently the accumulator is passed by value but not explicitly
   moved at the cons call site, relying on copy elision.
   Note: outer functions are polymorphic so the inner fix's type
   variable matches the outer scope, avoiding top-level hoisting. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixMoveAcc.

(* reverse_list: xs is borrowed (destructured only), acc is owned
   (consumed into cons). The last use of acc in go rest (x :: acc)
   should generate std::move(acc) in the cons call. *)
Definition reverse_list {A : Type} (l : list A) : list A :=
  let fix go (xs : list A) (acc : list A) : list A :=
    match xs with
    | [] => acc
    | x :: rest => go rest (x :: acc)
    end
  in go l [].

(* snoc: appends an element at the end by reversing, consing, reversing.
   Exercises the same owned-accumulator pattern. *)
Definition snoc {A : Type} (l : list A) (x : A) : list A :=
  let fix rev (xs : list A) (acc : list A) : list A :=
    match xs with
    | [] => acc
    | y :: rest => rev rest (y :: acc)
    end
  in rev (rev l []) [x].

(* === Test values === *)

Definition test_rev : list nat := reverse_list [1; 2; 3].
Definition test_snoc : list nat := snoc [10; 20] 30.

End LetFixMoveAcc.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_move_acc" LetFixMoveAcc.
