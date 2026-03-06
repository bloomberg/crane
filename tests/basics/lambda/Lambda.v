(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test lambda expressions (anonymous functions) *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module Lambda.

(* Simple lambda *)
Definition simple_lambda : nat -> nat := fun x => x.

(* Lambda with multiple arguments *)
Definition multi_arg : nat -> nat -> nat := fun x y => Nat.add x y.

(* Nested lambdas *)
Definition nested_lambda : nat -> nat -> nat -> nat :=
  fun x => fun y => fun z => Nat.add x (Nat.add y z).

(* Lambda capturing environment *)
Definition make_adder (n : nat) : nat -> nat :=
  fun x => Nat.add n x.

(* Lambda in let *)
Definition with_let : nat :=
  let f := fun x => Nat.mul x two in
  f five.

(* Lambda passed as argument *)
Definition apply_fn (f : nat -> nat) (x : nat) : nat := f x.

Definition use_apply : nat := apply_fn (fun x => Nat.add x one) five.

(* Test values *)
Definition test_simple := simple_lambda five.
Definition test_multi := multi_arg three four.
Definition test_nested := nested_lambda one two three.
Definition test_adder := make_adder three five.
Definition test_let := with_let.
Definition test_apply := use_apply.

End Lambda.

Crane Extraction "lambda" Lambda.
