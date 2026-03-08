(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test let-in expressions *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module LetIn.

(* Simple let binding *)
Definition simple_let : nat :=
  let x := 5 in x.

(* Nested let bindings *)
Definition nested_let : nat :=
  let x := 3 in
  let y := 4 in
  x.

(* Let with computation *)
Definition let_with_add : nat :=
  let x := 3 in
  let y := 4 in
  Nat.add x y.

(* Shadowing in let *)
Definition shadowed_let : nat :=
  let x := 5 in
  let x := 3 in
  x.

(* Let in function body *)
Definition let_in_fun (n : nat) : nat :=
  let doubled := Nat.add n n in
  doubled.

(* Let binding a function *)
Definition let_fun : nat :=
  let f := fun x => Nat.add x 1 in
  f 5.

(* Let with pattern (destructuring) *)
Inductive pair (A B : Type) : Type :=
| Pair : A -> B -> pair A B.

Arguments Pair {A B} _ _.

Definition let_destruct : nat :=
  let p := Pair 3 4 in
  match p with
  | Pair x y => x
  end.

(* Multiple independent lets *)
Definition multi_let : nat :=
  let a := 1 in
  let b := 2 in
  let c := 3 in
  Nat.add a (Nat.add b c).

(* Test values *)
Definition test_simple := simple_let.
Definition test_nested := nested_let.
Definition test_add := let_with_add.
Definition test_shadow := shadowed_let.
Definition test_fun_call := let_in_fun 3.
Definition test_let_fun := let_fun.
Definition test_destruct := let_destruct.
Definition test_multi := multi_let.

End LetIn.

Crane Extraction "let_in" LetIn.
