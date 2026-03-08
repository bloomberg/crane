(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test implicit arguments *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module ImplicitArgs.

(* Simple implicit type argument *)
Definition id {A : Type} (x : A) : A := x.

(* Multiple implicit arguments *)
Definition fst_of {A B : Type} (x : A) (y : B) : A := x.

(* Implicit argument in the middle *)
Definition apply {A B : Type} (f : A -> B) (x : A) : B := f x.

(* Chained implicits *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C :=
  g (f x).

(* Simple list for testing *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A} _ _.

(* Implicit in inductive pattern match *)
Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ rest => Nat.add 1 (length rest)
  end.

(* Using @ to provide implicit arguments explicitly *)
Definition explicit_id := @id nat 5.
Definition explicit_fst := @fst_of nat bool 3 true.

(* Partial application with implicits *)
Definition add_one := Nat.add 1.
Definition double_nat (n : nat) := Nat.add n n.

(* ===== IMPLICIT TERM ARGUMENTS (not just types) ===== *)

(* Implicit nat argument *)
Definition add_implicit {n : nat} (m : nat) : nat := Nat.add n m.

(* Using implicit nat *)
Definition use_add_implicit := @add_implicit 5 3.

(* Implicit nat with inference from later argument *)
Definition scale {factor : nat} (x : nat) (pf : factor = factor) : nat :=
  Nat.mul factor x.

Definition use_scale := @scale 3 7 eq_refl.

(* Multiple implicit term arguments *)
Definition combine {a b : nat} (x : nat) : nat := Nat.add a (Nat.add b x).

Definition use_combine := @combine 2 3 4.

(* Implicit function argument *)
Definition apply_implicit {f : nat -> nat} (x : nat) : nat := f x.

Definition use_apply_implicit := @apply_implicit (Nat.add 1) 5.

(* Implicit with default-like behavior *)
Definition with_base {base : nat} (offset : nat) : nat := Nat.add base offset.

Definition from_zero := @with_base 0.
Definition from_ten := @with_base 10.

Definition use_from_zero := from_zero 5.
Definition use_from_ten := from_ten 5.

(* Implicit argument that's a list *)
Definition head_or {A : Type} {default : A} (l : mylist A) : A :=
  match l with
  | mynil => default
  | mycons x _ => x
  end.

Definition use_head_empty := @head_or nat 0 mynil.
Definition use_head_nonempty := @head_or nat 0 (mycons 7 mynil).

(* Implicit arguments in recursive function *)
Fixpoint sum_with_init {init : nat} (l : mylist nat) : nat :=
  match l with
  | mynil => init
  | mycons x rest => Nat.add x (@sum_with_init init rest)
  end.

Definition use_sum_init := @sum_with_init 5 (mycons 1 (mycons 2 mynil)).

(* Nested implicit term arguments *)
Definition nested_implicits {a : nat} {b : nat} {c : nat} : nat :=
  Nat.add a (Nat.add b c).

Definition use_nested := @nested_implicits 1 2 3.

(* Implicit bool argument *)
Definition choose_branch {flag : bool} (t f : nat) : nat :=
  if flag then t else f.

Definition use_choose_true := @choose_branch true 7 3.
Definition use_choose_false := @choose_branch false 7 3.

(* Test values *)
Definition test_id := id 5.
Definition test_fst := fst_of 3 7.
Definition test_apply := apply double_nat 5.
Definition test_compose := compose double_nat (Nat.add 1) 3.
Definition test_length := length (mycons 1 (mycons 2 (mycons 3 mynil))).
Definition test_explicit_id := explicit_id.
Definition test_explicit_fst := explicit_fst.

(* Tests for implicit term arguments *)
Definition test_add_implicit := use_add_implicit.
Definition test_scale := use_scale.
Definition test_combine := use_combine.
Definition test_apply_implicit := use_apply_implicit.
Definition test_from_zero := use_from_zero.
Definition test_from_ten := use_from_ten.
Definition test_head_empty := use_head_empty.
Definition test_head_nonempty := use_head_nonempty.
Definition test_sum_init := use_sum_init.
Definition test_nested := use_nested.
Definition test_choose_true := use_choose_true.
Definition test_choose_false := use_choose_false.

End ImplicitArgs.

Crane Extraction "implicit_args" ImplicitArgs.
