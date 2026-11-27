From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    A local fixpoint returning [nat -> nat] whose branches return the class method [sz] (a C++ function pointer) and a [crane::fn] (from an [if] whose condition is [mop true true]): the lambda's returns disagree, "return type (a function pointer) must match previous return type crane::fn<...>".  The common-callable-type join misses a class method. *)
Module LocalFixMethodPointerJoin.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_bool : Mon bool := { munit := false; mop := orb }.
Definition st (A : Type) : Type := nat -> A * nat.

Definition t_4 : nat :=
  ((fun w177 : (nat -> nat) => ((fun w178 : nat => w178) (w177 0%nat) + (fun w178 : nat => w178) (w177 3)) mod 10007) (let fix go117 (l118 : (list nat)) (acc119 : (nat -> nat)) {struct l118} : (nat -> nat) := match l118 with [] => (if (mop true true) then (fold_left (fun (acc127 : (nat -> nat)) (e128 : N) => (fun _ : nat => 0%nat)) (@nil N) (fun _ : nat => 0%nat)) else sz) | e120 :: rest121 => sz end in go117 (@nil nat) sz)).
End LocalFixMethodPointerJoin.

Crane Extraction "local_fix_method_pointer_join" LocalFixMethodPointerJoin.
