(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Function vernacular — R_func induction principles. *)

From Stdlib Require Import Arith List Lia.
From Stdlib Require Import Recdef.
Import ListNotations.

Module FunctionVernac.

Function div2 (n : nat) {measure id} : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S p) => S (div2 p)
  end.
Proof.
  intros; unfold id; lia.
Defined.

Function list_sum (l : list nat) {measure length} : nat :=
  match l with
  | [] => 0
  | x :: xs => x + list_sum xs
  end.
Proof.
  intros; simpl; lia.
Defined.

Definition test_div2 : nat := div2 10.
Definition test_sum : nat := list_sum [1; 2; 3; 4; 5].

End FunctionVernac.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "function_vernac" FunctionVernac.
