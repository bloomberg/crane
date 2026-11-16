(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test sigma type precondition extraction *)

From Stdlib Require Import Arith PeanoNat.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(* Make sig transparent: extract to just the witness type *)
Crane Extract Inductive sig => "%t0" [ "%a0" ]
  "%t0 %b0a0 = %scrut; %br0".
Crane Extract Inlined Constant proj1_sig => "%a0".

Module SigmaAssert.

(* safe_pred: predecessor with nonzero precondition *)
Definition safe_pred (n : {x : nat | x <> 0}) : nat :=
  Nat.pred (proj1_sig n).

(* safe_div2: divide by 2, requires n > 0 *)
Definition safe_div2 (n : {x : nat | x > 0}) : nat :=
  Nat.div2 (proj1_sig n).

(* Test values *)
Definition test_pred := safe_pred (exist _ 5 (Nat.neq_sym _ _ (O_S 4))).
Definition test_div2 := safe_div2 (exist _ 4 (Nat.lt_0_succ 3)).

End SigmaAssert.

Crane Extraction "sigma_assert" SigmaAssert.
