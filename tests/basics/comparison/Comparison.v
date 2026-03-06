(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test comparison type and operations *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module Comparison.

(* Define our own comparison type for extraction testing *)
Inductive cmp : Type :=
| CmpLt : cmp
| CmpEq : cmp
| CmpGt : cmp.

(* Pattern matching on comparison *)
Definition cmp_to_nat (c : cmp) : nat :=
  match c with
  | CmpLt => zero
  | CmpEq => one
  | CmpGt => two
  end.

(* Custom compare function *)
Definition compare_nats (a b : nat) : cmp :=
  if Nat.ltb a b then CmpLt
  else if Nat.eqb a b then CmpEq
  else CmpGt.

(* Comparison-based operations *)
Definition max_nat (a b : nat) : nat :=
  match compare_nats a b with
  | CmpLt => b
  | _ => a
  end.

Definition min_nat (a b : nat) : nat :=
  match compare_nats a b with
  | CmpGt => b
  | _ => a
  end.

(* Chained comparisons *)
Definition clamp (val lo hi : nat) : nat :=
  match compare_nats val lo with
  | CmpLt => lo
  | _ => match compare_nats val hi with
         | CmpGt => hi
         | _ => val
         end
  end.

(* Reverse comparison *)
Definition flip_cmp (c : cmp) : cmp :=
  match c with
  | CmpLt => CmpGt
  | CmpEq => CmpEq
  | CmpGt => CmpLt
  end.

(* Test values *)
Definition test_lt_nat := cmp_to_nat CmpLt.
Definition test_eq_nat := cmp_to_nat CmpEq.
Definition test_gt_nat := cmp_to_nat CmpGt.
Definition test_compare_lt := compare_nats three five.
Definition test_compare_eq := compare_nats five five.
Definition test_compare_gt := compare_nats seven five.
Definition test_max := max_nat three seven.
Definition test_min := min_nat three seven.
Definition test_clamp_lo := clamp one three seven.
Definition test_clamp_mid := clamp five three seven.
Definition test_clamp_hi := clamp nine three seven.
Definition test_flip := flip_cmp CmpLt.

End Comparison.

Crane Extraction "comparison" Comparison.
