(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged JCN operation tests: branch target choice, condition evaluation, and constants. *)

From Stdlib Require Import Nat Bool.

Module JcnOps.

(* Shared state definition for all JCN tests *)
Record state : Type := mkState {
  acc : nat;
  carry : bool;
  test_pin : bool;
  pc : nat
}.

(* Shared JCN condition evaluator *)
Definition jcn_condition (s : state) (cond : nat) : bool :=
  let c1 := cond / 8 in
  let c2 := (cond / 4) mod 2 in
  let c3 := (cond / 2) mod 2 in
  let c4 := cond mod 2 in
  let base := orb (andb (acc s =? 0) (c2 =? 1))
                  (orb (andb (carry s) (c3 =? 1))
                       (andb (negb (test_pin s)) (c4 =? 1))) in
  if c1 =? 1 then negb base else base.

(* JCN branch target choice *)
Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).
Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.
Definition base_for_next2 (s : state) : nat := page_base (pc_inc2 s).

Definition branch_target (s : state) (cond off : nat) : nat :=
  if jcn_condition s cond
  then addr12_of_nat (base_for_next2 s + off)
  else addr12_of_nat (pc s + 2).

Definition test_branch_target : nat :=
  branch_target (mkState 0 true false 300) 2 17.

(* JCN condition evaluation tests *)
Definition check_carry_clear_gate : bool :=
  jcn_condition (mkState 1 false true 0) 10.

Definition check_nonzero_gate : bool :=
  jcn_condition (mkState 3 false true 0) 12.

Definition check_test_high : bool :=
  jcn_condition (mkState 1 false true 0) 9.

Definition check_test_low : bool :=
  jcn_condition (mkState 1 false false 0) 1.

Definition check_zero_gate : bool :=
  jcn_condition (mkState 0 false true 0) 4.

Definition test_condition : bool :=
  andb check_carry_clear_gate
    (andb check_nonzero_gate
      (andb check_test_high
        (andb check_test_low check_zero_gate))).

(* JCN constants evaluation *)
Definition JCN_JNT : nat := 1.
Definition JCN_JC : nat := 2.
Definition JCN_JZ : nat := 4.
Definition JCN_JT : nat := 9.
Definition JCN_JNC : nat := 10.
Definition JCN_JNZ : nat := 12.

Definition test_constants : nat :=
  let s := mkState 0 true false 0 in
  (if jcn_condition s JCN_JC then 1 else 0) +
  (if jcn_condition s JCN_JZ then 1 else 0) +
  (if jcn_condition s JCN_JNT then 1 else 0).

(* Combined test result as tuple *)
Definition t : nat * bool * nat :=
  (test_branch_target, test_condition, test_constants).

End JcnOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jcn_ops" JcnOps.
