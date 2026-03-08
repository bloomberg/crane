(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined JCN condition tests covering all behavioral candidates. *)

From Stdlib Require Import Nat Bool.

Module JcnCondition.

Record state : Type := mkState {
  acc : nat;
  carry : bool;
  test_pin : bool
}.

Definition jcn_condition (s : state) (cond : nat) : bool :=
  let c1 := cond / 8 in
  let c2 := (cond / 4) mod 2 in
  let c3 := (cond / 2) mod 2 in
  let c4 := cond mod 2 in
  let base := orb (andb (acc s =? 0) (c2 =? 1))
                  (orb (andb (carry s) (c3 =? 1))
                       (andb (negb (test_pin s)) (c4 =? 1))) in
  if c1 =? 1 then negb base else base.

(* JCN JNC observes the carry-clear path. *)
Definition check_carry_clear_gate : bool :=
  jcn_condition (mkState 1 false true) 10.

(* JCN JNZ branch condition depends on nonzero accumulator. *)
Definition check_nonzero_gate : bool :=
  jcn_condition (mkState 3 false true) 12.

(* JCN JT observes the inverted high test-pin path. *)
Definition check_test_high : bool :=
  jcn_condition (mkState 1 false true) 9.

(* JCN JNT observes the test pin low path. *)
Definition check_test_low : bool :=
  jcn_condition (mkState 1 false false) 1.

(* JCN JZ branch condition depends on zero accumulator. *)
Definition check_zero_gate : bool :=
  jcn_condition (mkState 0 false true) 4.

Definition t : bool :=
  andb check_carry_clear_gate
    (andb check_nonzero_gate
      (andb check_test_high
        (andb check_test_low check_zero_gate))).

End JcnCondition.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jcn_condition" JcnCondition.
