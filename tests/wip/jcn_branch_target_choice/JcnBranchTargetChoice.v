(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JCN branch target choice from condition evaluation. *)

From Stdlib Require Import Nat Bool.

Module JcnBranchTargetChoice.

Record state : Type := mkState {
  acc : nat;
  carry : bool;
  test_pin : bool;
  pc : nat
}.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).
Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.
Definition base_for_next2 (s : state) : nat := page_base (pc_inc2 s).

Definition jcn_condition (s : state) (cond : nat) : bool :=
  let c1 := cond / 8 in
  let c2 := (cond / 4) mod 2 in
  let c3 := (cond / 2) mod 2 in
  let c4 := cond mod 2 in
  let base := orb (andb (acc s =? 0) (c2 =? 1))
                  (orb (andb (carry s) (c3 =? 1))
                       (andb (negb (test_pin s)) (c4 =? 1))) in
  if c1 =? 1 then negb base else base.

Definition branch_target (s : state) (cond off : nat) : nat :=
  if jcn_condition s cond
  then addr12_of_nat (base_for_next2 s + off)
  else addr12_of_nat (pc s + 2).

Definition t : nat :=
  branch_target (mkState 0 true false 300) 2 17.

End JcnBranchTargetChoice.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jcn_branch_target_choice" JcnBranchTargetChoice.
