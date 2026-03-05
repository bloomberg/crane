(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JCN high bit inverts base condition. *)

From Stdlib Require Import Nat Bool.

Module ExecuteClcWfBehavior0098.

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

Definition t : bool := jcn_condition (mkState 15 false true) 13.

End ExecuteClcWfBehavior0098.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "execute_clc_wf_behavior_0098" ExecuteClcWfBehavior0098.
