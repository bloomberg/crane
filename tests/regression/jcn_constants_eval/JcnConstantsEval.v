(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JCN named-condition constants through jcn_condition. *)

From Stdlib Require Import Nat Bool.

Module JcnConstantsEval.

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

Definition JCN_JNT : nat := 1.
Definition JCN_JC : nat := 2.
Definition JCN_JZ : nat := 4.
Definition JCN_JT : nat := 9.
Definition JCN_JNC : nat := 10.
Definition JCN_JNZ : nat := 12.

Definition t : nat :=
  let s := mkState 0 true false in
  (if jcn_condition s JCN_JC then 1 else 0) +
  (if jcn_condition s JCN_JZ then 1 else 0) +
  (if jcn_condition s JCN_JNT then 1 else 0).

End JcnConstantsEval.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jcn_constants_eval" JcnConstantsEval.
