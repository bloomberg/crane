(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JCN cycle count is 8 when branch is not taken. *)

From Stdlib Require Import Nat Bool.

Module CyclesJcnNotTaken.

Record state : Type := mkState {
  acc : nat;
  carry : bool;
  test_pin : bool
}.

Inductive instruction : Type :=
| JCN : nat -> nat -> instruction
| NOP : instruction.

Definition cycles (s : state) (i : instruction) : nat :=
  match i with
  | NOP => 8
  | JCN cond _ =>
      let c1 := cond / 8 in
      let c2 := (cond / 4) mod 2 in
      let c3 := (cond / 2) mod 2 in
      let c4 := cond mod 2 in
      let base_cond := orb (andb (acc s =? 0) (c2 =? 1))
                           (orb (andb (carry s) (c3 =? 1))
                                (andb (negb (test_pin s)) (c4 =? 1))) in
      let jump := if c1 =? 1 then negb base_cond else base_cond in
      if jump then 16 else 8
  end.

Definition t : nat := cycles (mkState 1 false true) (JCN 4 7).

End CyclesJcnNotTaken.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "cycles_jcn_not_taken" CyclesJcnNotTaken.
