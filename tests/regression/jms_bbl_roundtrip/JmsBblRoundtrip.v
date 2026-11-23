(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JMS followed by BBL returns to the instruction after JMS. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module JmsBblRoundtrip.

Record state : Type := mkState {
  pc : nat;
  ret : nat;
  has_ret : bool
}.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.

Definition execute_jms (s : state) (addr : nat) : state :=
  mkState (addr12_of_nat addr) (addr12_of_nat (pc s + 2)) true.

Definition execute_bbl (s : state) : state :=
  if has_ret s
  then mkState (ret s) (ret s) false
  else s.

Definition sample : state := mkState 100 0 false.
Definition t : bool := Nat.eqb (pc (execute_bbl (execute_jms sample 200))) 102.

End JmsBblRoundtrip.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "jms_bbl_roundtrip" JmsBblRoundtrip.
