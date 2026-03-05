(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: ISZ loops when increment does not wrap to zero. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module EncodeBehavior0020.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition nibble_of_nat (n : nat) : nat := n mod 16.

Definition isz_loops (s : state) (r : nat) : bool :=
  negb (nibble_of_nat (get_reg s r + 1) =? 0).

Definition t : bool := isz_loops (mkState [15]) 7.

End EncodeBehavior0020.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_behavior_0020" EncodeBehavior0020.
