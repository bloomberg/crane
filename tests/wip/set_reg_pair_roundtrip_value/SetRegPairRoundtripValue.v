(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: set_reg_pair writes a byte that get_reg_pair reads back. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module SetRegPairRoundtripValue.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition update_nth_nat (n x : nat) (l : list nat) : list nat :=
  if n <? length l
  then firstn n l ++ x :: skipn (S n) l
  else l.

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition set_reg_pair (s : state) (r v : nat) : state :=
  let base := r - r mod 2 in
  let hi := v / 16 in
  let lo := v mod 16 in
  mkState (update_nth_nat (base + 1) lo (update_nth_nat base hi (regs s))).

Definition t : nat := get_reg_pair (set_reg_pair (mkState [0; 0; 0; 0]) 2 171) 2.

End SetRegPairRoundtripValue.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_reg_pair_roundtrip_value" SetRegPairRoundtripValue.
