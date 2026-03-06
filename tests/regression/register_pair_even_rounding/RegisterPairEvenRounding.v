(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: register-pair access with even-index rounding. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module RegisterPairEvenRounding.

Record state : Type := MkState {
  regs_ : list nat
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs_ s) 0.

Definition set_reg (s : state) (r : nat) (v : nat) : state :=
  MkState (update_nth r (v mod 16) (regs_ s)).

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let r_even := r - (r mod 2) in
  let hi := get_reg s r_even in
  let lo := get_reg s (r_even + 1) in
  (hi * 16) + lo.

Definition set_reg_pair (s : state) (r : nat) (v : nat) : state :=
  let r_even := r - (r mod 2) in
  let hi := v / 16 in
  let lo := v mod 16 in
  let s1 := set_reg s r_even hi in
  set_reg s1 (r_even + 1) lo.

Definition sample : state := MkState [0; 1; 2; 3; 4; 5].
Definition t : nat := get_reg_pair (set_reg_pair sample 3 45) 3.

End RegisterPairEvenRounding.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "register_pair_even_rounding" RegisterPairEvenRounding.
