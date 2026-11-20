(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: FIM writes an immediate into the selected register pair. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module FimOperatesOnPairs.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition set_reg (s : state) (r v : nat) : state :=
  mkState (update_nth r (v mod 16) (regs s)).

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition set_reg_pair (s : state) (r v : nat) : state :=
  let base := r - r mod 2 in
  let hi := v / 16 in
  let lo := v mod 16 in
  let s1 := set_reg s base hi in
  set_reg s1 (base + 1) lo.

Definition execute_fim (s : state) (r data : nat) : state := set_reg_pair s r data.

Definition sample : state := mkState [0; 0; 0; 0; 0; 0].
Definition t : bool := Nat.eqb (get_reg_pair (execute_fim sample 2 171) 2) 171.

End FimOperatesOnPairs.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "fim_operates_on_pairs" FimOperatesOnPairs.
