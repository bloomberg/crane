(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: SRC followed by WRR stores ACC at the selected ROM port. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SrcWrrRomPortRoundtrip.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat;
  acc : nat;
  rom_ports : list nat;
  sel_rom : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition execute_src (s : state) (r : nat) : state :=
  mkState (regs s) (acc s) (rom_ports s) (get_reg_pair s r / 16).

Definition execute_wrr (s : state) : state :=
  mkState (regs s) (acc s) (update_nth (sel_rom s) (acc s) (rom_ports s)) (sel_rom s).

Definition sample : state := mkState [0; 0; 2; 11; 0; 0] 13 [1; 2; 7; 4] 0.
Definition after_src : state := execute_src sample 3.
Definition after_wrr : state := execute_wrr after_src.
Definition t : bool := Nat.eqb (nth (sel_rom after_src) (rom_ports after_wrr) 0) 13.

End SrcWrrRomPortRoundtrip.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "src_wrr_rom_port_roundtrip" SrcWrrRomPortRoundtrip.
