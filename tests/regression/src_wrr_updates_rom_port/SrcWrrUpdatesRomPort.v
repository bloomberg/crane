(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: SRC followed by WRR writes ACC to the ROM port selected by the pair. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SrcWrrUpdatesRomPort.

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
Definition after : state := execute_wrr (execute_src sample 3).
Definition t : bool := Nat.eqb (nth 2 (rom_ports after) 0) 13.

End SrcWrrUpdatesRomPort.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "src_wrr_updates_rom_port" SrcWrrUpdatesRomPort.
