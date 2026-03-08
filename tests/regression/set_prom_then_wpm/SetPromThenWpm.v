(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidates: set_prom then WPM combined tests. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetPromThenWpm.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat;
  rom : list nat;
  acc : nat;
  pc : nat;
  stack : list nat;
  cur_bank : nat;
  rom_ports : list nat;
  sel_rom : nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (regs s) (rom s) (acc s) (pc s) (stack s) (cur_bank s)
          (rom_ports s) (sel_rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (regs s) new_rom (acc s) (pc s) (stack s) (cur_bank s)
          (rom_ports s) (sel_rom s) (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state :=
  mkState [1; 2; 3; 4] [10; 11; 12; 13; 14; 15; 16; 17] 7 1025 [7; 9] 2 [3; 4; 5; 6] 5 0 0 false.

(* Individual checks *)
Definition check_pc_bound : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.ltb (pc after) 4096.

Definition check_acc_bound : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.ltb (acc after) 16.

Definition check_bank_bound : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.ltb (cur_bank after) 8.

Definition check_regs_length : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.eqb (length (regs after)) 4.

Definition check_rom_ports_length : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.eqb (length (rom_ports after)) 4.

Definition check_sel_rom_bound : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.ltb (sel_rom after) 16.

Definition check_stack_length : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.leb (length (stack after)) 3.

Definition check_prom_addr_bound : bool :=
  let after := execute_wpm (set_prom_params sample 2048 99 true) in
  Nat.ltb (prom_addr after) 4096.

Definition check_prom_data_bound : bool :=
  let after := execute_wpm (set_prom_params sample 3 155 true) in
  Nat.ltb (prom_data after) 256.

Definition check_rom_length : bool :=
  let after := execute_wpm (set_prom_params sample 3 99 true) in
  Nat.eqb (length (rom after)) 8.

(* Combined test *)
Definition t : bool :=
  check_pc_bound && check_acc_bound && check_bank_bound &&
  check_regs_length && check_rom_ports_length && check_sel_rom_bound &&
  check_stack_length && check_prom_addr_bound && check_prom_data_bound &&
  check_rom_length.

End SetPromThenWpm.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_prom_then_wpm" SetPromThenWpm.
