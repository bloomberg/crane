(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: a state with accumulator overflow is not WF. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module BadStateAccOverflowNotWfProp.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record ram_reg : Type := mkReg {
  reg_main : list nat;
  reg_status : list nat
}.

Record ram_chip : Type := mkChip {
  chip_regs : list ram_reg;
  chip_port : nat
}.

Record ram_bank : Type := mkBank {
  bank_chips : list ram_chip
}.

Record ram_sel : Type := mkSel {
  sel_bank : nat;
  sel_chip : nat;
  sel_reg : nat;
  sel_char : nat
}.

Record state : Type := mkState {
  state_regs : list nat;
  state_acc : nat;
  state_carry : bool;
  state_pc : nat;
  state_stack : list nat;
  state_ram : list ram_bank;
  state_sel : ram_sel;
  state_rom : list nat
}.

Definition wf_nibbles (xs : list nat) : Prop :=
  Forall (fun x => x < 16) xs.

Definition WF_reg (rg : ram_reg) : Prop :=
  length (reg_main rg) = 16 /\
  wf_nibbles (reg_main rg) /\
  length (reg_status rg) = 4 /\
  wf_nibbles (reg_status rg).

Definition WF_chip (ch : ram_chip) : Prop :=
  length (chip_regs ch) = 4 /\
  Forall WF_reg (chip_regs ch) /\
  chip_port ch < 16.

Definition WF_bank (bk : ram_bank) : Prop :=
  length (bank_chips bk) = 4 /\
  Forall WF_chip (bank_chips bk).

Definition WF_sel (sr : ram_sel) : Prop :=
  sel_bank sr < 4 /\
  sel_chip sr < 4 /\
  sel_reg sr < 4 /\
  sel_char sr < 16.

Definition WF (s : state) : Prop :=
  length (state_regs s) = 16 /\
  wf_nibbles (state_regs s) /\
  state_acc s < 16 /\
  state_pc s < 4096 /\
  length (state_stack s) <= 3 /\
  Forall (fun a => a < 4096) (state_stack s) /\
  length (state_ram s) = 4 /\
  Forall WF_bank (state_ram s) /\
  WF_sel (state_sel s) /\
  length (state_rom s) = 8 /\
  Forall (fun b => b < 256) (state_rom s).

Definition empty_reg : ram_reg := mkReg (repeat 0 16) (repeat 0 4).
Definition empty_chip : ram_chip := mkChip (repeat empty_reg 4) 0.
Definition empty_bank : ram_bank := mkBank (repeat empty_chip 4).
Definition empty_ram : list ram_bank := repeat empty_bank 4.
Definition default_sel : ram_sel := mkSel 0 0 0 0.

Definition init_state : state :=
  mkState (repeat 0 16) 0 false 0 [] empty_ram default_sel (repeat 0 8).

Definition bad_state_wrong_reg_count : state :=
  mkState (repeat 0 15) 0 false 0 [] empty_ram default_sel (repeat 0 8).

Definition bad_state_acc_overflow : state :=
  mkState (repeat 0 16) 16 false 0 [] empty_ram default_sel (repeat 0 8).

Definition bad_state_pc_overflow : state :=
  mkState (repeat 0 16) 0 false 4096 [] empty_ram default_sel (repeat 0 8).

Definition bad_state_stack_overflow : state :=
  mkState (repeat 0 16) 0 false 0 [0; 1; 2; 3] empty_ram default_sel (repeat 0 8).

Definition reset_state (s : state) : state :=
  mkState (state_regs s) 0 false 0 [] (state_ram s) default_sel (state_rom s).

Definition get_main (rg : ram_reg) (i : nat) : nat :=
  nth i (reg_main rg) 0.

Definition get_stat (rg : ram_reg) (i : nat) : nat :=
  nth i (reg_status rg) 0.

Definition upd_main_in_reg (rg : ram_reg) (i v : nat) : ram_reg :=
  mkReg (update_nth i (v mod 16) (reg_main rg)) (reg_status rg).

Definition upd_stat_in_reg (rg : ram_reg) (i v : nat) : ram_reg :=
  mkReg (reg_main rg) (update_nth i (v mod 16) (reg_status rg)).

Definition get_regRAM (ch : ram_chip) (r : nat) : ram_reg :=
  nth r (chip_regs ch) empty_reg.

Definition upd_reg_in_chip (ch : ram_chip) (r : nat) (rg : ram_reg) : ram_chip :=
  mkChip (update_nth r rg (chip_regs ch)) (chip_port ch).

Definition upd_port_in_chip (ch : ram_chip) (v : nat) : ram_chip :=
  mkChip (chip_regs ch) (v mod 16).

Definition get_chip (bk : ram_bank) (c : nat) : ram_chip :=
  nth c (bank_chips bk) empty_chip.

Definition upd_chip_in_bank (bk : ram_bank) (c : nat) (ch : ram_chip) : ram_bank :=
  mkBank (update_nth c ch (bank_chips bk)).

Definition get_bank_from_sys (sys : list ram_bank) (b : nat) : ram_bank :=
  nth b sys empty_bank.

Definition upd_bank_in_sys (s : state) (b : nat) (bk : ram_bank) : list ram_bank :=
  update_nth b bk (state_ram s).

Definition current_bank (s : state) : ram_bank :=
  get_bank_from_sys (state_ram s) (sel_bank (state_sel s)).

Definition current_chip (s : state) : ram_chip :=
  get_chip (current_bank s) (sel_chip (state_sel s)).

Definition current_reg (s : state) : ram_reg :=
  get_regRAM (current_chip s) (sel_reg (state_sel s)).

Definition ram_read_main (s : state) : nat :=
  get_main (current_reg s) (sel_char (state_sel s)).

Definition ram_write_main_sys (s : state) (v : nat) : list ram_bank :=
  let rg := current_reg s in
  let ch := current_chip s in
  let bk := current_bank s in
  let rg' := upd_main_in_reg rg (sel_char (state_sel s)) v in
  let ch' := upd_reg_in_chip ch (sel_reg (state_sel s)) rg' in
  let bk' := upd_chip_in_bank bk (sel_chip (state_sel s)) ch' in
  upd_bank_in_sys s (sel_bank (state_sel s)) bk'.

Definition ram_write_status_sys (s : state) (idx v : nat) : list ram_bank :=
  let rg := current_reg s in
  let ch := current_chip s in
  let bk := current_bank s in
  let rg' := upd_stat_in_reg rg idx v in
  let ch' := upd_reg_in_chip ch (sel_reg (state_sel s)) rg' in
  let bk' := upd_chip_in_bank bk (sel_chip (state_sel s)) ch' in
  upd_bank_in_sys s (sel_bank (state_sel s)) bk'.

Definition pop_stack (s : state) : option nat * state :=
  match state_stack s with
  | [] => (None, s)
  | x :: xs =>
      (Some x,
       mkState (state_regs s) (state_acc s) (state_carry s) (state_pc s)
               xs (state_ram s) (state_sel s) (state_rom s))
  end.

Definition stack_state : state :=
  mkState (repeat 0 16) 0 false 0 [17; 255; 4095] empty_ram default_sel (repeat 0 8).

Definition cleared_state : state :=
  mkState (repeat 0 16) 7 true 99 [300] empty_ram (mkSel 3 2 1 7) (repeat 0 8).

Definition patched_reg : ram_reg :=
  upd_main_in_reg empty_reg 0 13.

Definition patched_chip : ram_chip :=
  upd_reg_in_chip empty_chip 1 patched_reg.

Definition patched_bank : ram_bank :=
  upd_chip_in_bank empty_bank 2 (upd_port_in_chip empty_chip 9).

Definition patched_system : list ram_bank :=
  upd_bank_in_sys init_state 3 patched_bank.
Definition t : Prop :=
  ~ WF bad_state_acc_overflow.

End BadStateAccOverflowNotWfProp.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "bad_state_acc_overflow_not_wf_prop" BadStateAccOverflowNotWfProp.
