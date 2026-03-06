(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: nested RAM status-character write update chain. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module RamStatusWriteChain.

Record ram_reg : Type := mkRamReg {
  reg_status : list nat
}.

Record ram_chip : Type := mkRamChip {
  chip_regs : list ram_reg
}.

Record ram_bank : Type := mkRamBank {
  bank_chips : list ram_chip
}.

Record state : Type := mkState {
  ram_sys : list ram_bank;
  cur_bank : nat;
  sel_chip : nat;
  sel_reg : nat
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: xs => y :: update_nth n' x xs
  | _, [] => []
  end.

Definition get_bank (s : state) (b : nat) : ram_bank :=
  nth b (ram_sys s) (mkRamBank []).

Definition get_chip (bk : ram_bank) (c : nat) : ram_chip :=
  nth c (bank_chips bk) (mkRamChip []).

Definition get_reg (ch : ram_chip) (r : nat) : ram_reg :=
  nth r (chip_regs ch) (mkRamReg []).

Definition upd_status_in_reg (rg : ram_reg) (i : nat) (v : nat) : ram_reg :=
  mkRamReg (update_nth i (v mod 16) (reg_status rg)).

Definition upd_reg_in_chip (ch : ram_chip) (r : nat) (rg : ram_reg) : ram_chip :=
  mkRamChip (update_nth r rg (chip_regs ch)).

Definition upd_chip_in_bank (bk : ram_bank) (c : nat) (ch : ram_chip) : ram_bank :=
  mkRamBank (update_nth c ch (bank_chips bk)).

Definition upd_bank_in_sys (s : state) (b : nat) (bk : ram_bank) : list ram_bank :=
  update_nth b bk (ram_sys s).

Definition ram_write_status_sys (s : state) (idx : nat) (v : nat) : list ram_bank :=
  let b := cur_bank s in
  let c := sel_chip s in
  let r := sel_reg s in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let rg := get_reg ch r in
  let rg' := upd_status_in_reg rg idx v in
  let ch' := upd_reg_in_chip ch r rg' in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

Definition t : nat :=
  let rg0 := mkRamReg [0; 0; 0; 0] in
  let ch0 := mkRamChip [rg0] in
  let bk0 := mkRamBank [ch0] in
  let s := mkState [bk0] 0 0 0 in
  let sys' := ram_write_status_sys s 2 25 in
  let bk' := nth 0 sys' (mkRamBank []) in
  let ch' := nth 0 (bank_chips bk') (mkRamChip []) in
  let rg' := nth 0 (chip_regs ch') (mkRamReg []) in
  nth 2 (reg_status rg') 0.

End RamStatusWriteChain.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_status_write_chain" RamStatusWriteChain.
