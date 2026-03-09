(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged PROM operations test suite. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PromOps.

(* Helper: list equality for nats *)
Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

(* Helper: update nth element *)
Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

(* From prom_data_fallback *)
Record state1 : Type := mkState1 {
  prom_data1 : nat;
  prom_enable1 : bool
}.

Definition prom_data_or_zero (s : state1) : nat :=
  if prom_enable1 s then prom_data1 s else 0.

Definition test1 : nat := prom_data_or_zero (mkState1 77 false).

(* From prom_flagged_sum *)
Record state2 : Type := mkState2 {
  acc2 : nat;
  prom_addr2 : nat;
  prom_data2 : nat;
  prom_enable2 : bool
}.

Definition flagged_sum (s : state2) : nat :=
  acc2 s + prom_addr2 s + (if prom_enable2 s then prom_data2 s else 0).

Definition test2 : nat :=
  flagged_sum (mkState2 3 12 77 false).

(* From prom_params_large_state *)
Record state3 : Type := mkState3 {
  acc3 : nat;
  regs3 : list nat;
  carry3 : bool;
  pc3 : nat;
  stack3 : list nat;
  ram_sys3 : list nat;
  cur_bank3 : nat;
  sel_ram3 : nat;
  rom_ports3 : list nat;
  sel_rom3 : nat;
  rom3 : list nat;
  test_pin3 : bool;
  prom_addr3 : nat;
  prom_data3 : nat;
  prom_enable3 : bool
}.

Definition set_prom_params3 (s : state3) (addr : nat) (data : nat) (enable : bool) : state3 :=
  mkState3 (acc3 s) (regs3 s) (carry3 s) (pc3 s) (stack3 s)
          (ram_sys3 s) (cur_bank3 s) (sel_ram3 s)
          (rom_ports3 s) (sel_rom3 s) (rom3 s) (test_pin3 s)
          addr data enable.

Definition test3 : nat :=
  let s := mkState3 1 [2; 3] false 4 [5] [6] 0 0 [7] 0 [8; 9] true 0 0 false in
  let s' := set_prom_params3 s 21 144 true in
  prom_addr3 s' + (if prom_enable3 s' then prom_data3 s' else 0) + length (regs3 s').

(* From prom_params_set (identical to large_state, reusing definitions) *)
Definition test4 : nat :=
  let s := mkState3 1 [2; 3] false 4 [5] [6] 0 0 [7] 0 [8; 9] true 0 0 false in
  let s' := set_prom_params3 s 21 144 true in
  prom_addr3 s' + (if prom_enable3 s' then prom_data3 s' else 0) + length (regs3 s').

(* From prom_params_update *)
Record state5 : Type := mkState5 {
  acc5 : nat;
  regs5 : list nat;
  rom5 : list nat;
  prom_addr5 : nat;
  prom_data5 : nat;
  prom_enable5 : bool
}.

Definition set_prom_params5 (s : state5) (addr : nat) (data : nat) (enable : bool) : state5 :=
  mkState5 (acc5 s) (regs5 s) (rom5 s) addr data enable.

Definition test5 : nat :=
  let s := mkState5 3 [1; 2] [9; 8; 7] 0 0 false in
  let s' := set_prom_params5 s 23 77 true in
  acc5 s' + prom_addr5 s' + (if prom_enable5 s' then prom_data5 s' else 0).

(* From set_prom_enable_true *)
Record state6 : Type := mkState6 {
  rom6 : list nat;
  prom_addr6 : nat;
  prom_data6 : nat;
  prom_enable6 : bool
}.

Definition set_prom_params6 (s : state6) (addr data : nat) (enable : bool) : state6 :=
  mkState6 (rom6 s) addr data enable.

Definition sample6 : state6 := mkState6 [10; 11; 12; 13] 0 0 false.
Definition test6 : bool := Bool.eqb (prom_enable6 (set_prom_params6 sample6 2 99 true)) true.

(* From set_prom_preserves_ram *)
Record state7 : Type := mkState7 {
  regs7 : list nat;
  ram_sys7 : list nat;
  prom_addr7 : nat;
  prom_data7 : nat;
  prom_enable7 : bool
}.

Definition set_prom_params7 (s : state7) (addr data : nat) (enable : bool) : state7 :=
  mkState7 (regs7 s) (ram_sys7 s) addr data enable.

Definition sample7 : state7 := mkState7 [1; 2; 3] [9; 8; 7] 0 0 false.
Definition test7 : bool :=
  nat_list_eqb (ram_sys7 (set_prom_params7 sample7 12 99 true)) (ram_sys7 sample7).

(* From set_prom_preserves_regs *)
Record state8 : Type := mkState8 {
  regs8 : list nat;
  ram_sys8 : list nat;
  prom_addr8 : nat;
  prom_data8 : nat;
  prom_enable8 : bool
}.

Definition set_prom_params8 (s : state8) (addr data : nat) (enable : bool) : state8 :=
  mkState8 (regs8 s) (ram_sys8 s) addr data enable.

Definition sample8 : state8 := mkState8 [1; 2; 3] [9; 8] 0 0 false.
Definition test8 : bool :=
  nat_list_eqb (regs8 (set_prom_params8 sample8 12 99 true)) (regs8 sample8).

(* From set_prom_preserves_rom_length *)
Record state9 : Type := mkState9 {
  rom9 : list nat;
  prom_addr9 : nat;
  prom_data9 : nat;
  prom_enable9 : bool
}.

Definition set_prom_params9 (s : state9) (addr data : nat) (enable : bool) : state9 :=
  mkState9 (rom9 s) addr data enable.

Definition sample9 : state9 := mkState9 [10; 11; 12; 13] 0 0 false.
Definition test9 : bool :=
  Nat.eqb
    (length (rom9 (set_prom_params9 sample9 12 99 true)))
    (length (rom9 sample9)).

(* From set_prom_then_wpm *)
Record state10 : Type := mkState10 {
  regs10 : list nat;
  rom10 : list nat;
  acc10 : nat;
  pc10 : nat;
  stack10 : list nat;
  cur_bank10 : nat;
  rom_ports10 : list nat;
  sel_rom10 : nat;
  prom_addr10 : nat;
  prom_data10 : nat;
  prom_enable10 : bool
}.

Definition set_prom_params10 (s : state10) (addr data : nat) (enable : bool) : state10 :=
  mkState10 (regs10 s) (rom10 s) (acc10 s) (pc10 s) (stack10 s) (cur_bank10 s)
          (rom_ports10 s) (sel_rom10 s) addr data enable.

Definition execute_wpm10 (s : state10) : state10 :=
  let new_rom := if prom_enable10 s
                 then update_nth (prom_addr10 s) (prom_data10 s) (rom10 s)
                 else rom10 s in
  mkState10 (regs10 s) new_rom (acc10 s) (pc10 s) (stack10 s) (cur_bank10 s)
          (rom_ports10 s) (sel_rom10 s) (prom_addr10 s) (prom_data10 s) (prom_enable10 s).

Definition sample10 : state10 :=
  mkState10 [1; 2; 3; 4] [10; 11; 12; 13; 14; 15; 16; 17] 7 1025 [7; 9] 2 [3; 4; 5; 6] 5 0 0 false.

Definition check_pc_bound : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.ltb (pc10 after) 4096.

Definition check_acc_bound : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.ltb (acc10 after) 16.

Definition check_bank_bound : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.ltb (cur_bank10 after) 8.

Definition check_regs_length : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.eqb (length (regs10 after)) 4.

Definition check_rom_ports_length : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.eqb (length (rom_ports10 after)) 4.

Definition check_sel_rom_bound : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.ltb (sel_rom10 after) 16.

Definition check_stack_length : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.leb (length (stack10 after)) 3.

Definition check_prom_addr_bound : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 2048 99 true) in
  Nat.ltb (prom_addr10 after) 4096.

Definition check_prom_data_bound : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 155 true) in
  Nat.ltb (prom_data10 after) 256.

Definition check_rom_length : bool :=
  let after := execute_wpm10 (set_prom_params10 sample10 3 99 true) in
  Nat.eqb (length (rom10 after)) 8.

Definition test10 : bool :=
  check_pc_bound && check_acc_bound && check_bank_bound &&
  check_regs_length && check_rom_ports_length && check_sel_rom_bound &&
  check_stack_length && check_prom_addr_bound && check_prom_data_bound &&
  check_rom_length.

(* From guarded_prom_write *)
Record state11 : Type := mkState11 {
  rom11 : list nat;
  prom_addr11 : nat;
  prom_data11 : nat;
  prom_enable11 : bool
}.

Definition execute_wpm11 (s : state11) : state11 :=
  if prom_enable11 s
  then mkState11 (update_nth (prom_addr11 s) (prom_data11 s) (rom11 s))
               (prom_addr11 s) (prom_data11 s) (prom_enable11 s)
  else s.

Definition sample11 : state11 := mkState11 [0; 0; 0] 1 9 true.
Definition test11 : nat := nth 1 (rom11 (execute_wpm11 sample11)) 0.

(* Combined test value: tuple of all test results *)
Definition t : nat * nat * nat * nat * nat * bool * bool * bool * bool * bool * nat :=
  (test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11).

End PromOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prom_ops" PromOps.
