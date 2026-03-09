(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged test: WPM operation behaviors *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WpmOps.

(* ===== Shared utilities ===== *)

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

(* ===== From wpm_disabled_is_nop ===== *)

Record state1 : Type := mkState1 {
  rom1 : list nat;
  prom_addr1 : nat;
  prom_data1 : nat;
  prom_enable1 : bool
}.

Definition execute_wpm1 (s : state1) : state1 :=
  let new_rom := if prom_enable1 s
                 then update_nth (prom_addr1 s) (prom_data1 s) (rom1 s)
                 else rom1 s in
  mkState1 new_rom (prom_addr1 s) (prom_data1 s) (prom_enable1 s).

Definition sample1 : state1 := mkState1 [10; 11; 12; 13] 2 99 false.
Definition after1 : state1 := execute_wpm1 sample1.

Definition test_wpm_disabled_is_nop : bool :=
  andb (Nat.eqb (nth 0 (rom1 after1) 0) 10)
    (andb (Nat.eqb (nth 1 (rom1 after1) 0) 11)
      (andb (Nat.eqb (nth 2 (rom1 after1) 0) 12)
            (Nat.eqb (nth 3 (rom1 after1) 0) 13))).

(* ===== From wpm_enabled_preserves_ram ===== *)

Record state2 : Type := mkState2 {
  ram_sys2 : list nat;
  rom2 : list nat;
  prom_addr2 : nat;
  prom_data2 : nat;
  prom_enable2 : bool
}.

Definition execute_wpm2 (s : state2) : state2 :=
  let new_rom := if prom_enable2 s
                 then update_nth (prom_addr2 s) (prom_data2 s) (rom2 s)
                 else rom2 s in
  mkState2 (ram_sys2 s) new_rom (prom_addr2 s) (prom_data2 s) (prom_enable2 s).

Definition sample2 : state2 := mkState2 [5; 6; 7] [10; 11; 12] 1 99 true.

Definition test_wpm_enabled_preserves_ram : bool :=
  nat_list_eqb (ram_sys2 (execute_wpm2 sample2)) (ram_sys2 sample2).

(* ===== From wpm_enabled_preserves_regs ===== *)

Record state3 : Type := mkState3 {
  regs3 : list nat;
  rom3 : list nat;
  prom_addr3 : nat;
  prom_data3 : nat;
  prom_enable3 : bool
}.

Definition execute_wpm3 (s : state3) : state3 :=
  let new_rom := if prom_enable3 s
                 then update_nth (prom_addr3 s) (prom_data3 s) (rom3 s)
                 else rom3 s in
  mkState3 (regs3 s) new_rom (prom_addr3 s) (prom_data3 s) (prom_enable3 s).

Definition sample3 : state3 := mkState3 [1; 2; 3] [10; 11; 12] 1 99 true.

Definition test_wpm_enabled_preserves_regs : bool :=
  nat_list_eqb (regs3 (execute_wpm3 sample3)) (regs3 sample3).

(* ===== From wpm_update_gate ===== *)

Record state4 : Type := mkState4 {
  rom4 : list nat;
  prom_addr4 : nat;
  prom_data4 : nat;
  prom_enable4 : bool
}.

Definition execute_wpm4 (s : state4) : state4 :=
  let new_rom := if prom_enable4 s
                 then update_nth (prom_addr4 s) (prom_data4 s) (rom4 s)
                 else rom4 s in
  mkState4 new_rom (prom_addr4 s) (prom_data4 s) (prom_enable4 s).

Definition test_wpm_update_gate : nat :=
  let s := mkState4 [10; 11; 12] 1 99 true in
  let s' := execute_wpm4 s in
  nth 1 (rom4 s') 0.

(* ===== From wpm_updates_rom_at_addr ===== *)

Record state5 : Type := mkState5 {
  rom5 : list nat;
  prom_addr5 : nat;
  prom_data5 : nat;
  prom_enable5 : bool
}.

Definition execute_wpm5 (s : state5) : state5 :=
  let new_rom := if prom_enable5 s
                 then update_nth (prom_addr5 s) (prom_data5 s) (rom5 s)
                 else rom5 s in
  mkState5 new_rom (prom_addr5 s) (prom_data5 s) (prom_enable5 s).

Definition sample5 : state5 := mkState5 [10; 11; 12; 13] 2 99 true.

Definition test_wpm_updates_rom_at_addr : bool :=
  Nat.eqb (nth 2 (rom5 (execute_wpm5 sample5)) 0) 99.

(* ===== From wpm_writes_exactly_once ===== *)

Record state6 : Type := mkState6 {
  rom6 : list nat;
  prom_addr6 : nat;
  prom_data6 : nat;
  prom_enable6 : bool
}.

Definition execute_wpm6 (s : state6) : state6 :=
  let new_rom := if prom_enable6 s
                 then update_nth (prom_addr6 s) (prom_data6 s) (rom6 s)
                 else rom6 s in
  mkState6 new_rom (prom_addr6 s) (prom_data6 s) (prom_enable6 s).

Definition sample6 : state6 := mkState6 [10; 11; 12; 13] 2 99 true.
Definition after6 : state6 := execute_wpm6 sample6.

Definition test_wpm_writes_exactly_once : bool :=
  andb (Nat.eqb (nth 2 (rom6 after6) 0) 99)
    (andb (Nat.eqb (nth 0 (rom6 after6) 0) 10)
      (andb (Nat.eqb (nth 1 (rom6 after6) 0) 11)
            (Nat.eqb (nth 3 (rom6 after6) 0) 13))).

(* ===== Combined test value ===== *)

Definition t : bool * bool * bool * nat * bool * bool :=
  (test_wpm_disabled_is_nop,
   test_wpm_enabled_preserves_ram,
   test_wpm_enabled_preserves_regs,
   test_wpm_update_gate,
   test_wpm_updates_rom_at_addr,
   test_wpm_writes_exactly_once).

End WpmOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wpm_ops" WpmOps.
