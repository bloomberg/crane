(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged RAM operations tests. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamOps.

(* ===== From ram_main_write_chain ===== *)

Record ram_reg_main : Type := mkRamRegMain {
  reg_main : list nat
}.

Record ram_chip_main : Type := mkRamChipMain {
  chip_regs_main : list ram_reg_main
}.

Record ram_bank_main : Type := mkRamBankMain {
  bank_chips_main : list ram_chip_main
}.

Record state_main : Type := mkStateMain {
  ram_sys_main : list ram_bank_main;
  cur_bank_main : nat;
  sel_chip_main : nat;
  sel_reg_main : nat;
  sel_char_main : nat
}.

Fixpoint update_nth_main {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: xs => y :: update_nth_main n' x xs
  | _, [] => []
  end.

Definition get_bank_main (s : state_main) (b : nat) : ram_bank_main :=
  nth b (ram_sys_main s) (mkRamBankMain []).

Definition get_chip_main (bk : ram_bank_main) (c : nat) : ram_chip_main :=
  nth c (bank_chips_main bk) (mkRamChipMain []).

Definition get_reg_main (ch : ram_chip_main) (r : nat) : ram_reg_main :=
  nth r (chip_regs_main ch) (mkRamRegMain []).

Definition upd_main_in_reg (rg : ram_reg_main) (i : nat) (v : nat) : ram_reg_main :=
  mkRamRegMain (update_nth_main i (v mod 16) (reg_main rg)).

Definition upd_reg_in_chip_main (ch : ram_chip_main) (r : nat) (rg : ram_reg_main) : ram_chip_main :=
  mkRamChipMain (update_nth_main r rg (chip_regs_main ch)).

Definition upd_chip_in_bank_main (bk : ram_bank_main) (c : nat) (ch : ram_chip_main) : ram_bank_main :=
  mkRamBankMain (update_nth_main c ch (bank_chips_main bk)).

Definition upd_bank_in_sys_main (s : state_main) (b : nat) (bk : ram_bank_main) : list ram_bank_main :=
  update_nth_main b bk (ram_sys_main s).

Definition ram_write_main_sys (s : state_main) (v : nat) : list ram_bank_main :=
  let b := cur_bank_main s in
  let c := sel_chip_main s in
  let r := sel_reg_main s in
  let i := sel_char_main s in
  let bk := get_bank_main s b in
  let ch := get_chip_main bk c in
  let rg := get_reg_main ch r in
  let rg' := upd_main_in_reg rg i v in
  let ch' := upd_reg_in_chip_main ch r rg' in
  let bk' := upd_chip_in_bank_main bk c ch' in
  upd_bank_in_sys_main s b bk'.

Definition test_main_write_chain : nat :=
  let rg0 := mkRamRegMain [0; 0; 0] in
  let ch0 := mkRamChipMain [rg0] in
  let bk0 := mkRamBankMain [ch0] in
  let s := mkStateMain [bk0] 0 0 0 1 in
  let sys' := ram_write_main_sys s 19 in
  let bk' := nth 0 sys' (mkRamBankMain []) in
  let ch' := nth 0 (bank_chips_main bk') (mkRamChipMain []) in
  let rg' := nth 0 (chip_regs_main ch') (mkRamRegMain []) in
  nth 1 (reg_main rg') 0.

(* ===== From ram_port_write_chain ===== *)

Record chip_port : Type := mkChipPort {
  chip_port_val : nat
}.

Record bank_port : Type := mkBankPort {
  bank_chips_port : list chip_port
}.

Record state_port : Type := mkStatePort {
  ram_sys_port : list bank_port;
  cur_bank_port : nat;
  sel_chip_port : nat
}.

Fixpoint update_nth_port {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: xs => y :: update_nth_port n' x xs
  | _, [] => []
  end.

Definition get_bank_port (s : state_port) (b : nat) : bank_port :=
  nth b (ram_sys_port s) (mkBankPort []).

Definition get_chip_port (bk : bank_port) (c : nat) : chip_port :=
  nth c (bank_chips_port bk) (mkChipPort 0).

Definition upd_port_in_chip (ch : chip_port) (v : nat) : chip_port :=
  mkChipPort (v mod 16).

Definition upd_chip_in_bank_port (bk : bank_port) (c : nat) (ch : chip_port) : bank_port :=
  mkBankPort (update_nth_port c ch (bank_chips_port bk)).

Definition upd_bank_in_sys_port (s : state_port) (b : nat) (bk : bank_port) : list bank_port :=
  update_nth_port b bk (ram_sys_port s).

Definition ram_write_port_sys (s : state_port) (v : nat) : list bank_port :=
  let b := cur_bank_port s in
  let c := sel_chip_port s in
  let bk := get_bank_port s b in
  let ch := get_chip_port bk c in
  let ch' := upd_port_in_chip ch v in
  let bk' := upd_chip_in_bank_port bk c ch' in
  upd_bank_in_sys_port s b bk'.

Definition test_port_write_chain : nat :=
  let ch0 := mkChipPort 0 in
  let bk0 := mkBankPort [ch0] in
  let s := mkStatePort [bk0] 0 0 in
  let sys' := ram_write_port_sys s 17 in
  let bk' := nth 0 sys' (mkBankPort []) in
  let ch' := nth 0 (bank_chips_port bk') (mkChipPort 0) in
  chip_port_val ch'.

(* ===== From ram_status_write_chain ===== *)

Record ram_reg_status : Type := mkRamRegStatus {
  reg_status : list nat
}.

Record ram_chip_status : Type := mkRamChipStatus {
  chip_regs_status : list ram_reg_status
}.

Record ram_bank_status : Type := mkRamBankStatus {
  bank_chips_status : list ram_chip_status
}.

Record state_status : Type := mkStateStatus {
  ram_sys_status : list ram_bank_status;
  cur_bank_status : nat;
  sel_chip_status : nat;
  sel_reg_status : nat
}.

Fixpoint update_nth_status {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: xs => y :: update_nth_status n' x xs
  | _, [] => []
  end.

Definition get_bank_status (s : state_status) (b : nat) : ram_bank_status :=
  nth b (ram_sys_status s) (mkRamBankStatus []).

Definition get_chip_status (bk : ram_bank_status) (c : nat) : ram_chip_status :=
  nth c (bank_chips_status bk) (mkRamChipStatus []).

Definition get_reg_status (ch : ram_chip_status) (r : nat) : ram_reg_status :=
  nth r (chip_regs_status ch) (mkRamRegStatus []).

Definition upd_status_in_reg (rg : ram_reg_status) (i : nat) (v : nat) : ram_reg_status :=
  mkRamRegStatus (update_nth_status i (v mod 16) (reg_status rg)).

Definition upd_reg_in_chip_status (ch : ram_chip_status) (r : nat) (rg : ram_reg_status) : ram_chip_status :=
  mkRamChipStatus (update_nth_status r rg (chip_regs_status ch)).

Definition upd_chip_in_bank_status (bk : ram_bank_status) (c : nat) (ch : ram_chip_status) : ram_bank_status :=
  mkRamBankStatus (update_nth_status c ch (bank_chips_status bk)).

Definition upd_bank_in_sys_status (s : state_status) (b : nat) (bk : ram_bank_status) : list ram_bank_status :=
  update_nth_status b bk (ram_sys_status s).

Definition ram_write_status_sys (s : state_status) (idx : nat) (v : nat) : list ram_bank_status :=
  let b := cur_bank_status s in
  let c := sel_chip_status s in
  let r := sel_reg_status s in
  let bk := get_bank_status s b in
  let ch := get_chip_status bk c in
  let rg := get_reg_status ch r in
  let rg' := upd_status_in_reg rg idx v in
  let ch' := upd_reg_in_chip_status ch r rg' in
  let bk' := upd_chip_in_bank_status bk c ch' in
  upd_bank_in_sys_status s b bk'.

Definition test_status_write_chain : nat :=
  let rg0 := mkRamRegStatus [0; 0; 0; 0] in
  let ch0 := mkRamChipStatus [rg0] in
  let bk0 := mkRamBankStatus [ch0] in
  let s := mkStateStatus [bk0] 0 0 0 in
  let sys' := ram_write_status_sys s 2 25 in
  let bk' := nth 0 sys' (mkRamBankStatus []) in
  let ch' := nth 0 (bank_chips_status bk') (mkRamChipStatus []) in
  let rg' := nth 0 (chip_regs_status ch') (mkRamRegStatus []) in
  nth 2 (reg_status rg') 0.

(* ===== From ram_read_main_selector ===== *)

Record ram_reg_sel : Type := mkRegSel {
  reg_main_sel : list nat;
  reg_status_sel : list nat
}.

Record ram_chip_sel : Type := mkChipSel {
  chip_regs_sel : list ram_reg_sel;
  chip_port_sel : nat
}.

Record ram_bank_sel : Type := mkBankSel {
  bank_chips_sel : list ram_chip_sel
}.

Record ram_sel : Type := mkSel {
  sel_chip : nat;
  sel_reg : nat;
  sel_char : nat
}.

Record state_sel : Type := mkStateSel {
  ram_sys_sel : list ram_bank_sel;
  cur_bank_sel : nat;
  sel_ram : ram_sel
}.

Definition empty_reg_sel : ram_reg_sel := mkRegSel [] [].
Definition empty_chip_sel : ram_chip_sel := mkChipSel [] 0.
Definition empty_bank_sel : ram_bank_sel := mkBankSel [].

Definition get_bank_sel (s : state_sel) (b : nat) : ram_bank_sel :=
  nth b (ram_sys_sel s) empty_bank_sel.

Definition get_chip_sel (bk : ram_bank_sel) (c : nat) : ram_chip_sel :=
  nth c (bank_chips_sel bk) empty_chip_sel.

Definition get_regRAM (ch : ram_chip_sel) (r : nat) : ram_reg_sel :=
  nth r (chip_regs_sel ch) empty_reg_sel.

Definition get_main_sel (rg : ram_reg_sel) (i : nat) : nat :=
  nth i (reg_main_sel rg) 0.

Definition ram_read_main (s : state_sel) : nat :=
  let bk := get_bank_sel s (cur_bank_sel s) in
  let ch := get_chip_sel bk (sel_chip (sel_ram s)) in
  let rg := get_regRAM ch (sel_reg (sel_ram s)) in
  get_main_sel rg (sel_char (sel_ram s)).

Definition sample_reg_sel : ram_reg_sel := mkRegSel [5; 6; 7; 8] [0; 0; 0; 0].
Definition sample_chip_sel : ram_chip_sel := mkChipSel [sample_reg_sel] 3.
Definition sample_bank_sel : ram_bank_sel := mkBankSel [sample_chip_sel].
Definition sample_sel : ram_sel := mkSel 0 0 2.
Definition sample_state_sel : state_sel := mkStateSel [sample_bank_sel] 0 sample_sel.

Definition test_read_main_selector : nat := ram_read_main sample_state_sel.

(* ===== From ram_read_nested ===== *)

Record ram_reg_nested : Type := mkRegNested {
  reg_main_nested : list nat;
  reg_status_nested : list nat
}.

Record ram_chip_nested : Type := mkChipNested {
  chip_regs_nested : list ram_reg_nested;
  chip_port_nested : nat
}.

Record ram_bank_nested : Type := mkBankNested {
  bank_chips_nested : list ram_chip_nested
}.

Record ram_sel_nested : Type := mkSelNested {
  sel_chip_nested : nat;
  sel_reg_nested : nat;
  sel_char_nested : nat
}.

Record state_nested : Type := mkStateNested {
  ram_sys_nested : list ram_bank_nested;
  cur_bank_nested : nat;
  sel_ram_nested : ram_sel_nested
}.

Definition empty_reg_nested : ram_reg_nested := mkRegNested [] [].
Definition empty_chip_nested : ram_chip_nested := mkChipNested [] 0.
Definition empty_bank_nested : ram_bank_nested := mkBankNested [].

Definition get_bank_nested (s : state_nested) (b : nat) : ram_bank_nested :=
  nth b (ram_sys_nested s) empty_bank_nested.

Definition get_chip_nested (bk : ram_bank_nested) (c : nat) : ram_chip_nested :=
  nth c (bank_chips_nested bk) empty_chip_nested.

Definition get_regRAM_nested (ch : ram_chip_nested) (r : nat) : ram_reg_nested :=
  nth r (chip_regs_nested ch) empty_reg_nested.

Definition get_main_nested (rg : ram_reg_nested) (i : nat) : nat :=
  nth i (reg_main_nested rg) 0.

Definition ram_read_main_nested (s : state_nested) : nat :=
  let bk := get_bank_nested s (cur_bank_nested s) in
  let ch := get_chip_nested bk (sel_chip_nested (sel_ram_nested s)) in
  let rg := get_regRAM_nested ch (sel_reg_nested (sel_ram_nested s)) in
  get_main_nested rg (sel_char_nested (sel_ram_nested s)).

Definition sample_reg_nested : ram_reg_nested := mkRegNested [5; 6; 7; 8] [0; 0; 0; 0].
Definition sample_chip_nested : ram_chip_nested := mkChipNested [sample_reg_nested] 3.
Definition sample_bank_nested : ram_bank_nested := mkBankNested [sample_chip_nested].
Definition sample_sel_nested : ram_sel_nested := mkSelNested 0 0 2.
Definition sample_state_nested : state_nested := mkStateNested [sample_bank_nested] 0 sample_sel_nested.

Definition test_read_nested : nat := ram_read_main_nested sample_state_nested.

(* ===== From ram_write_frame_different_chip ===== *)

Fixpoint update_nth_frame {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth_frame n' x ys
  | _, [] => []
  end.

Definition reg_frame := list nat.
Definition chip_frame := list reg_frame.
Definition bank_frame := list chip_frame.

Definition upd_main_in_reg_frame (rg : reg_frame) (i : nat) (v : nat) : reg_frame :=
  update_nth_frame i v rg.

Definition upd_reg_in_chip_frame (ch : chip_frame) (r : nat) (rg : reg_frame) : chip_frame :=
  update_nth_frame r rg ch.

Definition upd_chip_in_bank_frame (bk : bank_frame) (c : nat) (ch : chip_frame) : bank_frame :=
  update_nth_frame c ch bk.

Definition sample_bank_frame : bank_frame :=
  [
    [[1; 2; 3]; [4; 5; 6]];
    [[7; 8; 9]; [10; 11; 12]]
  ].

Definition updated_bank_frame : bank_frame :=
  let ch := nth 0 sample_bank_frame [] in
  let rg := nth 1 ch [] in
  let rg' := upd_main_in_reg_frame rg 2 99 in
  let ch' := upd_reg_in_chip_frame ch 1 rg' in
  upd_chip_in_bank_frame sample_bank_frame 0 ch'.

Definition test_write_frame_different_chip : bool :=
  Nat.eqb (nth 2 (nth 0 (nth 1 updated_bank_frame []) []) 0) 7.

(* ===== From ram_write_main_preserves_other_bank ===== *)

Fixpoint update_nth_preserve {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth_preserve n' x ys
  | _, [] => []
  end.

Record state_preserve : Type := mkStatePreserve {
  ram_sys_preserve : list nat;
  cur_bank_preserve : nat
}.

Definition ram_write_main_sys_preserve (s : state_preserve) (v : nat) : list nat :=
  update_nth_preserve (cur_bank_preserve s) v (ram_sys_preserve s).

Definition execute_write (s : state_preserve) (v : nat) : state_preserve :=
  mkStatePreserve (ram_write_main_sys_preserve s v) (cur_bank_preserve s).

Definition sample_preserve : state_preserve := mkStatePreserve [10; 20; 30; 40] 1.
Definition test_write_main_preserves_other_bank : bool :=
  Nat.eqb (nth 3 (ram_sys_preserve (execute_write sample_preserve 99)) 0) 40.

(* ===== From ram_addr_disjoint_bool ===== *)

Definition ram_addr_disjointb
    (b1 c1 r1 i1 b2 c2 r2 i2 : nat) : bool :=
  negb ((b1 =? b2) && (c1 =? c2) && (r1 =? r2) && (i1 =? i2)).

Definition test_addr_disjoint_bool : nat :=
  (if ram_addr_disjointb 0 1 2 3 0 1 2 3 then 1 else 0) +
  (if ram_addr_disjointb 0 1 2 3 0 1 2 4 then 1 else 0).

(* ===== From nested_bank_status_write ===== *)

Record reg_nested_bank : Type := MkReg {
  status' : list nat
}.

Record chip_nested_bank : Type := MkChip {
  regs_ : list reg_nested_bank
}.

Record bank_nested_bank : Type := MkBank {
  chips_ : list chip_nested_bank
}.

Record state_nested_bank : Type := MkState {
  banks_ : list bank_nested_bank
}.

Fixpoint update_nth_nested_bank {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth_nested_bank n' x ys
  | _, [] => []
  end.

Definition get_bank0 (s : state_nested_bank) : bank_nested_bank :=
  nth 0 (banks_ s) (MkBank []).

Definition get_chip0 (b : bank_nested_bank) : chip_nested_bank :=
  nth 0 (chips_ b) (MkChip []).

Definition get_reg0 (c : chip_nested_bank) : reg_nested_bank :=
  nth 0 (regs_ c) (MkReg []).

Definition write_status0 (s : state_nested_bank) (v : nat) : state_nested_bank :=
  let b := get_bank0 s in
  let c := get_chip0 b in
  let r := get_reg0 c in
  let r' := MkReg (update_nth_nested_bank 0 v (status' r)) in
  let c' := MkChip (update_nth_nested_bank 0 r' (regs_ c)) in
  let b' := MkBank (update_nth_nested_bank 0 c' (chips_ b)) in
  MkState (update_nth_nested_bank 0 b' (banks_ s)).

Definition read_status0 (s : state_nested_bank) : nat :=
  let b := get_bank0 s in
  let c := get_chip0 b in
  let r := get_reg0 c in
  nth 0 (status' r) 0.

Definition sample_nested_bank : state_nested_bank :=
  MkState [MkBank [MkChip [MkReg [3; 4]]]].

Definition test_nested_bank_status_write : nat :=
  read_status0 (write_status0 sample_nested_bank 7).

(* ===== From ram_accessor_namespace ===== *)

Inductive item : Type := S' | S_.

Definition score (x : item) : nat :=
  match x with
  | S' => 1
  | S_ => 2
  end.

Definition test_accessor_namespace : nat := score S' + score S_.

(* ===== Combined test value ===== *)

Definition t : (nat * nat * nat * nat * nat * nat * bool * bool * nat * nat) :=
  (test_main_write_chain,
   test_port_write_chain,
   test_status_write_chain,
   test_read_main_selector,
   test_read_nested,
   test_addr_disjoint_bool,
   test_write_frame_different_chip,
   test_write_main_preserves_other_bank,
   test_nested_bank_status_write,
   test_accessor_namespace).

End RamOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_ops" RamOps.
