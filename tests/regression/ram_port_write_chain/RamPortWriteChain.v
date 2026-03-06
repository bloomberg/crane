(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: nested RAM bank/chip port write update chain. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module RamPortWriteChain.

Record chip : Type := mkChip {
  chip_port : nat
}.

Record bank : Type := mkBank {
  bank_chips : list chip
}.

Record state : Type := mkState {
  ram_sys : list bank;
  cur_bank : nat;
  sel_chip : nat
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: xs => y :: update_nth n' x xs
  | _, [] => []
  end.

Definition get_bank (s : state) (b : nat) : bank :=
  nth b (ram_sys s) (mkBank []).

Definition get_chip (bk : bank) (c : nat) : chip :=
  nth c (bank_chips bk) (mkChip 0).

Definition upd_port_in_chip (ch : chip) (v : nat) : chip :=
  mkChip (v mod 16).

Definition upd_chip_in_bank (bk : bank) (c : nat) (ch : chip) : bank :=
  mkBank (update_nth c ch (bank_chips bk)).

Definition upd_bank_in_sys (s : state) (b : nat) (bk : bank) : list bank :=
  update_nth b bk (ram_sys s).

Definition ram_write_port_sys (s : state) (v : nat) : list bank :=
  let b := cur_bank s in
  let c := sel_chip s in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let ch' := upd_port_in_chip ch v in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

Definition t : nat :=
  let ch0 := mkChip 0 in
  let bk0 := mkBank [ch0] in
  let s := mkState [bk0] 0 0 in
  let sys' := ram_write_port_sys s 17 in
  let bk' := nth 0 sys' (mkBank []) in
  let ch' := nth 0 (bank_chips bk') (mkChip 0) in
  chip_port ch'.

End RamPortWriteChain.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_port_write_chain" RamPortWriteChain.
