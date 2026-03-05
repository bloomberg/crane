(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: out-of-range bank lookup falls back to empty bank. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module BankLookupDefault.

Record ram_chip : Type := mkChip {
  chip_port : nat
}.

Record ram_bank : Type := mkBank {
  bank_chips : list ram_chip
}.

Record state : Type := mkState {
  ram_sys : list ram_bank
}.

Definition empty_chip : ram_chip := mkChip 0.
Definition empty_bank : ram_bank := mkBank [].

Definition get_bank (s : state) (b : nat) : ram_bank :=
  nth b (ram_sys s) empty_bank.

Definition sample_state : state := mkState [mkBank [empty_chip]].

Definition t : nat := length (bank_chips (get_bank sample_state 7)).

End BankLookupDefault.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "bank_lookup_default" BankLookupDefault.
