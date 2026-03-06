(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: nested RAM bank/chip/reg status write chain. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module NestedBankStatusWrite.

Record reg : Type := MkReg {
  status' : list nat
}.

Record chip : Type := MkChip {
  regs_ : list reg
}.

Record bank : Type := MkBank {
  chips_ : list chip
}.

Record state : Type := MkState {
  banks_ : list bank
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition get_bank0 (s : state) : bank := nth 0 (banks_ s) (MkBank []).
Definition get_chip0 (b : bank) : chip := nth 0 (chips_ b) (MkChip []).
Definition get_reg0 (c : chip) : reg := nth 0 (regs_ c) (MkReg []).

Definition write_status0 (s : state) (v : nat) : state :=
  let b := get_bank0 s in
  let c := get_chip0 b in
  let r := get_reg0 c in
  let r' := MkReg (update_nth 0 v (status' r)) in
  let c' := MkChip (update_nth 0 r' (regs_ c)) in
  let b' := MkBank (update_nth 0 c' (chips_ b)) in
  MkState (update_nth 0 b' (banks_ s)).

Definition read_status0 (s : state) : nat :=
  let b := get_bank0 s in
  let c := get_chip0 b in
  let r := get_reg0 c in
  nth 0 (status' r) 0.

Definition sample : state := MkState [MkBank [MkChip [MkReg [3; 4]]]].
Definition t : nat := read_status0 (write_status0 sample 7).

End NestedBankStatusWrite.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nested_bank_status_write" NestedBankStatusWrite.
