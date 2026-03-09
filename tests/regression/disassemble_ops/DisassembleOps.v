(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined test: disassemble operations for instruction decoding. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module DisassembleOps.

(* === Common instruction type === *)

Inductive instruction : Type :=
| NOP : instruction
| NOP2 : instruction
| LDM : nat -> instruction
| LDM2 : nat -> instruction.

(* === From disassemble_drop_window === *)

Definition decode1 (b1 b2 : nat) : instruction :=
  if Nat.eqb (b1 mod 2) 0 then NOP2 else LDM2 (b2 mod 16).

Fixpoint drop' (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop' n' l'
      end
  end.

Definition disassemble1 (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop' addr rom with
  | b1 :: b2 :: _ => Some (decode1 b1 b2, addr + 2)
  | _ => None
  end.

Definition test_disassemble_drop_window : nat :=
  match disassemble1 [1; 2; 3; 4; 5] 1 with
  | Some (_, next) => next
  | None => 0
  end.

(* === From disassemble_next_address === *)

Definition decode2 (b1 : nat) (b2 : nat) : instruction :=
  if b1 =? 0 then NOP else LDM (b2 mod 16).

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

Definition disassemble2 (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (decode2 b1 b2, addr + 2)
  | _ => None
  end.

Definition test_disassemble_next_address : nat :=
  match disassemble2 [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

(* === From disassemble_short_rom_none === *)

Definition decode3 (b1 : nat) (b2 : nat) : instruction :=
  if b1 =? 0 then NOP else LDM (b2 mod 16).

Definition disassemble3 (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (decode3 b1 b2, addr + 2)
  | _ => None
  end.

Definition is_none {A : Type} (o : option A) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition test_disassemble_short_rom_none : bool :=
  is_none (disassemble3 [9] 0).

(* === From decode_disassemble === *)

Definition decode4 (b1 : nat) (b2 : nat) : instruction :=
  if b1 =? 0 then NOP else LDM (b2 mod 16).

Definition disassemble4 (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (decode4 b1 b2, addr + 2)
  | _ => None
  end.

Record state : Type := mkState {
  regs : list nat;
  rom : list nat
}.

Definition init_state : state := mkState (repeat 0 16) (repeat 0 4096).

Definition test_decode_disassemble_1 : nat :=
  match disassemble4 [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

Definition test_decode_disassemble_2 : nat :=
  match disassemble4 [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

Definition test_init_state_regs : nat := length (regs init_state).

Definition test_init_state_rom : nat := length (rom init_state).

(* Combined test tuple *)
Definition t : nat * nat * bool * nat * nat * nat * nat :=
  (test_disassemble_drop_window,
   test_disassemble_next_address,
   test_disassemble_short_rom_none,
   test_decode_disassemble_1,
   test_decode_disassemble_2,
   test_init_state_regs,
   test_init_state_rom).

End DisassembleOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "disassemble_ops" DisassembleOps.
