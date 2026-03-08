(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined regression test for decode/disassemble functionality. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DecodeDisassemble.

(* Instruction type used by decode/disassemble tests *)
Inductive instruction : Type :=
| NOP : instruction
| LDM : nat -> instruction.

(* Decode two bytes into an instruction *)
Definition decode (b1 : nat) (b2 : nat) : instruction :=
  if b1 =? 0 then NOP else LDM (b2 mod 16).

(* Drop n elements from a list *)
Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

(* Disassemble instruction from ROM at given address *)
Definition disassemble (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (decode b1 b2, addr + 2)
  | _ => None
  end.

(* State record used by init_state tests *)
Record state : Type := mkState {
  regs : list nat;
  rom : list nat
}.

(* Initialize state with 16 registers and 4096-byte ROM *)
Definition init_state : state := mkState (repeat 0 16) (repeat 0 4096).

(* Test case 1: disassemble advances address by two bytes (opcode 0) *)
Definition test_disassemble_opcode_0 : nat :=
  match disassemble [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

(* Test case 2: disassemble advances address by two bytes (alternative) *)
Definition test_disassemble_alternative : nat :=
  match disassemble [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

(* Test case 3: init_state provisions 16 general registers *)
Definition test_init_state_regs : nat := length (regs init_state).

(* Test case 4: init_state provisions 4096-byte ROM image *)
Definition test_init_state_rom : nat := length (rom init_state).

End DecodeDisassemble.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_disassemble" DecodeDisassemble.
