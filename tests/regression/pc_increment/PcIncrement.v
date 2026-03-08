(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined regression tests for PC increment behaviors. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module PcIncrement.

(* Shared state record *)
Record state : Type := mkState {
  pc : nat
}.

(* Shared address normalization *)
Definition addr12_of_nat (n : nat) : nat := n mod 4096.

(* pc_inc1: increment by 1 with addr12 normalization *)
Definition pc_inc1 (s : state) : nat := addr12_of_nat (pc s + 1).

(* pc_inc2: increment by 2 with addr12 normalization *)
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).

(* Maximum 12-bit address *)
Definition max_addr : nat := Nat.pow 2 12 - 1.

(* Instruction set for disassemble test *)
Inductive instruction : Type :=
| NOP : instruction
| LDM : nat -> instruction.

Definition decode (b1 : nat) (b2 : nat) : instruction :=
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

Definition disassemble (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (decode b1 b2, addr + 2)
  | _ => None
  end.

(* Test case 1: pc_inc1 wraps modulo at max_addr *)
Definition test_inc1_wrap : nat := pc_inc1 (mkState max_addr).

(* Test case 2: pc_inc2 wraps modulo at max_addr *)
Definition test_inc2_wrap : nat := pc_inc2 (mkState max_addr).

(* Test case 3: disassemble advances address by two bytes *)
Definition test_disassemble_edge : nat :=
  match disassemble [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

(* Combined result tuple *)
Definition t : (nat * nat * nat) :=
  (test_inc1_wrap, test_inc2_wrap, test_disassemble_edge).

End PcIncrement.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "pc_increment" PcIncrement.
