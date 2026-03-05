(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: disassemble advances address by two bytes. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DisassembleNextAddress.

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

Definition t : nat :=
  match disassemble [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

End DisassembleNextAddress.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "disassemble_next_address" DisassembleNextAddress.
