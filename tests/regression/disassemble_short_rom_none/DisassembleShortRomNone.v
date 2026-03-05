(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: disassemble returns None on short trailing ROM. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module DisassembleShortRomNone.

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

Definition is_none {A : Type} (o : option A) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition t : bool := is_none (disassemble [9] 0).

End DisassembleShortRomNone.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "disassemble_short_rom_none" DisassembleShortRomNone.
