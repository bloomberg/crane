(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: drop and disassemble over byte stream. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DisassembleDropWindow.

Inductive instruction : Type :=
| NOP'
| LDM_ : nat -> instruction.

Definition decode (b1 b2 : nat) : instruction :=
  if Nat.eqb (b1 mod 2) 0 then NOP' else LDM_ (b2 mod 16).

Fixpoint drop' (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop' n' l'
      end
  end.

Definition disassemble (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop' addr rom with
  | b1 :: b2 :: _ => Some (decode b1 b2, addr + 2)
  | _ => None
  end.

Definition t : nat :=
  match disassemble [1; 2; 3; 4; 5] 1 with
  | Some (_, next) => next
  | None => 0
  end.

End DisassembleDropWindow.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "disassemble_drop_window" DisassembleDropWindow.
