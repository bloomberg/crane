(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: opcode/operand decode partitioning. *)

From Stdlib Require Import Nat.

Module OpcodeOperandDecode.

Inductive instruction : Type :=
| NOP_
| WRM_
| WRR_
| RDM_
| DCL_.

Definition decode (b1 b2 : nat) : instruction :=
  let opcode := b1 / 16 in
  let operand := b1 mod 16 in
  match opcode with
  | 14 =>
      match operand with
      | 0 => WRM_
      | 2 => WRR_
      | 9 => RDM_
      | _ => NOP_
      end
  | 15 =>
      match operand with
      | 13 => DCL_
      | _ => NOP_
      end
  | _ => NOP_
  end.

Definition t : nat :=
  match decode 224 0 with
  | WRM_ => 1
  | _ => 0
  end.

End OpcodeOperandDecode.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "opcode_operand_decode" OpcodeOperandDecode.
