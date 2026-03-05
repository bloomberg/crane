(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: port writes are normalized to nibble width. *)

From Stdlib Require Import Nat.

Module PortWriteNibbleMask.

Record ram_chip : Type := mkChip {
  chip_port : nat
}.

Definition nibble_of_nat (n : nat) : nat := n mod 16.

Definition upd_port_in_chip (ch : ram_chip) (v : nat) : ram_chip :=
  mkChip (nibble_of_nat v).

Definition t : nat := chip_port (upd_port_in_chip (mkChip 0) 31).

End PortWriteNibbleMask.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "port_write_nibble_mask" PortWriteNibbleMask.
