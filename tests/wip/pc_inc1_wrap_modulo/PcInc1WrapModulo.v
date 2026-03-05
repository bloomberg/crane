(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: pc_inc1 normalizes through addr12 modulo window. *)

From Stdlib Require Import Nat.

Module PcInc1WrapModulo.

Record state : Type := mkState {
  pc : nat
}.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition pc_inc1 (s : state) : nat := addr12_of_nat (pc s + 1).

Definition max_addr : nat := Nat.pow 2 12 - 1.

Definition t : nat := pc_inc1 (mkState max_addr).

End PcInc1WrapModulo.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "pc_inc1_wrap_modulo" PcInc1WrapModulo.
