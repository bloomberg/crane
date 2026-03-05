(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: pc_inc2 normalizes through addr12 modulo window. *)

From Stdlib Require Import Nat.

Module PcInc2WrapModulo.

Record state : Type := mkState {
  pc : nat
}.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).

Definition max_addr : nat := Nat.pow 2 12 - 1.

Definition t : nat := pc_inc2 (mkState max_addr).

End PcInc2WrapModulo.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "pc_inc2_wrap_modulo" PcInc2WrapModulo.
