(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: bank selector writes modulo-NBANKS value. *)

From Stdlib Require Import Nat.

Module SetCurBankModulo.

Definition NBANKS : nat := 4.

Record state : Type := mkState {
  cur_bank : nat;
  acc : nat
}.

Definition set_cur_bank (s : state) (b : nat) : state :=
  mkState (b mod NBANKS) (acc s).

Definition t : nat :=
  cur_bank (set_cur_bank (mkState 0 9) 7).

End SetCurBankModulo.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_cur_bank_modulo" SetCurBankModulo.
