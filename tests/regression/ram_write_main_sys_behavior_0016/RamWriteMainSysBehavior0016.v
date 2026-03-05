(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: fetch_byte defaults to zero out of ROM range. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module RamWriteMainSysBehavior0016.

Record state : Type := mkState {
  rom : list nat
}.

Definition fetch_byte (s : state) (addr : nat) : nat :=
  nth addr (rom s) 0.

Definition t : nat := fetch_byte (mkState [16; 18]) 5.

End RamWriteMainSysBehavior0016.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_write_main_sys_behavior_0016" RamWriteMainSysBehavior0016.
