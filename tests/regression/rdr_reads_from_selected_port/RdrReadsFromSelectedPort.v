(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: RDR reads the selected ROM port into ACC. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RdrReadsFromSelectedPort.

Record state : Type := mkState {
  acc : nat;
  rom_ports : list nat;
  sel_rom : nat
}.

Definition execute_rdr (s : state) : state :=
  mkState (nth (sel_rom s) (rom_ports s) 0) (rom_ports s) (sel_rom s).

Definition sample : state := mkState 0 [1; 2; 7; 4] 2.
Definition t : bool := Nat.eqb (acc (execute_rdr sample)) 7.

End RdrReadsFromSelectedPort.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "rdr_reads_from_selected_port" RdrReadsFromSelectedPort.
