(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: init_state provisions 4096-byte ROM image. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DecodeWfOpcode9Edge0079.

Record state : Type := mkState {
  rom : list nat
}.

Definition init_state : state := mkState (repeat 0 4096).

Definition t : nat := length (rom init_state).

End DecodeWfOpcode9Edge0079.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_wf_opcode_9_edge_0079" DecodeWfOpcode9Edge0079.
