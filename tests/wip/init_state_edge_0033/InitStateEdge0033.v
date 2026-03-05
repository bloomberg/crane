(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: addr12_of_nat wraps into 0..4095 window. *)

From Stdlib Require Import Nat.

Module InitStateEdge0033.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.

Definition t : nat := addr12_of_nat (Nat.pow 2 12 + 5).

End InitStateEdge0033.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "init_state_edge_0033" InitStateEdge0033.
