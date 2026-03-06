(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: arithmetic using conditional PROM data contribution. *)

From Stdlib Require Import Nat Bool.

Module PromFlaggedSum.

Record state : Type := mkState {
  acc : nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition flagged_sum (s : state) : nat :=
  acc s + prom_addr s + (if prom_enable s then prom_data s else 0).

Definition t : nat :=
  flagged_sum (mkState 3 12 77 false).

End PromFlaggedSum.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prom_flagged_sum" PromFlaggedSum.
