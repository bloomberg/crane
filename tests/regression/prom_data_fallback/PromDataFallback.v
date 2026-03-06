(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: PROM data fallback to zero when write-enable is false. *)

From Stdlib Require Import Nat Bool.

Module PromDataFallback.

Record state : Type := mkState {
  prom_data : nat;
  prom_enable : bool
}.

Definition prom_data_or_zero (s : state) : nat :=
  if prom_enable s then prom_data s else 0.

Definition t : nat := prom_data_or_zero (mkState 77 false).

End PromDataFallback.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prom_data_fallback" PromDataFallback.
