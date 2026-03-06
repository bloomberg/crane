(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: address membership check inside layout region. *)

From Stdlib Require Import Nat Bool.

Module RegionMembershipBounds.

Record layout : Type := mkLayout {
  base_addr : nat;
  code_size : nat
}.

Definition addr_in_regionb (addr : nat) (l : layout) : bool :=
  (base_addr l <=? addr) && (addr <? base_addr l + code_size l).

Definition t : nat :=
  let l := mkLayout 100 20 in
  (if addr_in_regionb 110 l then 1 else 0) +
  (if addr_in_regionb 121 l then 1 else 0).

End RegionMembershipBounds.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "region_membership_bounds" RegionMembershipBounds.
