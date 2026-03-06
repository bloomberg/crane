(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: disjoint RAM address selection predicate as boolean. *)

From Stdlib Require Import Nat Bool.

Module RamAddrDisjointBool.

Definition ram_addr_disjointb
    (b1 c1 r1 i1 b2 c2 r2 i2 : nat) : bool :=
  negb ((b1 =? b2) && (c1 =? c2) && (r1 =? r2) && (i1 =? i2)).

Definition t : nat :=
  (if ram_addr_disjointb 0 1 2 3 0 1 2 3 then 1 else 0) +
  (if ram_addr_disjointb 0 1 2 3 0 1 2 4 then 1 else 0).

End RamAddrDisjointBool.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_addr_disjoint_bool" RamAddrDisjointBool.
