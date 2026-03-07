(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: page decomposition recombines to the original address. *)

From Stdlib Require Import Nat Bool.

Module AddrPageDecomp1027.

Definition recompose (a : nat) : nat := (a / 256) * 256 + a mod 256.

Definition t : bool := Nat.eqb (recompose 1027) 1027.

End AddrPageDecomp1027.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "addr_page_decomp_1027" AddrPageDecomp1027.
