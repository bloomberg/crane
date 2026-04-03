(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Mapping.NatIntBDE External.VectorBDE Monads.ITree Monads.IOBDE Monads.STMBDE.
From Crane Require Import Examples.ConcurrentHashTable.

Crane Extract Inlined Constant CHT.max => "bsl::max<int64_t>(%a0, %a1)".

Set Crane BDE Directory "~/bde_install/".
Crane Extraction "stm_hash_map_bde" CHT.
