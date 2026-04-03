(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd External.Vector Monads.ITree Monads.IO Monads.STM.
From Crane Require Import Examples.ConcurrentHashTable.

Crane Extract Inlined Constant CHT.max => "std::max<int64_t>(%a0, %a1)".
Crane Extraction "stm_hash_map" CHT.
