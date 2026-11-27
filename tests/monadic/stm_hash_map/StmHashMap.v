(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt External.Vector Monads.ITree Monads.IO Monads.STM.
From Crane Require Import Examples.ConcurrentHashTable.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance max_mapping : OperationMapping (Ref (@CHT.max)) :=
  pure_cpp ["algorithm"] ["x0"; "x1"]
    (Expr "std::max<int64_t>(%arg(x0), %arg(x1))").
Crane Extraction "stm_hash_map" CHT.
