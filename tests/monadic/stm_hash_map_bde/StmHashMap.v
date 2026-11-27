(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Mapping.NatIntBDE External.VectorBDE Monads.ITree Monads.IOBDE Monads.STMBDE.
From Crane Require Import Examples.ConcurrentHashTable.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance max_mapping : OperationMapping (Ref (@CHT.max)) :=
  pure_cpp [] ["x0"; "x1"]
    (Expr "bsl::max<int64_t>(%arg(x0), %arg(x1))").

Set Crane BDE Directory "~/bde_install/".
Crane Extraction "stm_hash_map_bde" CHT.
