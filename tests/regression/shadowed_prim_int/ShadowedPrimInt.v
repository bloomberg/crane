(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A primitive integer literal is spelled through the mapping of the
    primitive type itself, whatever the short name [int] means where the
    extraction command runs.  Here a user's own [int], declared after
    [PrimInt63] is imported and mapped to a narrower C++ type, shadows the
    primitive one: a literal spelled through it would be cast to [int8_t],
    and [300] would come out as [44]. *)

From Stdlib Require Import PrimInt63.

Module ShadowedPrimInt.

Definition big : PrimInt63.int := 300%int63.
Definition sum : PrimInt63.int := add big 1%int63.

End ShadowedPrimInt.

Axiom int : Type.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extract Inlined Constant int => "int8_t" From "cstdint".
Crane Extraction "shadowed_prim_int" ShadowedPrimInt.
