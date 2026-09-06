From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.ZInt Mapping.Real.
From Stdlib Require Import Reals.
Open Scope R_scope.

(** [Mapping.Real] is integer-flavor-agnostic, so a program that uses [IZR]
    imports one as well -- here [ZInt], which makes [from_z]'s argument an
    [int64_t].  What remains is reading the result back out: [Real] wraps a
    [long double] and must offer a conversion to it. *)

Module RealMappingGetD.

  Definition x : R := 3 + 4 * 2.
  Definition y : R := x / 2.

  Definition run : R := y - 1.

End RealMappingGetD.

Crane Extraction "real_mapping_get_d" RealMappingGetD.
