From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.Real.
From Stdlib Require Import Reals.
Open Scope R_scope.

(** [Mapping.Real] routes every literal through [crane_real.h]'s [from_z],
    whose non-arithmetic branch calls [z.get_d()] -- a GMP method.  Without a
    GMP mapping for [Z], the argument is Crane's extracted [Z] struct, which
    has no such member, so the header does not compile.  [Real] also declares
    no conversion to a C++ floating type, so the value cannot be read out. *)

Module RealMappingGetD.

  Definition x : R := 3 + 4 * 2.
  Definition y : R := x / 2.

  Definition run : R := y - 1.

End RealMappingGetD.

Crane Extraction "real_mapping_get_d" RealMappingGetD.
